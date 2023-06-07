import constants
from pycparser import c_ast


class AstVisitor(c_ast.NodeVisitor):
    def __init__(self, return_line):
        self.__in_function = False
        self.__line_number = 0
        self.__variables_info = {}
        self.__pointers_info = []
        self.__stmts_bindings = {}
        self.__constructs_info = {}
        self.__function_pointers = {}
        self.__function_variables = {}
        self.__then_successors = {}
        self.__return_line = return_line

    def visit_Decl(self, node):
        if not self.__in_function:
            if isinstance(node.type, c_ast.PtrDecl):
                self.__pointers_info.append(node.name)
            elif isinstance(node.type, c_ast.TypeDecl):
                node_type = node.type.type.names[0]
                if node_type == 'int':
                    self.__variables_info[node.name] = constants.INT
                if node_type == 'double':
                    self.__variables_info[node.name] = constants.REAL
                if node_type == 'bool':
                    self.__variables_info[node.name] = constants.BOOL
            elif isinstance(node.type, c_ast.Struct):
                declarations = node.type.decls
                for decl in declarations:
                    if isinstance(decl.type, c_ast.PtrDecl):
                        self.__pointers_info.append(decl.name)
                    elif isinstance(decl.type, c_ast.TypeDecl):
                        node_type = decl.type.type.names[0]
                        if node_type == 'int':
                            self.__variables_info[decl.name] = constants.INT
                        if node_type == 'double':
                            self.__variables_info[decl.name] = constants.REAL
                        if node_type == 'bool':
                            self.__variables_info[decl.name] = constants.BOOL

    def visit_FuncDef(self, node):
        for decl in node.decl.type.args.params:
            if isinstance(decl.type, c_ast.PtrDecl):
                self.__function_pointers[decl.name] = "param"

        self.__in_function = True
        self.generic_visit(node.body)
        self.__in_function = False

    def generic_visit(self, node):
        if isinstance(node, c_ast.Compound):
            for stmt in node.block_items:
                if isinstance(stmt, c_ast.Decl):
                    if isinstance(stmt.type, c_ast.PtrDecl):
                        self.__function_pointers[stmt.name] = "function"
                    else:
                        node_type = stmt.type.type.names[0]
                        if node_type == 'int':
                            self.__function_variables[stmt.name] = constants.INT
                        if node_type == 'double':
                            self.__function_variables[stmt.name] = constants.REAL
                        if node_type == 'bool':
                            self.__function_variables[stmt.name] = constants.BOOL
                else:
                    if isinstance(stmt, c_ast.Return):
                        if stmt.coord.line != self.__return_line:
                            self.__stmts_bindings[self.__line_number] = stmt
                            self.__constructs_info[self.__line_number] = constants.SKIP
                            self.__line_number += 1
                        else:
                            self.__stmts_bindings[self.__line_number] = stmt
                            self.__line_number += 1
                    else:
                        self.__stmts_bindings[self.__line_number] = stmt
                        self.__line_number += 1

                self.visit(stmt)

        elif isinstance(node, c_ast.If):
            curr_line_number = self.__line_number
            self.__constructs_info[curr_line_number - 1] = self.__line_number
            self.visit(node.iftrue)
            last_if_true = self.__line_number - 1
            if node.iffalse:
                self.__constructs_info[curr_line_number - 1] = (
                    self.__constructs_info[curr_line_number - 1], self.__line_number)
                self.visit(node.iffalse)
                self.__then_successors[last_if_true] = self.__line_number

        elif isinstance(node, c_ast.While):
            curr_line_number = self.__line_number
            self.visit(node.stmt)
            self.__constructs_info[curr_line_number - 1] = (curr_line_number, self.__line_number)
        elif isinstance(node, c_ast.For):
            curr_line_number = self.__line_number
            self.visit(node.stmt)
            self.__constructs_info[curr_line_number - 1] = (curr_line_number, self.__line_number)
        else:
            super().generic_visit(node)

    @property
    def variables_info(self):
        return self.__variables_info

    @property
    def pointers_info(self):
        return self.__pointers_info

    @property
    def stmts_bindings(self):
        return self.__stmts_bindings

    @property
    def constructs_info(self):
        return self.__constructs_info

    @property
    def function_pointers(self):
        return self.__function_pointers

    @property
    def function_variables(self):
        return self.__function_variables

    @property
    def then_successors(self):
        return self.__then_successors
