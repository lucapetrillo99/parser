import constants
from pycparser import c_ast


class AstVisitor(c_ast.NodeVisitor):
    def __init__(self, return_line):
        self.__in_function = False
        self.variables_info = {}  # TODO private
        self.pointers_info = []  # TODO private
        self.stmts_bindings = {}  # TODO private
        self.line_number = 0  # TODO private
        self.constructs_info = {}
        self.function_pointers = {}
        self.function_variables = {}
        self.then_successors = {} # Dictionary that contains the last line number of the if's then and the last line number of the if's else,
                          # it is used to handle successors of if statements in case of if-then-else
        self.return_line = return_line

    def visit_Decl(self, node):
        if not self.__in_function:
            if isinstance(node.type, c_ast.PtrDecl):
                self.pointers_info.append(node.name)
            elif isinstance(node.type, c_ast.TypeDecl):
                node_type = node.type.type.names[0]
                if node_type == 'int':
                    self.variables_info[node.name] = constants.INT
                if node_type == 'double':
                    self.variables_info[node.name] = constants.REAL
                if node_type == 'bool':
                    self.variables_info[node.name] = constants.BOOL
            elif isinstance(node.type, c_ast.Struct):
                declarations = node.type.decls
                for decl in declarations:
                    if isinstance(decl.type, c_ast.PtrDecl):
                        self.pointers_info.append(decl.name)
                    elif isinstance(decl.type, c_ast.TypeDecl):
                        node_type = decl.type.type.names[0]
                        if node_type == 'int':
                            self.variables_info[decl.name] = constants.INT
                        if node_type == 'double':
                            self.variables_info[decl.name] = constants.REAL
                        if node_type == 'bool':
                            self.variables_info[decl.name] = constants.BOOL

    def visit_FuncDef(self, node):
        for decl in node.decl.type.args.params:
            if isinstance(decl.type, c_ast.PtrDecl):
                self.function_pointers[decl.name] = "param"

        self.__in_function = True
        self.generic_visit(node.body)
        self.__in_function = False

    def generic_visit(self, node):
        if isinstance(node, c_ast.Compound):
            for stmt in node.block_items:
                if isinstance(stmt, c_ast.Decl):
                    if isinstance(stmt.type, c_ast.PtrDecl):
                        self.function_pointers[stmt.name] = "function"
                    else:
                        node_type = stmt.type.type.names[0]
                        if node_type == 'int':
                            self.function_variables[stmt.name] = constants.INT
                        if node_type == 'double':
                            self.function_variables[stmt.name] = constants.REAL
                        if node_type == 'bool':
                            self.function_variables[stmt.name] = constants.BOOL
                else:
                    if isinstance(stmt, c_ast.Return):
                        if stmt.coord.line != self.return_line:
                            self.stmts_bindings[self.line_number] = stmt
                            self.constructs_info[self.line_number] = constants.SKIP
                            self.line_number += 1
                        else:
                            self.stmts_bindings[self.line_number] = stmt
                            self.line_number += 1
                    else:
                        self.stmts_bindings[self.line_number] = stmt
                        self.line_number += 1

                self.visit(stmt)

        elif isinstance(node, c_ast.If):
            curr_line_number = self.line_number
            self.constructs_info[curr_line_number - 1] = self.line_number
            self.visit(node.iftrue)
            last_if_true = self.line_number - 1
            if node.iffalse:
                self.constructs_info[curr_line_number - 1] = (self.constructs_info[curr_line_number - 1], self.line_number)
                self.visit(node.iffalse)
                self.then_successors[last_if_true] = self.line_number

        elif isinstance(node, c_ast.While):
            curr_line_number = self.line_number
            self.visit(node.stmt)
            self.constructs_info[curr_line_number - 1] = (curr_line_number, self.line_number)
        elif isinstance(node, c_ast.For):
            curr_line_number = self.line_number
            self.visit(node.stmt)
            self.constructs_info[curr_line_number - 1] = (curr_line_number, self.line_number)
        else:
            super().generic_visit(node)
