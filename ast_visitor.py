from pycparser import c_ast
import statements
import z3


class AstVisitor(c_ast.NodeVisitor):
    def __init__(self, return_line):
        self.__line_number = 0
        self.__stmts_bindings = {}
        self.__constructs_info = {}
        self.__function_pointers = []
        self.__function_variables = {}
        self.__then_successors = {}
        self.__return_line = return_line

    def visit_FuncDef(self, node):
        if node.decl.type.args is not None:
            for decl in node.decl.type.args.params:
                if isinstance(decl.type, c_ast.PtrDecl):
                    self.__function_pointers.append(decl.name)
                elif isinstance(decl.type, c_ast.TypeDecl):
                    node_type = decl.type.type.names[0]
                    if node_type == 'int':
                        self.__function_variables[decl.name] = z3.IntSort()
                    if node_type == 'double':
                        self.__function_variables[decl.name] = z3.RealSort()
                    if node_type == 'bool':
                        self.__function_variables[decl.name] = z3.BoolSort()

        self.generic_visit(node.body)

    def generic_visit(self, node):
        if isinstance(node, c_ast.Compound):
            for stmt in node.block_items:
                if isinstance(stmt, c_ast.Decl):
                    if isinstance(stmt.type, c_ast.PtrDecl):
                        self.__function_pointers.append(stmt.name)
                    else:
                        node_type = stmt.type.type.names[0]
                        if node_type == 'int':
                            self.__function_variables[stmt.name] = z3.IntSort()
                        if node_type == 'double':
                            self.__function_variables[stmt.name] = z3.RealSort()
                        if node_type == 'bool':
                            self.__function_variables[stmt.name] = z3.BoolSort()
                elif isinstance(stmt, c_ast.EmptyStatement):
                    pass
                else:
                    if isinstance(stmt, c_ast.Return):
                        if stmt.coord.line != self.__return_line:
                            self.__stmts_bindings[self.__line_number] = stmt
                            self.__constructs_info[self.__line_number] = statements.Skip()
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
        elif isinstance(node, c_ast.EmptyStatement):
            pass
        else:
            super().generic_visit(node)

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
