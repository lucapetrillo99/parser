import z3
from pycparser import c_ast


class FunctionVisitor(c_ast.NodeVisitor):
    def __init__(self):
        self.__in_function = False
        self.__variables_info = {}
        self.__pointers_info = []
        self.__return_line = []
        self.__functions = {}

    def visit_Decl(self, node):
        if not self.__in_function:
            if isinstance(node.type, c_ast.PtrDecl):
                self.__pointers_info.append(node.name)
            elif isinstance(node.type, c_ast.TypeDecl):
                node_type = node.type.type.names[0]
                if node_type == 'int':
                    self.__variables_info[node.name] = z3.IntSort()
                if node_type == 'double':
                    self.__variables_info[node.name] = z3.RealSort()
                if node_type == 'bool':
                    self.__variables_info[node.name] = z3.BoolSort()
            elif isinstance(node.type, c_ast.Struct):
                declarations = node.type.decls
                for decl in declarations:
                    if isinstance(decl.type, c_ast.PtrDecl):
                        self.__pointers_info.append(decl.name)
                    elif isinstance(decl.type, c_ast.TypeDecl):
                        node_type = decl.type.type.names[0]
                        if node_type == 'int':
                            self.__variables_info[decl.name] = z3.IntSort()
                        if node_type == 'double':
                            self.__variables_info[decl.name] = z3.RealSort()
                        if node_type == 'bool':
                            self.__variables_info[decl.name] = z3.BoolSort()

    def visit_FuncDef(self, ast):
        self.__functions[ast.decl.name] = ast

        # for each function finds the last return statement
        inst_num = len(ast.body.block_items) - 1
        return_line = ast.body.block_items[inst_num].coord.line
        self.__return_line.append(return_line)
        self.__in_function = True
        self.generic_visit(ast.body)
        self.__in_function = False

    @property
    def variables_info(self):
        return self.__variables_info

    @property
    def pointers_info(self):
        return self.__pointers_info

    @property
    def functions(self):
        return self.__functions

    @property
    def return_line(self):
        return self.__return_line
