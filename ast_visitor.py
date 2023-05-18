from pycparser import c_ast


class AstVisitor(c_ast.NodeVisitor):
    def __init__(self):
        self.in_function = False
        self.var_dict = {}
        self.PtrFieldSort = []
        self.statement_dict = {}
        self.line_number = 0
        self.constructs = {}
        self.function_dict = {}
        self.ptr_var = []

    def visit_Decl(self, node):
        if not self.in_function:
            if isinstance(node.type, c_ast.PtrDecl):
                self.PtrFieldSort.append(node.name)
            if isinstance(node.type, c_ast.TypeDecl):
                node_type = node.type.type.names[0]
                if node_type == 'int':
                    self.var_dict[node.name] = "z3.IntSort()"
                if node_type == 'double':
                    self.var_dict[node.name] = "z3.RealSort()"
                if node_type == 'bool':
                    self.var_dict[node.name] = "z3.BoolSort()"

    def visit_FuncDef(self, node):
        self.function_dict['F'] = "Function()"
        self.in_function = True
        self.generic_visit(node.body)
        self.in_function = False

    def generic_visit(self, node):
        if isinstance(node, c_ast.Compound):
            for stmt in node.block_items:
                if isinstance(stmt, c_ast.Decl):
                    if isinstance(stmt.type, c_ast.PtrDecl):
                        self.ptr_var.append(stmt.name)
                        self.function_dict[stmt.name] = "F.getPtr()"
                    else:
                        node_type = stmt.type.type.names[0]
                        if node_type == 'int':
                            self.function_dict[stmt.type.declname] = "F.getVar(z3.IntSort)"
                        if node_type == 'double':
                            self.function_dict[stmt.type.declname] = "F.getVar(z3.RealSort)"
                        if node_type == 'bool':
                            self.function_dict[stmt.type.declname] = "F.getVar(z3.BoolSort)"
                else:
                    self.statement_dict[self.line_number] = stmt
                    self.line_number += 1

                self.visit(stmt)

        elif isinstance(node, c_ast.If):
            curr_line_number = self.line_number
            self.constructs[curr_line_number - 1] = self.line_number
            self.visit(node.iftrue)
            if node.iffalse:
                self.constructs[curr_line_number - 1] = (self.constructs[curr_line_number - 1], self.line_number)
                self.visit(node.iffalse)
        elif isinstance(node, c_ast.While):
            curr_line_number = self.line_number
            self.visit(node.stmt)
            self.constructs[curr_line_number - 1] = (curr_line_number, self.line_number)
        elif isinstance(node, c_ast.For):
            curr_line_number = self.line_number
            self.visit(node.stmt)
            self.constructs[curr_line_number - 1] = (curr_line_number, self.line_number)
        else:
            super().generic_visit(node)