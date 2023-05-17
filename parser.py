from __future__ import print_function
import argparse
import sys

from z3 import *

# This is not required if you've installed pycparser into
# your site-packages/ with setup.py
sys.path.extend(['.', '..'])
from pycparser import parse_file, c_generator, c_ast, c_parser


class Z3Generator(c_ast.NodeVisitor):
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
                    self.var_dict[node.name] = IntSort()
                if node_type == 'double':
                    self.var_dict[node.name] = RealSort()
                if node_type == 'bool':
                    self.var_dict[node.name] = BoolSort()

    def visit_FuncDef(self, node):
        # print(node.body.block_items[7])
        # while_cond.next.show()
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
                # print(stmt)
                # if isinstance(stmt, (c_ast.Return, c_ast.Break, c_ast.Continue)):
                    # if the loop is exited by a return, break, or continue statement,
                    # store the current statement as the exit statement
                    # print("esco:", self.line_number)

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


if __name__ == "__main__":
    argparser = argparse.ArgumentParser('Dump AST')
    argparser.add_argument('filename',
                           default='examples/c_files/basic.c',
                           nargs='?',
                           help='name of file to parse')
    args = argparser.parse_args()

    ast = parse_file(args.filename, use_cpp=True,
                     cpp_path='cpp',
                     cpp_args=r'-Iutils/fake_libc_include')

    # ast.show(showcoord=True)
    visitor = Z3Generator()
    visitor.visit(ast)

    instructions = {}
    successors = {}
    exp = "{} {} {}"
    listing = "listing[{0}]"
    succ = "succ[{}]"
    bin_exp_assign = "PL.ExpAssign({}, exp)"
    ptr_assign = "PL.PtrAssign({}, {})"
    heap_condition = "HeapCond.Eq({}, {})"

    for k, v in visitor.statement_dict.items():
        l = listing.format(k)
        if isinstance(v, c_ast.Assignment):
            if isinstance(v.rvalue, c_ast.BinaryOp):
                instructions[l] = {"exp": exp.format(v.rvalue.left.name, v.rvalue.op, v.rvalue.right.name),
                                   "op": bin_exp_assign.format(v.lvalue.name)}
                s = succ.format(k)
                successors[s] = k + 1
            else:
                if isinstance(v.rvalue, c_ast.Constant):
                    r_value = v.rvalue.value
                else:
                    r_value = v.rvalue.name

                if v.lvalue.name in visitor.ptr_var:
                    instructions[l] = ptr_assign.format(v.lvalue.name, r_value)
                    s = succ.format(k)
                    successors[s] = k + 1
                else:
                    # TODO: syntax for unary assignments
                    pass

        elif isinstance(v, c_ast.While):
            instructions[l] = {"cond": heap_condition.format(v.cond.left.name, v.cond.right.name),
                               "op": "PL.While(cond)"}
            s = succ.format(k)
            successors[s] = visitor.constructs[k]

        elif isinstance(v, c_ast.If):
            if isinstance(v.cond.right, c_ast.Constant):
                right = v.cond.right.value
            else:
                right = v.cond.right.name

            instructions[l] = {"cond": exp.format(v.cond.right.value, v.cond.op, right),
                               "op": "PL.If(cond)"}
            s = succ.format(k)
            successors[s] = visitor.constructs[k]

        elif isinstance(v, c_ast.UnaryOp):
            # TODO: syntax for unary operations
            pass

        elif isinstance(v, c_ast.Return):
            instructions[l] = "PL.Exit()"
            s = succ.format(k)
            successors[s] = None

    print(instructions)
    print(successors)
    # print(visitor.statement_dict)
    # print(visitor.constructs)
    # print(visitor.var_dict)
    # print(visitor.PtrFieldSort)
    # for k, v in visitor.statement_dict.items():
    #     if isinstance(v, c_ast.Assignment):
    #         print(v)
