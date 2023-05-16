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
        self.statement_dict = {}
        self.line_number = 1
        self.constructs = {}

    def visit_FuncDef(self, node):
        # print(node.body.block_items[7])
        # while_cond.next.show()
        self.generic_visit(node.body)

    def generic_visit(self, node):
        if isinstance(node, c_ast.Compound):
            for stmt in node.block_items:
                if not isinstance(stmt, c_ast.Decl):
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
    print(visitor.statement_dict)
    print(visitor.constructs)
    # for k, v in visitor.statement_dict.items():
    #     if isinstance(v, c_ast.Assignment):
    #         print(v)
