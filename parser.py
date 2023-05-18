from __future__ import print_function
import argparse
import sys

from z3 import *

# This is not required if you've installed pycparser into
# your site-packages/ with setup.py
sys.path.extend(['.', '..'])
from ast_visitor import AstVisitor
from file_costructor import FileConstructor
from pycparser import parse_file, c_generator, c_ast, c_parser

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
    visitor = AstVisitor()
    visitor.visit(ast)
    f_cons = FileConstructor(visitor)
    f_cons.build_file()
    f_cons.write_file(args.filename)
    # print(instructions)
    # print(successors)
    # print(visitor.constructs)
    # print(visitor.var_dict)
    # print(visitor.PtrFieldSort)
    # for k, v in visitor.statement_dict.items():
    #     if isinstance(v, c_ast.Assignment):
    #         print(v)
