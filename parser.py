from __future__ import print_function
import argparse
import sys
import statements

# from z3 import *

# This is not required if you've installed pycparser into
# your site-packages/ with setup.py
sys.path.extend(['.', '..'])
from ast_visitor import AstVisitor
from function_visitor import FunctionVisitor
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
    inst_num = len(ast.ext) - 1
    last_return = ast.ext[inst_num].body.block_items[len(ast.ext[inst_num].body.block_items) - 1].coord.line
    fun_vis = FunctionVisitor()
    fun_vis.visit(ast)
    F = []
    for f in fun_vis.functions:
        visitor = AstVisitor(last_return)
        visitor.visit(f)
        f_cons = FileConstructor(fun_vis, visitor)
        tree_decl, fun = f_cons.build_file()
        F.append(fun)
