from __future__ import print_function
import argparse
import sys

from z3 import *

# This is not required if you've installed pycparser into
# your site-packages/ with setup.py
sys.path.extend(['.', '..'])
from ast_visitor import AstVisitor
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

    # instructions = {}
    # successors = {}
    # exp = "{} {} {}"
    # listing = "listing[{0}]"
    # succ = "succ[{}]"
    # bin_exp_assign = "PL.ExpAssign({}, exp)"
    # ptr_assign = "PL.PtrAssign({}, {})"
    # heap_condition = "HeapCond.Eq({}, {})"
    #
    # for k, v in visitor.statement_dict.items():
    #     l = listing.format(k)
    #     if isinstance(v, c_ast.Assignment):
    #         if isinstance(v.rvalue, c_ast.BinaryOp):
    #             instructions[l] = {"exp": exp.format(v.rvalue.left.name, v.rvalue.op, v.rvalue.right.name),
    #                                "op": bin_exp_assign.format(v.lvalue.name)}
    #             s = succ.format(k)
    #             successors[s] = k + 1
    #         else:
    #             if isinstance(v.rvalue, c_ast.Constant):
    #                 r_value = v.rvalue.value
    #             else:
    #                 r_value = v.rvalue.name
    #
    #             if v.lvalue.name in visitor.ptr_var:
    #                 instructions[l] = ptr_assign.format(v.lvalue.name, r_value)
    #                 s = succ.format(k)
    #                 successors[s] = k + 1
    #             else:
    #                 # TODO: syntax for unary assignments
    #                 pass
    #
    #     elif isinstance(v, c_ast.While):
    #         instructions[l] = {"cond": heap_condition.format(v.cond.left.name, v.cond.right.name),
    #                            "op": "PL.While(cond)"}
    #         s = succ.format(k)
    #         successors[s] = visitor.constructs[k]
    #
    #     elif isinstance(v, c_ast.If):
    #         if isinstance(v.cond.right, c_ast.Constant):
    #             right = v.cond.right.value
    #         else:
    #             right = v.cond.right.name
    #
    #         instructions[l] = {"cond": exp.format(v.cond.right.value, v.cond.op, right),
    #                            "op": "PL.If(cond)"}
    #         s = succ.format(k)
    #         successors[s] = visitor.constructs[k]
    #
    #     elif isinstance(v, c_ast.UnaryOp):
    #         # TODO: syntax for unary operations
    #         pass
    #
    #     elif isinstance(v, c_ast.Return):
    #         instructions[l] = "PL.Exit()"
    #         s = succ.format(k)
    #         successors[s] = None

    print(visitor.statement_dict)
    # print(instructions)
    # print(successors)
    # print(visitor.constructs)
    # print(visitor.var_dict)
    # print(visitor.PtrFieldSort)
    # for k, v in visitor.statement_dict.items():
    #     if isinstance(v, c_ast.Assignment):
    #         print(v)
