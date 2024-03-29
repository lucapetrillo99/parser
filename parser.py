import sys
import debug
import argparse
from ast_visitor import AstVisitor
from function_visitor import FunctionVisitor
from statements_handler import StatementsHandler

sys.path.extend(['.', '..'])
from pycparser import parse_file

if __name__ == "__main__":
    arg_parser = argparse.ArgumentParser('Parse a C file')
    arg_parser.add_argument('filename', help='name of file to parse')
    arg_parser.add_argument('--print-result', action='store_true', help="prints the result of the instructions")
    arg_parser.add_argument('--no-print-result', dest='print', action='store_false',
                            help="does not print the result of the instruction")
    arg_parser.set_defaults(print_result=False)
    args = arg_parser.parse_args()

    ast = parse_file(args.filename, use_cpp=True, cpp_path='cpp', cpp_args=r'-Iutils/fake_libc_include')

    # explores all functions in the code
    fun_vis = FunctionVisitor()
    fun_vis.visit(ast)
    tree_decl = None
    functions = []
    for i, (f_name, body) in enumerate(fun_vis.functions.items()):

        # visits the AST of each explored function
        visitor = AstVisitor(fun_vis.return_line[i])
        visitor.visit(body)
        f_cons = StatementsHandler(fun_vis, visitor, f_name)

        # create z3 compatible statements
        tree_decl, fun = f_cons.build_statements()
        functions.append(fun)

        if args.print_result:
            debug.print_result(tree_decl, fun, f_cons)
