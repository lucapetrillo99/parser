import os
import json
import constants
from pycparser import c_ast


class FileConstructor:
    def __init__(self, visitor):
        self.visitor = visitor
        self.instructions = {}
        self.successors = {}

    def build_file(self):
        for k, v in self.visitor.statement_dict.items():
            listing = constants.LISTING.format(k)
            if isinstance(v, c_ast.Assignment):
                if isinstance(v.rvalue, c_ast.BinaryOp):
                    self.instructions[listing] = {
                        "exp": constants.EXPRESSION.format(v.rvalue.left.name, v.rvalue.op, v.rvalue.right.name),
                        "op": constants.BIN_EXPR_ASSIGN.format(v.lvalue.name)}
                    succ = constants.SUCCESSOR.format(k)
                    self.successors[succ] = k + 1
                else:
                    if isinstance(v.rvalue, c_ast.Constant):
                        r_value = v.rvalue.value
                    else:
                        r_value = v.rvalue.name

                    if v.lvalue.name in self.visitor.ptr_var:
                        self.instructions[listing] = constants.PTR_ASSIGN.format(v.lvalue.name, r_value)
                        succ = constants.SUCCESSOR.format(k)
                        self.successors[succ] = k + 1
                    else:
                        self.instructions[listing] = {
                            "exp": v.rvalue.name, "op": constants.BIN_EXPR_ASSIGN.format(v.lvalue.name)}
                        succ = constants.SUCCESSOR.format(k)
                        self.successors[succ] = k + 1

            elif isinstance(v, c_ast.While):
                try:
                    self.instructions[listing] = {"cond": constants.HEAP_COND.format(v.cond.left.name,
                                                                                     v.cond.right.name),
                                                  "op": constants.WHILE_COND}
                except AttributeError:
                    self.instructions[listing] = {
                        "cond": constants.HEAP_COND.format(v.cond.left.name, v.cond.right),
                        "op": constants.WHILE_COND}

                succ = constants.SUCCESSOR.format(k)
                self.successors[succ] = self.visitor.constructs[k]

            elif isinstance(v, c_ast.If):
                if isinstance(v.cond.right, c_ast.Constant):
                    right = v.cond.right.value
                else:
                    right = v.cond.right.name

                self.instructions[listing] = {"cond": constants.EXPRESSION.format(v.cond.left.name, v.cond.op, right),
                                              "op": constants.IF_COND}
                succ = constants.SUCCESSOR.format(k)
                self.successors[succ] = self.visitor.constructs[k]

            elif isinstance(v, c_ast.UnaryOp):
                # TODO: syntax for unary operations
                pass

            elif isinstance(v, c_ast.Return):
                self.instructions[listing] = constants.EXIT_COND
                succ = constants.SUCCESSOR.format(k)
                self.successors[succ] = None

    def write_file(self, filename):
        os.makedirs(constants.OUT_DIR, exist_ok=True)
        split_file = filename.split(".")[0].split("/")
        f = split_file[len(split_file) - 1] + ".py"
        with open(os.path.join("out/", f), "w") as file:
            file.write("%s = %s\n" % (constants.DATA_DECL, json.dumps(self.visitor.var_dict)))
            file.write("%s = %s\n\n" % (constants.PTR_DECL, json.dumps(self.visitor.PtrFieldSort)))
            for k, v in self.visitor.function_dict.items():
                file.write('%s = %s\n' % (k, v))

            file.write('\n')
            for k, v in zip(self.instructions.items(), self.successors.items()):
                if isinstance(k[1], str):
                    file.write('%s = %s\n' % (k[0], k[1]))
                    file.write('%s = %s\n' % (v[0], v[1]))
                elif isinstance(k[1], dict):
                    file.write('%s = %s\n' % (list(k[1].keys())[0], list(k[1].values())[0]))
                    file.write('%s = %s\n' % (k[0], list(k[1].values())[1]))
                    file.write('%s = %s\n' % (v[0], v[1]))
