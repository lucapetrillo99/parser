import os
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
                    if isinstance(v.lvalue, c_ast.StructRef):
                        l_value = constants.STRUCT_VAR.format(v.lvalue.name.name, v.lvalue.type, v.lvalue.field.name)
                    else:
                        l_value = v.lvalue.name

                    if isinstance(v.rvalue.left, c_ast.StructRef):
                        left_r_value = constants.STRUCT_VAR.format(v.rvalue.left.name.name, v.rvalue.left.type,
                                                                   v.rvalue.left.field.name)
                    else:
                        left_r_value = v.rvalue.left.name

                    if isinstance(v.rvalue.right, c_ast.StructRef):
                        right_r_value = constants.STRUCT_VAR.format(v.rvalue.left.name.name, v.rvalue.left.type,
                                                                    v.rvalue.left.field.name)
                    else:
                        right_r_value = v.rvalue.right.name

                    self.instructions[listing] = {
                        "exp": constants.EXPRESSION.format(left_r_value, v.rvalue.op, right_r_value),
                        "op": constants.BIN_EXPR_ASSIGN.format(l_value)}
                    succ = constants.SUCCESSOR.format(k)
                    self.successors[succ] = k + 1
                else:
                    if isinstance(v.lvalue, c_ast.StructRef):
                        l_value = constants.STRUCT_VAR.format(v.lvalue.name.name, v.lvalue.type, v.lvalue.field.name)
                    else:
                        l_value = v.lvalue.name

                    if isinstance(v.rvalue, c_ast.StructRef):
                        r_value = constants.STRUCT_VAR.format(v.rvalue.name.name, v.rvalue.type, v.rvalue.field.name)
                    elif isinstance(v.rvalue, c_ast.Constant):
                        r_value = v.rvalue.value
                    else:
                        r_value = v.rvalue.name

                    if l_value in self.visitor.ptr_var:
                        self.instructions[listing] = constants.PTR_ASSIGN.format(l_value, r_value)
                        succ = constants.SUCCESSOR.format(k)
                        self.successors[succ] = k + 1
                    else:
                        self.instructions[listing] = {"exp": r_value,
                                                      "op": constants.BIN_EXPR_ASSIGN.format(l_value)}
                        succ = constants.SUCCESSOR.format(k)
                        self.successors[succ] = k + 1

            elif isinstance(v, c_ast.While):
                if v.cond.op == "==":
                    self.instructions[listing] = {"cond": constants.EQ_HEAP_COND.format(v.cond.left.name,
                                                                                        v.cond.right.name),
                                                  "op": constants.WHILE_COND}
                else:
                    self.instructions[listing] = {"cond": constants.NEQ_HEAP_COND.format(v.cond.left.name,
                                                                                         v.cond.right.name),
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
                if v.op == "p++":
                    self.instructions[listing] = {
                        "exp": constants.EXPRESSION.format(v.expr.name, "+", "1"),
                        "op": constants.BIN_EXPR_ASSIGN.format(v.expr.name)}
                else:
                    self.instructions[listing] = {
                        "exp": constants.EXPRESSION.format(v.expr.name, "-", "1"),
                        "op": constants.BIN_EXPR_ASSIGN.format(v.expr.name)}

                succ = constants.SUCCESSOR.format(k)
                self.successors[succ] = k + 1

            elif isinstance(v, c_ast.Return):
                try:
                    self.instructions[listing] = self.visitor.constructs[k]
                    succ = constants.SUCCESSOR.format(k)
                    self.successors[succ] = list(self.visitor.statement_dict)[-1]

                except KeyError:
                    self.instructions[listing] = constants.EXIT_COND
                    succ = constants.SUCCESSOR.format(k)
                    self.successors[succ] = None

    def write_file(self, filename):
        os.makedirs(constants.OUT_DIR, exist_ok=True)
        split_file = filename.split(".")[0].split("/")
        f = split_file[len(split_file) - 1] + ".py"
        with open(os.path.join("out/", f), "w") as file:
            file.write("%s\n" % constants.TREE_DECL.format(len(self.visitor.var_dict), len(self.visitor.PtrFieldSort)))

            for ptr in self.visitor.PtrFieldSort:
                file.write("%s = %s\n" % (ptr, constants.PTR_DECL.format(ptr)))

            for name, var_type in self.visitor.var_dict.items():
                file.write("%s = %s\n" % (name, constants.VAR_DECL.format(name, var_type)))

            file.write("\n")
            file.write("%s\n" % constants.FUNCTION.format(len(self.visitor.vars), len(self.visitor.ptr_var)))

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

            file.write("\n")
            file.write(constants.FUNCTION_CLOSE)
