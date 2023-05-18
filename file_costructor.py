from pycparser import c_ast

exp = "{} {} {}"
listing = "listing[{0}]"
succ = "succ[{}]"
bin_exp_assign = "PL.ExpAssign({}, exp)"
ptr_assign = "PL.PtrAssign({}, {})"
heap_condition = "HeapCond.Eq({}, {})"


class FileConstructor:
    def __init__(self, visitor):
        self.visitor = visitor
        self.instructions = {}
        self.successors = {}

    def build_file(self):
        print(self.visitor.statement_dict)
        for k, v in self.visitor.statement_dict.items():
            l = listing.format(k)
            if isinstance(v, c_ast.Assignment):
                if isinstance(v.rvalue, c_ast.BinaryOp):
                    self.instructions[l] = {"exp": exp.format(v.rvalue.left.name, v.rvalue.op, v.rvalue.right.name),
                                            "op": bin_exp_assign.format(v.lvalue.name)}
                    s = succ.format(k)
                    self.successors[s] = k + 1
                else:
                    if isinstance(v.rvalue, c_ast.Constant):
                        r_value = v.rvalue.value
                    else:
                        r_value = v.rvalue.name

                    if v.lvalue.name in self.visitor.ptr_var:
                        self.instructions[l] = ptr_assign.format(v.lvalue.name, r_value)
                        s = succ.format(k)
                        self.successors[s] = k + 1
                    else:
                        # TODO: syntax for unary assignments
                        pass

            elif isinstance(v, c_ast.While):
                self.instructions[l] = {"cond": heap_condition.format(v.cond.left.name, v.cond.right.name),
                                        "op": "PL.While(cond)"}
                s = succ.format(k)
                self.successors[s] = self.visitor.constructs[k]

            elif isinstance(v, c_ast.If):
                if isinstance(v.cond.right, c_ast.Constant):
                    right = v.cond.right.value
                else:
                    right = v.cond.right.name

                self.instructions[l] = {"cond": exp.format(v.cond.right.value, v.cond.op, right),
                                        "op": "PL.If(cond)"}
                s = succ.format(k)
                self.successors[s] = self.visitor.constructs[k]

            elif isinstance(v, c_ast.UnaryOp):
                # TODO: syntax for unary operations
                pass

            elif isinstance(v, c_ast.Return):
                self.instructions[l] = "PL.Exit()"
                s = succ.format(k)
                self.successors[s] = None
