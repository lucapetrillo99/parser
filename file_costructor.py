import os
import constants
from pycparser import c_ast


class FileConstructor:
    def __init__(self, visitor):
        self.visitor = visitor
        self.instructions = {}
        self.successors = {}

    def build_file(self):
        for line, instruction in self.visitor.stmts_bindings.items():
            listing = constants.LISTING.format(line)
            if isinstance(instruction, c_ast.Assignment):
                if isinstance(instruction.rvalue, c_ast.BinaryOp):
                    l_value, left_r_value, right_r_value = self.__binary_assignment_handler(instruction)

                    self.instructions[listing] = {
                        "exp": constants.EXPRESSION.format(left_r_value, instruction.rvalue.op, right_r_value),
                        "op": constants.BIN_EXPR_ASSIGN.format(l_value)}

                    succ = constants.SUCCESSOR.format(line)
                    if line in list(self.visitor.then_successors.keys()):
                        self.successors[succ] = self.visitor.then_successors[line]
                    else:
                        self.successors[succ] = line + 1

                else:
                    l_value, r_value, is_ptr = self.__unary_assignment_handler(instruction)
                    if l_value in self.visitor.function_pointers or is_ptr:
                        self.instructions[listing] = constants.PTR_ASSIGN.format(l_value, r_value)
                    else:
                        self.instructions[listing] = {"exp": r_value,
                                                      "op": constants.BIN_EXPR_ASSIGN.format(l_value)}

                    succ = constants.SUCCESSOR.format(line)
                    if line in list(self.visitor.then_successors.keys()):
                        self.successors[succ] = self.visitor.then_successors[line]
                    else:
                        self.successors[succ] = line + 1

            elif isinstance(instruction, c_ast.While):
                if instruction.cond.op == "==":
                    self.instructions[listing] = {"cond": constants.EQ_HEAP_COND.format(instruction.cond.left.name,
                                                                                        instruction.cond.right.name),
                                                  "op": constants.WHILE_COND}
                else:
                    self.instructions[listing] = {"cond": constants.NEQ_HEAP_COND.format(instruction.cond.left.name,
                                                                                         instruction.cond.right.name),
                                                  "op": constants.WHILE_COND}

                succ = constants.SUCCESSOR.format(line)
                self.successors[succ] = self.visitor.constructs_info[line]

            elif isinstance(instruction, c_ast.If):
                left_cond, right_cond = self.__unary_operation_handler(instruction)
                self.instructions[listing] = {
                    "cond": constants.EXPRESSION.format(left_cond, instruction.cond.op, right_cond),
                    "op": constants.IF_COND}
                succ = constants.SUCCESSOR.format(line)
                self.successors[succ] = self.visitor.constructs_info[line]

            elif isinstance(instruction, c_ast.UnaryOp):
                if isinstance(instruction.expr, c_ast.StructRef):
                    variable_name = instruction.expr.name.name + instruction.expr.type + instruction.expr.field.name
                else:
                    variable_name = instruction.expr.name

                if instruction.op == "p++":
                    self.instructions[listing] = {
                        "exp": constants.EXPRESSION.format(variable_name, "+", "1"),
                        "op": constants.BIN_EXPR_ASSIGN.format(variable_name)}
                else:
                    self.instructions[listing] = {
                        "exp": constants.EXPRESSION.format(variable_name, "-", "1"),
                        "op": constants.BIN_EXPR_ASSIGN.format(variable_name)}

                succ = constants.SUCCESSOR.format(line)
                if line in list(self.visitor.then_successors.keys()):
                    self.successors[succ] = self.visitor.then_successors[line]
                else:
                    self.successors[succ] = line + 1

            elif isinstance(instruction, c_ast.Return):
                try:
                    self.instructions[listing] = self.visitor.constructs_info[line]
                    succ = constants.SUCCESSOR.format(line)
                    self.successors[succ] = list(self.visitor.stmts_bindings)[-1]

                except KeyError:
                    self.instructions[listing] = constants.EXIT_COND
                    succ = constants.SUCCESSOR.format(line)
                    self.successors[succ] = None

    def write_file(self, filename):
        os.makedirs(constants.OUT_DIR, exist_ok=True)
        split_file = filename.split(".")[0].split("/")
        f = split_file[len(split_file) - 1] + ".py"
        with open(os.path.join("out/", f), "w") as file:
            file.write(
                "%s\n" % constants.TREE_DECL.format(len(self.visitor.variables_info), len(self.visitor.pointers_info)))

            for ptr in self.visitor.pointers_info:
                file.write("%s = %s\n" % (ptr, constants.PTR_DECL.format(ptr)))

            for name, var_type in self.visitor.variables_info.items():
                file.write("%s = %s\n" % (name, constants.VAR_DECL.format(name, var_type)))

            file.write("\n")
            file.write("%s\n" % constants.FUNCTION.format(len(self.visitor.function_variables),
                                                          sum(1 for v in self.visitor.function_pointers.values()
                                                              if v == 'function')))

            for name, value in self.visitor.function_pointers.items():
                if value == 'function':
                    file.write("%s = %s\n" % (name, constants.GET_PTR.format(name)))

            for name, var_type in self.visitor.function_variables.items():
                file.write("%s = %s\n" % (name, constants.GET_VAR.format(name, var_type)))

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

    @staticmethod
    def __binary_assignment_handler(node):
        if isinstance(node.lvalue, c_ast.StructRef):
            left_value = constants.STRUCT_VAR.format(node.lvalue.name.name, node.lvalue.type, node.lvalue.field.name)
        else:
            left_value = node.lvalue.name

        if isinstance(node.rvalue.left, c_ast.StructRef):
            left_r_value = constants.STRUCT_VAR.format(node.rvalue.left.name.name, node.rvalue.left.type,
                                                       node.rvalue.left.field.name)
        else:
            left_r_value = node.rvalue.left.name

        if isinstance(node.rvalue.right, c_ast.StructRef):
            right_r_value = constants.STRUCT_VAR.format(node.rvalue.left.name.name, node.rvalue.left.type,
                                                        node.rvalue.left.field.name)
        else:
            right_r_value = node.rvalue.right.name

        return left_value, left_r_value, right_r_value

    @staticmethod
    def __unary_assignment_handler(node):
        is_ptr = False
        if isinstance(node.lvalue, c_ast.StructRef):
            is_ptr = True
            left_value = constants.STRUCT_VAR.format(node.lvalue.name.name, node.lvalue.type, node.lvalue.field.name)
        elif isinstance(node.lvalue, c_ast.UnaryOp):
            is_ptr = True
            left_value = node.lvalue.op + node.lvalue.expr.name
        else:
            left_value = node.lvalue.name

        if isinstance(node.rvalue, c_ast.StructRef):
            is_ptr = True
            right_value = constants.STRUCT_VAR.format(node.rvalue.name.name, node.rvalue.type, node.rvalue.field.name)
        elif isinstance(node.rvalue, c_ast.Constant):
            right_value = node.rvalue.value
        elif isinstance(node.rvalue, c_ast.UnaryOp):
            right_value = node.rvalue.op + node.rvalue.expr.name
        else:
            right_value = node.rvalue.name

        return left_value, right_value, is_ptr

    @staticmethod
    def __unary_operation_handler(node):
        if isinstance(node.cond.left, c_ast.UnaryOp):
            left_cond = node.cond.left.op + node.cond.left.expr.name
            right_cond = node.cond.right.name
        elif isinstance(node.cond.right, c_ast.UnaryOp):
            left_cond = node.cond.left.name
            right_cond = node.cond.right.op + node.cond.right.expr.name
        elif isinstance(node.cond.right, c_ast.Constant):
            left_cond = node.cond.left.name
            right_cond = node.cond.right.value
        else:
            left_cond = node.cond.left.name
            right_cond = node.cond.right.name

        return left_cond, right_cond
