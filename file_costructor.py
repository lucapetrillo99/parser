import os
import constants
import statements
from pycparser import c_ast


class FileConstructor:
    def __init__(self, visitor):
        self.visitor = visitor
        self.inst = []
        self.succ = []
        self.instructions = {}
        self.successors = {}

    def build_file(self):
        for line, instruction in self.visitor.stmts_bindings.items():
            if isinstance(instruction, c_ast.Assignment):
                if isinstance(instruction.rvalue, c_ast.BinaryOp):
                    l_value, left_r_value, right_r_value = self.__binary_assignment_handler(instruction)
                    exp = constants.EXPRESSION.format(left_r_value, instruction.rvalue.op, right_r_value)
                    self.inst.append(statements.ExpAssign(l_value, exp))
                else:
                    statement = self.__unary_assignment_handler(instruction)
                    self.inst.append(statement)

                if line in list(self.visitor.then_successors.keys()):
                    self.succ.append(self.visitor.then_successors[line])
                else:
                    self.succ.append(line + 1)

            # elif isinstance(instruction, c_ast.While):
            # if instruction.cond.op == "==":
            #     self.instructions[listing] = {"cond": constants.EQ_HEAP_COND.format(instruction.cond.left.name,
            #                                                                         instruction.cond.right.name),
            #                                   "op": constants.WHILE_COND}
            # else:
            #     self.instructions[listing] = {"cond": constants.NEQ_HEAP_COND.format(instruction.cond.left.name,
            #                                                                          instruction.cond.right.name),
            #                                   "op": constants.WHILE_COND}
            #
            # succ = constants.SUCCESSOR.format(line)
            # self.successors[succ] = self.visitor.constructs_info[line]

            elif isinstance(instruction, c_ast.If):
                left_cond, right_cond = self.__unary_operation_handler(instruction)
                cond = constants.EXPRESSION.format(left_cond, instruction.cond.op, right_cond)
                self.inst.append(statements.If(cond))
                self.succ.append(self.visitor.constructs_info[line])

            elif isinstance(instruction, c_ast.UnaryOp):
                if isinstance(instruction.expr, c_ast.StructRef):
                    variable_name = instruction.expr.name.name + instruction.expr.type + instruction.expr.field.name
                else:
                    variable_name = instruction.expr.name

                if instruction.op == "p++":
                    exp = constants.EXPRESSION.format(variable_name, "+", "1")
                else:
                    exp = constants.EXPRESSION.format(variable_name, "-", "1")

                self.inst.append(statements.ExpAssign(variable_name, exp))

                if line in list(self.visitor.then_successors.keys()):
                    self.succ.append(self.visitor.then_successors[line])
                else:
                    self.succ.append(line + 1)

            elif isinstance(instruction, c_ast.Return):
                try:
                    self.inst.append(self.visitor.constructs_info[line])
                    self.succ.append(list(self.visitor.stmts_bindings)[-1])
                except KeyError:
                    self.inst.append(statements.Exit())
                    self.succ.append(None)

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
            """ case of pointer assignment like: p->data = b + c """
            left_value = constants.STRUCT_VAR.format(node.lvalue.name.name, node.lvalue.type, node.lvalue.field.name)
        else:
            """ case of assignment like: p = [everything] """
            left_value = node.lvalue.name

        if isinstance(node.rvalue.left, c_ast.StructRef):
            """ case of assignment like: a = p->data + c """
            left_r_value = constants.STRUCT_VAR.format(node.rvalue.left.name.name, node.rvalue.left.type,
                                                       node.rvalue.left.field.name)
        else:
            left_r_value = node.rvalue.left.name

        if isinstance(node.rvalue.right, c_ast.StructRef):
            """ case of pointer assignment like: a = c + p->data """
            right_r_value = constants.STRUCT_VAR.format(node.rvalue.right.name.name, node.rvalue.right.type,
                                                        node.rvalue.right.field.name)
        elif isinstance(node.rvalue.right, c_ast.Constant):
            right_r_value = node.rvalue.right.value
        else:
            right_r_value = node.rvalue.right.name

        return left_value, left_r_value, right_r_value

    def __unary_assignment_handler(self, node):
        is_left_ptr = False
        is_left_field = False
        is_right_ptr = False
        is_right_field = False
        is_right_constant = False
        field = None

        if isinstance(node.lvalue, c_ast.StructRef):
            """ case of left value like: p->field = * """
            is_left_field = True
            left_value = node.lvalue.name.name
            field = node.lvalue.field.name
        elif isinstance(node.lvalue, c_ast.UnaryOp):
            """ case of left value like: *root = * """
            is_left_ptr = True
            left_value = node.lvalue.op + node.lvalue.expr.name
        else:
            """ case of left value like: p = * """
            left_value = node.lvalue.name
            if left_value in self.visitor.function_pointers:
                is_left_ptr = True

        if isinstance(node.rvalue, c_ast.StructRef):
            """ case of right value like: * = q->field """
            is_right_field = True
            right_value = node.rvalue.name.name
            field = node.rvalue.field.name
        elif isinstance(node.rvalue, c_ast.Constant):
            """ case of assignment like: * = 1 """
            is_right_constant = True
            right_value = node.rvalue.value
        elif isinstance(node.rvalue, c_ast.UnaryOp):
            """ case of pointer assignment like: * = *root """
            is_right_ptr = True
            right_value = node.rvalue.op + node.rvalue.expr.name
        else:
            """ case of pointer assignment like: * = q """
            right_value = node.rvalue.name
            if right_value in self.visitor.function_pointers:
                is_right_ptr = True

        if is_left_ptr and is_right_ptr:
            """ case: p = q """
            statement = statements.PtrAssign(left_value, right_value)
        elif is_left_field and is_right_ptr:
            """ case: p->pfield = q """
            statement = statements.ToPtrFieldAssign(left_value, field, right_value)
        elif is_left_ptr and is_right_field:
            """ case: p = q->pfield """
            statement = statements.FromPtrFieldAssign(left_value, right_value, field)
        elif not is_left_ptr and is_right_field:
            """ case: d = p->datafield """
            statement = statements.FromDataFieldAssign(left_value, right_value, field)
        elif is_left_field and not is_right_ptr:
            """ case: p->datafield = d """
            statement = statements.ToDataFieldAssign(left_value, field, right_value)
        elif is_left_ptr and is_right_constant:
            """ case: p = NULL """
            statement = statements.NilAssign(left_value)
        else:
            statement = statements.ExpAssign(left_value, right_value)

        return statement

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
