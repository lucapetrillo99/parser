import constants
import statements
import function
from pycparser import c_ast


class FileConstructor:
    def __init__(self, visitor):
        self.visitor = visitor
        self.inst = []
        self.succ = []
        self.fun_vars = {}
        self.vars = {}

    def build_file(self):
        fun_decl = self.write_file()
        heap_cond = statements.makeCondSort(fun_decl.getPtrIdSort())

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

            elif isinstance(instruction, c_ast.While):
                if isinstance(instruction.cond, c_ast.ID):
                    cond = heap_cond.EqNil(self.fun_vars[instruction.cond.name])
                elif isinstance(instruction.cond, c_ast.UnaryOp):
                    cond = heap_cond.NeqNil(self.fun_vars[instruction.cond.expr.name])
                else:
                    if instruction.cond.op == "==":
                        cond = heap_cond.Eq(self.fun_vars[instruction.cond.left.name],
                                            self.fun_vars[instruction.cond.right.name])
                    elif instruction.cond.op == "!=":
                        cond = heap_cond.Neq(self.fun_vars[instruction.cond.left.name],
                                             self.fun_vars[instruction.cond.right.name])
                self.inst.append(statements.While(cond))
                self.succ.append(self.visitor.constructs_info[line])

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

    def write_file(self):
        vars_number = len(self.visitor.variables_info)
        ptrs_number = len(self.visitor.pointers_info)
        tree_decl = function.VarDecl("fld_", nVars=vars_number, nPtrs=ptrs_number)

        for ptr in self.visitor.pointers_info:
            self.vars[ptr] = tree_decl.getPtr()

        for name, value in self.visitor.variables_info.items():
            self.vars[name] = tree_decl.getVar(name, value)

        fun_decl = function.VarDecl("var_", nVars=len(self.visitor.function_variables),
                                    nPtrs=len(self.visitor.function_pointers))

        for ptr in self.visitor.function_pointers:
            self.fun_vars[ptr] = fun_decl.getPtr()

        for name, value in self.visitor.function_variables.items():
            self.fun_vars[name] = fun_decl.getVar(name, value)

        return fun_decl

    @staticmethod
    def __binary_assignment_handler(node):
        if isinstance(node.lvalue, c_ast.StructRef):
            """ case of pointer assignment like: p->data = b + c """
            left_value = constants.STRUCT_VAR.format(node.lvalue.name.name, node.lvalue.type, node.lvalue.field.name)
        else:
            """ case of assignment like: p = * """
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
            left_value = self.fun_vars[node.lvalue.name.name]
            field = self.vars[node.lvalue.field.name]
        elif isinstance(node.lvalue, c_ast.UnaryOp):
            """ case of left value like: *root = * """
            is_left_ptr = True
            left_value = self.fun_vars[node.lvalue.expr.name]
        else:
            """ case of left value like: p = * """
            left_value = node.lvalue.name
            if left_value in self.visitor.function_pointers:
                is_left_ptr = True
            left_value = self.fun_vars[node.lvalue.name]

        if isinstance(node.rvalue, c_ast.StructRef):
            """ case of right value like: * = q->field """
            is_right_field = True
            right_value = self.fun_vars[node.rvalue.name.name]
            field = self.vars[node.rvalue.field.name]
        elif isinstance(node.rvalue, c_ast.Constant):
            """ case of assignment like: * = 1 """
            is_right_constant = True
            right_value = node.rvalue.value
        elif isinstance(node.rvalue, c_ast.UnaryOp):
            """ case of pointer assignment like: * = *root """
            is_right_ptr = True
            right_value = self.fun_vars[node.rvalue.expr.name]
        else:
            """ case of pointer assignment like: * = q """
            right_value = node.rvalue.name
            if right_value in self.visitor.function_pointers:
                is_right_ptr = True
            right_value = self.fun_vars[node.rvalue.name]

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

    def __unary_operation_handler(self, node):
        # TODO case of !p -> check on UnaryOp and case p -> other case
        
        if isinstance(node.cond.left, c_ast.UnaryOp):
            left_cond = self.fun_vars[node.cond.left.expr.name]
            right_cond = self.fun_vars[node.cond.right.name]
        elif isinstance(node.cond.right, c_ast.UnaryOp):
            left_cond = self.fun_vars[node.cond.left.name]
            right_cond = self.fun_vars[node.cond.right.expr.name]
        elif isinstance(node.cond.right, c_ast.Constant):
            left_cond = self.fun_vars[node.cond.left.name]
            right_cond = node.cond.right.value
        else:
            left_cond = self.fun_vars[node.cond.left.name]
            right_cond = self.fun_vars[node.cond.right.name]

        return left_cond, right_cond
