import function
import statements
import conditions
from pycparser import c_ast


class StatementsHandler:
    def __init__(self, fun_visitor, visitor, fun_name):
        self.__visitor = visitor
        self.__fun_visitor = fun_visitor
        self.__fun_name = fun_name
        self.__instructions = []
        self.__successors = []
        self.__fun_vars = {}
        self.__vars = {}

    def build_statements(self):
        tree_decl, fun_decl = self.__variables_handler()

        for line, instruction in self.__visitor.stmts_bindings.items():
            if isinstance(instruction, c_ast.Assignment):
                if isinstance(instruction.rvalue, c_ast.BinaryOp):
                    """  case: cond1 = (p == NULL) """
                    if instruction.rvalue.op == "==":
                        self.__instructions.append(statements.HeapCondAssign(self.__fun_vars[instruction.lvalue.name],
                                                                             conditions.EqNil(
                                                                                 self.__fun_vars[
                                                                                     instruction.rvalue.left.name])))
                    elif instruction.rvalue.op == "!=":
                        """  case: cond1 = (p != NULL) """
                        self.__instructions.append(statements.HeapCondAssign(self.__fun_vars[instruction.lvalue.name],
                                                                             conditions.NeqNil(
                                                                                 self.__fun_vars[
                                                                                     instruction.rvalue.left.name])))
                    else:
                        exp = "{} {} {}".format(self.__fun_vars[instruction.rvalue.left.name], instruction.rvalue.op,
                                                self.__fun_vars[instruction.rvalue.right.name])
                        self.__instructions.append(statements.ExpAssign(self.__fun_vars[instruction.lvalue.name], exp))
                else:
                    statement = self.__unary_assignment_handler(instruction)
                    self.__instructions.append(statement)

                if line in list(self.__visitor.then_successors.keys()):
                    self.__successors.append(self.__visitor.then_successors[line])
                else:
                    self.__successors.append(line + 1)

            elif isinstance(instruction, c_ast.While):
                cond = self.__conditions_handler(instruction)
                self.__instructions.append(statements.While(cond))
                self.__successors.append(self.__visitor.constructs_info[line])

            elif isinstance(instruction, c_ast.If):
                cond = self.__conditions_handler(instruction)
                self.__instructions.append(statements.If(cond))
                self.__successors.append(self.__visitor.constructs_info[line])

            elif isinstance(instruction, c_ast.UnaryOp):
                if instruction.op == "p++":
                    exp = "%s %s %d" % (self.__fun_vars[instruction.expr.name], "+", 1)
                else:
                    exp = "%s %s %d" % (self.__fun_vars[instruction.expr.name], "-", 1)

                self.__instructions.append(statements.ExpAssign(self.__fun_vars[instruction.expr.name], exp))

                if line in list(self.__visitor.then_successors.keys()):
                    self.__successors.append(self.__visitor.then_successors[line])
                else:
                    self.__successors.append(line + 1)

            elif isinstance(instruction, c_ast.Return):
                try:
                    self.__instructions.append(self.__visitor.constructs_info[line])
                    self.__successors.append(list(self.__visitor.stmts_bindings)[-1])
                except KeyError:
                    self.__instructions.append(statements.Exit())
                    self.__successors.append(None)

        fun = function.Function(self.__fun_name, fun_decl, self.__instructions, self.__successors)

        return tree_decl, fun

    def __variables_handler(self):
        vars_number = len(self.__fun_visitor.variables_info)
        ptrs_number = len(self.__fun_visitor.pointers_info)
        tree_decl = function.VarDecl("fld_", nVars=vars_number, nPtrs=ptrs_number)

        for ptr in self.__fun_visitor.pointers_info:
            self.__vars[ptr] = tree_decl.getPtr()

        for name, value in self.__fun_visitor.variables_info.items():
            self.__vars[name] = tree_decl.getVar(name, value)

        fun_decl = function.VarDecl("var_", nVars=len(self.__visitor.function_variables),
                                    nPtrs=len(self.__visitor.function_pointers))

        for ptr in self.__visitor.function_pointers:
            self.__fun_vars[ptr] = fun_decl.getPtr()

        for name, value in self.__visitor.function_variables.items():
            self.__fun_vars[name] = fun_decl.getVar(name, value)

        return fun_decl, tree_decl

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
            left_value = self.__fun_vars[node.lvalue.name.name]
            field = self.__vars[node.lvalue.field.name]
        elif isinstance(node.lvalue, c_ast.UnaryOp):
            """ case of left value like: *root = * """
            is_left_ptr = True
            left_value = self.__fun_vars[node.lvalue.expr.name]
        else:
            """ case of left value like: p = * """
            left_value = node.lvalue.name
            if left_value in self.__visitor.function_pointers:
                is_left_ptr = True
            left_value = self.__fun_vars[node.lvalue.name]

        if isinstance(node.rvalue, c_ast.StructRef):
            """ case of right value like: * = q->field """
            is_right_field = True
            right_value = self.__fun_vars[node.rvalue.name.name]
            field = self.__vars[node.rvalue.field.name]
        elif isinstance(node.rvalue, c_ast.Constant):
            """ case of assignment like: * = 1 """
            is_right_constant = True
            right_value = node.rvalue.value
        elif isinstance(node.rvalue, c_ast.UnaryOp):
            """ case of pointer assignment like: * = *root """
            is_right_ptr = True
            right_value = self.__fun_vars[node.rvalue.expr.name]
        else:
            """ case of pointer assignment like: * = q """
            right_value = node.rvalue.name
            if right_value in self.__visitor.function_pointers:
                is_right_ptr = True
            right_value = self.__fun_vars[node.rvalue.name]

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

    def __conditions_handler(self, node):
        cond = None
        if isinstance(node.cond, c_ast.ID):
            """ case: cond(a) """
            cond = self.__fun_vars[node.cond.name]
        elif isinstance(node.cond, c_ast.BinaryOp):
            if isinstance(node.cond.left, c_ast.UnaryOp):
                left = node.cond.left.expr.name
            if isinstance(node.cond.right, c_ast.UnaryOp):
                right = node.cond.right.expr.name
            if isinstance(node.cond.left, c_ast.ID):
                left = node.cond.left.name
            if isinstance(node.cond.right, c_ast.ID):
                right = node.cond.right.name

            if isinstance(node.cond.right, c_ast.Constant):
                cond = "{} {} {}".format(self.__fun_vars[node.cond.left.name], node.cond.op,
                                         node.cond.right.value)
            elif left in self.__visitor.function_pointers or right in self.__visitor.function_pointers:
                if node.cond.op == "==":
                    """ case: cond(p == q) """
                    cond = conditions.Eq(self.__fun_vars[left],
                                         self.__fun_vars[right])
                elif node.cond.op == "!=":
                    """ case: cond(p != q) """
                    cond = conditions.Neq(self.__fun_vars[left],
                                          self.__fun_vars[right])
            else:
                cond = "{} {} {}".format(self.__fun_vars[left], node.cond.op,
                                         self.__fun_vars[right])

        return cond
