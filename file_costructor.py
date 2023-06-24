import statements
import conditions
import function
from pycparser import c_ast


class FileConstructor:
    def __init__(self, fun_visitor, visitor, fun_name):
        self.visitor = visitor
        self.fun_visitor = fun_visitor
        self.fun_name = fun_name
        self.inst = []
        self.succ = []
        self.fun_vars = {}
        self.vars = {}

    def build_file(self):
        fun_decl, tree_decl = self.write_file()
        heap_cond = statements.makeCondSort(fun_decl.getPtrIdSort())

        for line, instruction in self.visitor.stmts_bindings.items():
            if isinstance(instruction, c_ast.Assignment):
                if isinstance(instruction.rvalue, c_ast.BinaryOp):
                    """  case: cond1 = (p == NULL) """
                    if instruction.rvalue.op == "==":
                        self.inst.append(statements.HeapCondAssign(self.fun_vars[instruction.lvalue.name],
                                                                   conditions.EqNil(
                                                                       self.fun_vars[instruction.rvalue.left.name])))
                    elif instruction.rvalue.op == "!=":
                        """  case: cond1 = (p != NULL) """
                        self.inst.append(statements.HeapCondAssign(self.fun_vars[instruction.lvalue.name],
                                                                   conditions.NeqNil(
                                                                       self.fun_vars[instruction.rvalue.left.name])))
                    else:
                        exp = "{} {} {}".format(self.fun_vars[instruction.rvalue.left.name], instruction.rvalue.op,
                                                self.fun_vars[instruction.rvalue.right.name])
                        self.inst.append(statements.ExpAssign(self.fun_vars[instruction.lvalue.name], exp))
                else:
                    statement = self.__unary_assignment_handler(instruction)
                    self.inst.append(statement)

                if line in list(self.visitor.then_successors.keys()):
                    self.succ.append(self.visitor.then_successors[line])
                else:
                    self.succ.append(line + 1)

            elif isinstance(instruction, c_ast.While):
                cond = self.__conditions_handler(instruction, heap_cond)
                self.inst.append(statements.While(cond))
                self.succ.append(self.visitor.constructs_info[line])

            elif isinstance(instruction, c_ast.If):
                cond = self.__conditions_handler(instruction, heap_cond)
                self.inst.append(statements.If(cond))
                self.succ.append(self.visitor.constructs_info[line])

            elif isinstance(instruction, c_ast.UnaryOp):
                if instruction.op == "p++":
                    exp = "%s %s %d" % (self.fun_vars[instruction.expr.name], "+", 1)
                else:
                    exp = "%s %s %d" % (self.fun_vars[instruction.expr.name], "-", 1)

                self.inst.append(statements.ExpAssign(self.fun_vars[instruction.expr.name], exp))

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

        fun = function.Function(self.fun_name, fun_decl, self.inst, self.succ)

        return tree_decl, fun

    def write_file(self):
        vars_number = len(self.fun_visitor.variables_info)
        ptrs_number = len(self.fun_visitor.pointers_info)
        tree_decl = function.VarDecl("fld_", nVars=vars_number, nPtrs=ptrs_number)

        for ptr in self.fun_visitor.pointers_info:
            self.vars[ptr] = tree_decl.getPtr()

        for name, value in self.fun_visitor.variables_info.items():
            self.vars[name] = tree_decl.getVar(name, value)

        fun_decl = function.VarDecl("var_", nVars=len(self.visitor.function_variables),
                                    nPtrs=len(self.visitor.function_pointers))

        for ptr in self.visitor.function_pointers:
            self.fun_vars[ptr] = fun_decl.getPtr()

        for name, value in self.visitor.function_variables.items():
            self.fun_vars[name] = fun_decl.getVar(name, value)

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

    def __conditions_handler(self, node, heap_cond):
        cond = None
        if isinstance(node.cond, c_ast.ID):
            """ case: cond(a) """
            cond = self.fun_vars[node.cond.name]
        elif isinstance(node.cond, c_ast.BinaryOp):
            if isinstance(node.cond.right, c_ast.Constant):
                cond = "{} {} {}".format(self.fun_vars[node.cond.left.name], node.cond.op,
                                         node.cond.right.value)
            elif node.cond.left.name in self.visitor.function_pointers or node.cond.right.name in \
                    self.visitor.function_pointers:
                if node.cond.op == "==":
                    """ case: cond(p == q) """
                    cond = heap_cond.Eq(self.fun_vars[node.cond.left.name],
                                        self.fun_vars[node.cond.right.name])
                elif node.cond.op == "!=":
                    """ case: cond(p != q) """
                    cond = heap_cond.Neq(self.fun_vars[node.cond.left.name],
                                         self.fun_vars[node.cond.right.name])
            else:
                cond = "{} {} {}".format(self.fun_vars[node.cond.left.name], node.cond.op,
                                         self.fun_vars[node.cond.right.name])

        return cond
