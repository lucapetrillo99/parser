import statements
import conditions


def print_result(tree_decl, fun_decl, f_cons):
    __print_vars(tree_decl, fun_decl, f_cons)
    __print_statements(f_cons)


def __print_vars(tree_decl, fun_decl, f_cons):
    print("TreeDecl => nVars: {}, nPtrs: {}".format(tree_decl.nVars, tree_decl.nPtrs))
    for name, var in f_cons.vars.items():
        print("tree => {}: {}".format(name, var))

    print("\n")

    print("FunDecl => nVars: {}, nPtrs: {}".format(fun_decl.decl.nVars, fun_decl.decl.nPtrs))
    for name, var in f_cons.fun_vars.items():
        print("fun => {}: {}".format(name, var))

    print("\n")


def __print_statements(f_cons):
    for i, (inst, succ) in enumerate(zip(f_cons.instructions, f_cons.successors)):
        if isinstance(inst, statements.Skip):
            print("listing[{}] => Skip: {}".format(i, inst.step()))
            print("succ[{}] = {}".format(i, succ))

        if isinstance(inst, statements.ExpAssign):
            print("listing[{}] => ExpAssign: {} = {}".format(i, inst.dstVarId, inst.exp))
            print("succ[{}] = {}".format(i, succ))

        if isinstance(inst, statements.HeapCondAssign):
            if isinstance(inst.heap_cond, conditions.NeqNil):
                print("listing[{}] => HeapCondAssign: {} = {} != NULL".format(i, inst.dstVarId, inst.heap_cond.ptr1))
            elif isinstance(inst.heap_cond, conditions.EqNil):
                print("listing[{}] => HeapCondAssign: {} = {} == NULL".format(i, inst.dstVarId, inst.heap_cond.ptr1))
            else:
                print("listing[{}] => HeapCondAssign: {} = {}".format(i, inst.dstVarId, inst.heap_cond))

            print("succ[{}] = {}".format(i, succ))

        if isinstance(inst, statements.Exit):
            print("listing[{}] => Exit: {}".format(i, inst.step()))
            print("succ[{}] = {}".format(i, succ))

        if isinstance(inst, statements.NilAssign):
            print("listing[{}] => NilAssign: {}".format(i, inst.dstPtrId))
            print("succ[{}] = {}".format(i, succ))

        if isinstance(inst, statements.PtrAssign):
            print("listing[{}] => PtrAssign: {} = {}".format(i, inst.dstPtrId, inst.srcPtrId))
            print("succ[{}] = {}".format(i, succ))

        if isinstance(inst, statements.ToPtrFieldAssign):
            print("listing[{}] => ToPtrFieldAssign: {} -> {} = {}".format(i, inst.dstPtrId, inst.ptrFieldId,
                                                                          inst.srcPtrId))
            print("succ[{}] = {}".format(i, succ))

        if isinstance(inst, statements.FromPtrFieldAssign):
            print("listing[{}] => FromPtrFieldAssign: {} = {} -> {}".format(i, inst.dstPtrId, inst.srcPtrId,
                                                                            inst.ptrFieldId))
            print("succ[{}] = {}".format(i, succ))

        if isinstance(inst, statements.FromDataFieldAssign):
            print("listing[{}] => FromDataFieldAssign: {} = {} -> {}".format(i, inst.dstVarId, inst.srcPtrId,
                                                                             inst.dataFieldId))
            print("succ[{}] = {}".format(i, succ))

        if isinstance(inst, statements.ToDataFieldAssign):
            print("listing[{}] => ToDataFieldAssign: {} -> {} = {}".format(i, inst.dstPtrId, inst.dataFieldId,
                                                                           inst.srcVarId))
            print("succ[{}] = {}".format(i, succ))

        if isinstance(inst, statements.While):
            if isinstance(inst.cond, conditions.Eq):
                print("listing[{}] => While: Eq = {}, {}".format(i, inst.cond.ptr1, inst.cond.ptr2))
            elif isinstance(inst.cond, conditions.Neq):
                print("listing[{}] => While: Neq = {}, {}".format(i, inst.cond.ptr1, inst.cond.ptr2))
            else:
                print("listing[{}] => While: {}".format(i, inst.cond))
            print("succ[{}] = {}".format(i, succ))

        if isinstance(inst, statements.If):
            if isinstance(inst.cond, conditions.Eq):
                print("listing[{}] => If: Eq = {}, {}".format(i, inst.cond.ptr1, inst.cond.ptr2))
            elif isinstance(inst.cond, conditions.Neq):
                print("listing[{}] => If: Neq = {}, {}".format(i, inst.cond.ptr1, inst.cond.ptr2))
            else:
                print("listing[{}] => If: {}".format(i, inst.cond))
            print("succ[{}] = {}".format(i, succ))
