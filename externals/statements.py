import sys
import z3

from externals import conditions


def makeCondSort(PtrIdSort):
    """The type of a Boolean condition involving pointers."""
    HeapCondSort = z3.Datatype('HeapCond')
    HeapCondSort.declare('Neq', ('APtrId', PtrIdSort), ('BPtrId', PtrIdSort))
    HeapCondSort.declare('Eq', ('APtrId', PtrIdSort), ('BPtrId', PtrIdSort))
    HeapCondSort.declare('EqNil', ('PtrId', PtrIdSort))
    HeapCondSort.declare('NeqNil', ('PtrId', PtrIdSort))
    HeapCondSort = HeapCondSort.create()
    return HeapCondSort


class Stmt:
    """The superclass of all statements (currently unused)."""
    pass


class Skip(Stmt):
    def step(self):
        return True


class ExpAssign(Stmt):
    """datavar := expression
       Where datavar is a local data variable
    """
    def __init__(self, datavar, exp):
        self.dstVarId = datavar
        self.exp = exp


class HeapCondAssign(Stmt):
    """datavar := heap_condition
       Where datavar is a local boolean variable
    """
    def __init__(self, datavar, heap_cond):
        self.dstVarId = datavar
        self.heap_cond = heap_cond


class Exit(Stmt):
    """Exit"""
    def step(self):
        return True

class NilAssign(Stmt):
    """p := nil"""
    def __init__(self, p):
        self.dstPtrId = p

class PtrAssign(Stmt):
    """p := q"""
    def __init__(self, p, q):
        self.dstPtrId = p
        self.srcPtrId = q

class ToPtrFieldAssign(Stmt):
    """p->pfield := q"""
    def __init__(self, p, pField, q):
        self.dstPtrId = p
        self.ptrFieldId = pField
        self.srcPtrId = q

class FromPtrFieldAssign(Stmt):
    """p := q->pfield"""
    def __init__(self, p, q, pField):
        self.dstPtrId = p
        self.ptrFieldId = pField
        self.srcPtrId = q

class FromDataFieldAssign(Stmt):
    """d := p->datafield"""
    def __init__(self, dstVarId, srcPtrId, dataFieldId):
        self.dstVarId = dstVarId
        self.srcPtrId = srcPtrId
        self.dataFieldId = dataFieldId

class ToDataFieldAssign(Stmt):
    """p->datafield := d"""
    def __init__(self, dstPtrId, dataFieldId, srcVarId):
        self.dstPtrId = dstPtrId
        self.dataFieldId = dataFieldId
        self.srcVarId = srcVarId

class New(Stmt):
    """new p"""
    def __init__(self, p):
        self.dstPtrId = p


class Free(Stmt):
    """new p"""
    def __init__(self, p):
        self.dstPtrId = p
        raise Exception("This statement is unsupported.")


class While(Stmt):
    """while (cond) {...}"""
    def __init__(self, cond):
        self.cond = cond
        self.isHeapCond = isinstance(cond, conditions.Cond)

class If(Stmt):
    """if (cond) {...} else {...}"""
    def __init__(self, cond):
        self.cond = cond
        self.isHeapCond = isinstance(cond, conditions.Cond)


class Error(Stmt):
    """A special instruction that raises Err."""
    pass



import inspect
classes = [cls for name, cls in inspect.getmembers(sys.modules[__name__], inspect.isclass)]
