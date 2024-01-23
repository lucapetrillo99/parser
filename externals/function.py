import math
import z3
from z3 import BitVecVal

from externals import conditions
from externals import statements

class VarDecl:
    """A collection of variables of different types.
    Used both for node data fields and for local data variables. """

    # Pointer variables are numbered 0...n and the id is encoded in unary (one-hot)

    def __init__(self, varNamePrefix, nVars, nPtrs):
        """Creates a VariableDeclaration object supporting nVars data variables and nPtrs pointers."""
        self.varNamePrefix = varNamePrefix
        self.nVars = nVars
        self.nPtrs = nPtrs
        self.varCounter = 0
        self.ptrCounter = 0
        self.idBits = math.ceil(math.log(nVars + 1, 2))
        self.types = {}
        self.varToName = {}
        self.ptrToIndex = {}
        self.ptrIndexBits = math.floor(math.log(self.nPtrs + 1, 2))

    def getVar(self, name, type):
        if self.varCounter >= self.nVars:
            raise ValueError("You asked for more variables than anticipated.")
        qualified_name = self.varNamePrefix + name
        self.types[qualified_name] = type
        self.varCounter += 1
        result = z3.Const(name, type)
        self.varToName[result] = qualified_name
        return result

    def allVars(self):
        return list(self.varToName.keys())

    def allPtrIds(self):
        """Generator for pointer ids"""
        return self.ptrToIndex.keys()

    def getVarIdSort(self):
        return z3.BitVecSort(self.idBits)

    def getListOfTypes(self):
        return list(self.types.items())

    def getPtrIndexSort(self):
        return z3.BitVecSort(self.ptrIndexBits)

    def getPtr(self):
        if self.ptrCounter >= self.nPtrs:
            raise ValueError("You asked for more pointer variables than anticipated.")
        id = z3.BitVecVal(1, self.nPtrs) << self.ptrCounter
        self.ptrToIndex[id] = z3.BitVecVal(self.ptrCounter, self.ptrIndexBits)
        self.ptrCounter += 1
        return id

    def getIndexOfPtr(self, ptrId_symb):
        formula = None
        # print(f"{self.ptrToIndex}, {ptrId_symb}")
        for ptrId in self.allPtrIds():
            if formula is None:
                formula = self.ptrToIndex[ptrId]
            else:
                formula = z3.If(ptrId_symb == ptrId, self.ptrToIndex[ptrId], formula)
        return formula

    def getPtrIdSort(self):
        return z3.BitVecSort(self.nPtrs)

    def getAllPtrsExcept(self, ptrId):
        return ~ptrId

    def getSetOfPtrIdSort(self):
        # Since the encoding of pointers is one-hot, a set of pointers
        # has the same type as a pointer id
        return z3.BitVecSort(self.nPtrs)

    def getSetOfPtrs(self, ptrIds):
        mask = z3.BitVecVal(0, self.nPtrs)
        for ptrId in ptrIds:
            mask = mask | ptrId
        return mask


class Function:

    # Pointer 0 is the special root pointer (p-hat in the paper)

    def __init__(self, name: str, funDecl: VarDecl, listing, successorRelation):
        assert len(listing) == len(successorRelation)
        self.name = name
        self.decl = funDecl
        self.listing = listing
        self.PCsByType = {}
        self.successor = successorRelation
        self.PCBits = math.ceil(math.log(len(self.listing), 2))
        # print(f"{len(listing)}: {self.PCBits} bits")
        for cls in statements.classes:
            self.PCsByType[cls] = []
        for i in range(len(listing)):
            t = type(listing[i])
            self.PCsByType[t].append(i)
        self.data_cond_stmts = list(filter(lambda i:
                                           not self.listing[i].isHeapCond,
                                           self.PCsByType[statements.If] + self.PCsByType[statements.While]))
        self.heap_cond_stmts = list(filter(lambda i:
                                           self.listing[i].isHeapCond,
                                           self.PCsByType[statements.If] + self.PCsByType[statements.While]))
        self.eq_nil_cond_stmts = list(filter(
            lambda i:
            (self.listing[i].isHeapCond and
             type(self.listing[i].cond) in (conditions.NeqNil, conditions.EqNil)),
            self.PCsByType[statements.If] + self.PCsByType[statements.While]))
        self.cmp_ptrs_cond_stmts = list(filter(
            lambda i:
            (self.listing[i].isHeapCond and
             type(self.listing[i].cond) in (conditions.Eq, conditions.Neq)),
            self.PCsByType[statements.If] + self.PCsByType[statements.While]))


    def getDstPtrId(self, symbolicPC):
        """Returns a Z3 function that accepts a symbolic PC of an instruction with the dstPtrId
        parameter, and returns the value of that parameter."""
        # List of PCs with a dstPtrId argument (to be completed)
        stmts = self.PCsByType[statements.NilAssign] + \
                self.PCsByType[statements.PtrAssign] + \
                self.PCsByType[statements.New] + \
                self.PCsByType[statements.FromPtrFieldAssign] + \
                self.PCsByType[statements.ToPtrFieldAssign] + \
                self.PCsByType[statements.ToDataFieldAssign]
        if len(stmts) == 0:
            return None
        # print(stmts)
        formula = self.listing[stmts[0]].dstPtrId
        for i in range(1, len(stmts)):
            pc = stmts[i]
            cond = symbolicPC == pc
            dstPtrId = self.listing[pc].dstPtrId
            # print(f"{i}: {self.listing[i]} \t {dstPtrId}")
            formula = z3.If(cond, dstPtrId, formula)
        # print(formula)
        return formula


    def getSrcPtrId(self, symbolicPC):
        # List of PCs with a srcPtrId argument (to be completed)
        stmts = self.PCsByType[statements.PtrAssign] + \
                self.PCsByType[statements.ToPtrFieldAssign] + \
                self.PCsByType[statements.FromPtrFieldAssign] + \
                self.PCsByType[statements.FromDataFieldAssign]
        if len(stmts) == 0:
            return None
        # print(stmts)
        formula = self.listing[stmts[0]].srcPtrId
        for i in range(1, len(stmts)):
            pc = stmts[i]
            cond = symbolicPC == pc
            srcPtrId = self.listing[pc].srcPtrId
            formula = z3.If(cond, srcPtrId, formula)
        return formula


    def getPtrFldId(self, symbolicPC):
        stmts = self.PCsByType[statements.ToPtrFieldAssign] + \
                self.PCsByType[statements.FromPtrFieldAssign]
        if len(stmts) == 0:
            return None
        formula = self.listing[stmts[0]].ptrFieldId
        for i in range(1, len(stmts)):
            pc = stmts[i]
            cond = symbolicPC == pc
            srcPtrId = self.listing[pc].ptrFieldId
            formula = z3.If(cond, srcPtrId, formula)
        return formula


    def meta_attribute_get(self, symbolicPC, statement_type_list, attribute_name):
        stmts = []
        for statement_type in statement_type_list:
            stmts = stmts + self.PCsByType[statement_type]
        if len(stmts) == 0:
            return None
        formula = getattr(self.listing[stmts[0]], attribute_name)
        for i in range(1, len(stmts)):
            pc = stmts[i]
            cond = symbolicPC == pc
            the_attribute = getattr(self.listing[pc], attribute_name)
            formula = z3.If(cond, the_attribute, formula)
        return formula


    def getDataFldId(self, symbolicPC):
        return self.meta_attribute_get(symbolicPC,
                                       [statements.ToDataFieldAssign, statements.FromDataFieldAssign],
                                       "dataFieldId")


    def is_heap_cond(self, symbolicPC):
        return z3.Or(*[symbolicPC == BitVecVal(pc, self.PCBits) for pc in self.heap_cond_stmts])

    def assgn_exp(self, frame1, frame2):
        """local_var := expression"""
        symbolicPC = frame1.pc()
        stmts = self.PCsByType[statements.ExpAssign]
        if len(stmts) == 0:
            return False
        formula = None
        for i in range(len(stmts)):
            pc = stmts[i]
            cond = symbolicPC == pc
            dstVar = self.listing[pc].dstVarId
            expr = self.listing[pc].exp
            dstVarName = self.decl.varToName[dstVar]
            frameField = getattr(self.FrameSort, dstVarName)
            # frame1.var = expr
            # Note that the binding of values to the variables in expr is
            # handled *outside* of this function, by the set_var_values function.
            assignment = (frameField(frame2.frame) == expr)
            # Other variables keep their value from frame1 to frame2
            otherNames = [varname for (varname, _) in self.decl.getListOfTypes()]
            otherNames.remove(dstVarName)
            other_vars_keep_value = z3.And(
                *[frame1.dataValue(varname) == frame2.dataValue(varname)
                  for varname in otherNames])
            if formula is None:
                formula = z3.And(assignment, other_vars_keep_value)
            else:
                formula = z3.If(cond,
                                z3.And(assignment, other_vars_keep_value),
                                formula)
        return z3.And(self.set_var_values(frame1), formula)


    def assgn_var_to_fld(self, frame1, frame2):
        """p->data := local_var"""
        symbolicPC = frame1.pc()
        stmts = self.PCsByType[statements.ToDataFieldAssign]
        if len(stmts) == 0:
            return False
        formula = None
        for i in range(len(stmts)):
            pc = stmts[i]
            dstFld = self.listing[pc].dataFieldId
            srcVar = self.listing[pc].srcVarId
            dstFldName = self.TreeDecl.varToName[dstFld]
            srcVarName = self.decl.varToName[srcVar]
            assignment = z3.And(frame2.dataValue(dstFldName) == frame1.dataValue(srcVarName),
                                default_val_except(frame1, frame2, dstFldName))
            if formula is None:
                formula = assignment
            else:
                cond = symbolicPC == pc
                formula = z3.If(cond, assignment, formula)
        return formula


    def assgn_fld_to_var(self, frame1, frame2):
        """local_var := p->data"""
        symbolicPC = frame1.pc()
        stmts = self.PCsByType[statements.FromDataFieldAssign]
        if len(stmts) == 0:
            return False
        formula = None
        for i in range(len(stmts)):
            pc = stmts[i]
            srcFld = self.listing[pc].dataFieldId
            dstVar = self.listing[pc].dstVarId
            srcFldName = self.TreeDecl.varToName[srcFld]
            dstVarName = self.decl.varToName[dstVar]
            assignment = z3.And(frame2.dataValue(dstVarName) == frame1.dataValue(srcFldName),
                                default_d_except(frame1, frame2, dstVarName))
            if formula is None:
                formula = assignment
            else:
                cond = symbolicPC == pc
                formula = z3.If(cond, assignment, formula)
        return formula

    def heap_cond_switcher(self, symbolicPC, switch_table):
        if not self.cmp_ptrs_cond_stmts:
            return False
        formula = None
        for pc in self.cmp_ptrs_cond_stmts:
            stmt = self.listing[pc]
            if formula is None:
                formula = switch_table[type(stmt.cond)](stmt.cond)
            else:
                formula = z3.If(symbolicPC == pc,
                                switch_table[type(stmt.cond)](stmt.cond),
                                formula)
        return formula

    def get_eq_nil_cond(self, f1, f2):
        if not self.eq_nil_cond_stmts:
            return False
        pc1 = f1.pc()
        pc2 = f2.pc()
        formulas = []
        for pc in self.eq_nil_cond_stmts:
            stmt = self.listing[pc]
            if type(stmt.cond) == conditions.EqNil:
                cond = f1.isNil(stmt.cond.ptr)
            else:
                cond = z3.Not(f1.isNil(stmt.cond.ptr))
            formulas.append(z3.And(pc1 == BitVecVal(pc, self.PCBits),
                                   z3.If(cond,
                                         pc2 == BitVecVal(self.successor[pc][0], self.PCBits),
                                         pc2 == BitVecVal(self.successor[pc][1], self.PCBits))))
        return z3.Or(*formulas)

    def prog(self, pc: int):
        """Returns the instruction indexed by pc."""
        result = self.listing[-1]  # The last instruction
        for i in range(len(self.listing) - 2, -1, -1):
            result = z3.If(pc == i, self.listing[i], result)
        # print("DEBUG!!!" + result.sexpr())
        return result

    def succ(self, pc: int, condValue=True):
        if type(self.successor[pc]) == int:
            return self.successor[pc]
        else:
            return self.successor[pc][0 if condValue else 1]

    def advance_pc(self, pc1, pc2):
        """Advance pc unconditionally. Only for statements with a single successor."""
        formulas = []
        for pc in range(len(self.successor)):
            pcbv = BitVecVal(pc, self.PCBits)
            if type(self.listing[pc]) in [statements.Exit, statements.Error]:
                continue
            if type(self.successor[pc]) == int:
                # Unconditional statement
                formulas.append(z3.And(pc1 == pcbv,
                                       pc2 == BitVecVal(self.successor[pc], self.PCBits)))
        formula = z3.Or(*formulas)
        # print(f'advance_pc:\n{formula}')
        return formula


    def advance_pc_on_heap_condition(self, pc1, pc2, symbolicCond):
        if len(self.heap_cond_stmts) == 0:
            return False
        formulas = []
        for pc in self.heap_cond_stmts:
            assert type(self.successor[pc]) == tuple and len(self.successor[pc]) == 2
            pcbv = BitVecVal(pc, self.PCBits)
            # Conditional statement
            formulas.append(z3.And(pc1 == pcbv,
                                   z3.If(symbolicCond,
                                         pc2 == BitVecVal(self.successor[pc][0], self.PCBits),
                                         pc2 == BitVecVal(self.successor[pc][1], self.PCBits))))
        formula = z3.Or(*formulas)
        print(f'advance_pc_on_heap_cond (cond={symbolicCond}):\n{formula}')
        return formula


    def advance_pc_on_data_condition(self, pc1, pc2):
        if len(self.data_cond_stmts) == 0:
            return False
        formulas = []
        for pc in self.data_cond_stmts:
            assert type(self.successor[pc]) == tuple and len(self.successor[pc]) == 2
            pcbv = BitVecVal(pc, self.PCBits)
            stmt = self.listing[pc]
            symbolicCond = stmt.cond
            formulas.append(z3.And(pc1 == pcbv,
                                   z3.If(symbolicCond,
                                         pc2 == BitVecVal(self.successor[pc][0], self.PCBits),
                                         pc2 == BitVecVal(self.successor[pc][1], self.PCBits))))
        formula = z3.Or(*formulas)
        # print(f'advance_pc_on_data_cond:\n{formula}')
        return formula



    def set_var_values(self, frame):
        """Returns the predicate that sets the value of all data variables
        to the values specified in the given frame."""
        list = [z3var == frame.dataValue(name)
                for (z3var, name) in self.decl.varToName.items()]
        # print(list)
        return z3.And(*list)
