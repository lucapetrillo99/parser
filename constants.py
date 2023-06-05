# variables declaration

DATA_DECL = "DataFieldSort"
PTR_DECL = "PtrFieldSort"
INT = "z3.IntSort()"
REAL = "z3.RealSort()"
BOOL = "z3.BoolSort()"

# functions variables

FUNCTION = "Function()"
GET_PTR = "F.getPtr()"
GET_INT = "F.getVar(z3.IntSort)"
GET_REAL = "F.getVar(z3.RealSort)"
GET_BOOL = "F.getVar(z3.BoolSort)"

# functions instructions

EXPRESSION = "{} {} {}"
STRUCT_VAR = "{} {} {}"
LISTING = "listing[{0}]"
SUCCESSOR = "succ[{}]"
BIN_EXPR_ASSIGN = "PL.ExpAssign({}, exp)"
PTR_ASSIGN = "PL.PtrAssign({}, {})"
EQ_HEAP_COND = "HeapCond.Eq({}, {})"
NEQ_HEAP_COND = "HeapCond.Neq({}, {})"
WHILE_COND = "PL.While(cond)"
IF_COND = "PL.If(cond)"
SKIP = "PL.Skip()"
EXIT_COND = "PL.Exit()"

# program output directory

OUT_DIR = "out/"
