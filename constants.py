# variables declaration
TREE_DECL = "treeDecl = function.VarDecl(\"fld-\", nVars={}, nPtrs={})"
PTR_DECL = "treeDecl.getPtr(\"{}\")"
VAR_DECL = "treeDecl.getVar(\"{}\", {})"

INT = "z3.IntSort"
REAL = "z3.RealSort"
BOOL = "z3.BoolSort"

# functions variables
FUNCTION = "funDecl = function.VarDecl(\"var-\", nVars={}, nPtrs={})"
FUNCTION_CLOSE = "F = function.Function(funDecl, listing, succ)"
GET_VAR = "funDecl.getVar(\"{}\", {})"
GET_PTR = "funDecl.getPtr(\"{}\")"

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
