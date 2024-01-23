class Cond:
    """The superclass of all heap conditions (currently unused)."""
    pass


class Eq(Cond):
    """p == q
    """
    def __init__(self, ptr1, ptr2):
        self.ptr1 = ptr1
        self.ptr2 = ptr2


class Neq(Cond):
    """p != q
    """
    def __init__(self, ptr1, ptr2):
        self.ptr1 = ptr1
        self.ptr2 = ptr2


class EqNil(Cond):
    """p == NIL
    """
    def __init__(self, ptr):
        self.ptr = ptr


class NeqNil(Cond):
    """p != NIL
    """
    def __init__(self, ptr):
        self.ptr = ptr


