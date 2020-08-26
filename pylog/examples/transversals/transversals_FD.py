from __future__ import annotations

from random import randint, sample
from typing import List, Set, Union

from control_structures import Trace
from logic_variables import euc


class All_Different:

    # sibs_dict = {FD_Var_x: {FD_Var_i that must be different from FD_Var_x}}
    # Aggregated from the All_Different declarations
    sibs_dict = {}

    def __init__(self, vars: Set[FD_Var]):
        self.vars = vars
        for v in vars:
            All_Different.sibs_dict[v] = All_Different.sibs_dict.setdefault(v, set()) | (vars - {v})

    @staticmethod
    def all_satisfied():
        return all(All_Different.satisfied_for_var(v) for v in All_Different.sibs_dict)

    @staticmethod
    def satisfied_for_var(v: FD_Var):
        if not v.is_instantiated(): return True
        return all(v.value() != w.value() for w in All_Different.sibs_dict[v])

    @staticmethod
    def to_string_sibs_dict():
        return '{' + ", ".join([All_Different.to_string_sibs_entry(v) for v in All_Different.sibs_dict]) + '}'

    @staticmethod
    def to_string_sibs_entry(v):
        entry = f'{v.name}: ' + '{' + ", ".join(v.name for v in All_Different.sibs_dict[v]) + '}'
        return entry


class FD_Var:
    """ A Finite Domain variable """
    id = 0

    propagate = False
    smallest_first = False

    def __init__(self, init_range=None, name=None):
        FD_Var.id += 1
        self.id = FD_Var.id
        self.name = name if name is not None else f'V{str(self.id)}'
        self.range = set() if init_range is None else init_range
        self.range_was_set_stack = []
        self.was_set = False
        self.unification_chain_next = None

    def __eq__(self, other: FD_Var):
        return self.id == other.id

    def __hash__(self):
        return hash(self.id)

    def __str__(self):
        name_part = '' if self.name is None else self.name + ('*' if self.was_set else '') + ': '
        (left, right) = ("{", "}")
        return f'{name_part}{left}{", ".join([str(x) for x in self.range])}{right}'

    def is_instantiated(self):
        return len(self.range) == 1

    def member_FD(self, a_list: List[Union[FD_Var, int, str]]):
        """ Is v in a_list?  """
        # If a_list is empty, it can't have a member. So fail.
        if not a_list: return

        yield from self.set_value(a_list[0])
        yield from self.member_FD(a_list[1:])

    def propagate_value(self, value):
        for v in All_Different.sibs_dict[self]:
            v.update_range(v.range - {value})

    def set_value(self, new_value: Union[float, int, str]):
        self.update_range({new_value}, True)
        if FD_Var.propagate:
            self.propagate_value(new_value)
        yield
        self.undo_update_range()
        if FD_Var.propagate:
            self.undo_propagate_value()

    def undo_propagate_value(self):
        for v in All_Different.sibs_dict[self]:
            v.undo_update_range()

    def undo_update_range(self):
        (self.range, self.was_set) = self.range_was_set_stack[-1]
        self.range_was_set_stack = self.range_was_set_stack[:-1]

    def update_range(self, new_range, was_set=False):
        self.range_was_set_stack = self.range_was_set_stack + [(self.range, self.was_set)]
        self.range = new_range
        self.was_set = self.was_set or was_set

    def value(self):
        return list(self.range)[0] if self.is_instantiated() else None


@Trace
def FD_solver(vars: Set[FD_Var]):
    if any(not v.range for v in vars): return
    elif not All_Different.all_satisfied(): return
    elif all(v.is_instantiated() for v in vars): yield
    else:
        not_set_vars: Set[FD_Var] = {v for v in vars if not v.was_set}
        nxt_var = min(not_set_vars, key=lambda v: len(v.range)) if FD_Var.smallest_first else \
                  not_set_vars.pop()
        for _ in nxt_var.member_FD(list(nxt_var.range)):
            yield from FD_solver(vars)


def gen_sets(nbr_sets=5):
    sets_size_low = 2
    sets_size_high = nbr_sets
    vals_size = nbr_sets
    (vals_range_start_min, vals_range_start_max) = (ord('a'), ord('z') + 1 - vals_size)
    alpha_low = randint(vals_range_start_min, vals_range_start_max)
    vals = [chr(alpha_low + k) for k in range(vals_size)]
    sets = [{k for k in sample(vals, randint(sets_size_low, sets_size_high))}
            for _ in range(nbr_sets)]
    return sets


if __name__ == '__main__':
    print()
    sets = gen_sets()
    for FD_Var.propagate in [False, True]:
        for FD_Var.smallest_first in [False, True]:
            FD_Var.id = 0
            All_Different.sibs_dict = {}
            # Create an FV_Var for each set
            vars = {FD_Var(set) for set in sets}
            All_Different(vars)
            print(Trace.to_str(vars))
            Trace.line_no = 0
            Trace.trace = True
            solutions = 0
            print(f'{"~" * 90}')
            print(f'propagate: {FD_Var.propagate}; smallest_first: {FD_Var.smallest_first};')
            for _ in FD_solver(vars):
                solutions += 1
                if Trace.trace:  print()
                print(f"{solutions}. {Trace.to_str(vars)}")
                if Trace.trace:  print()
            print(f'propagate: {FD_Var.propagate}; smallest_first: {FD_Var.smallest_first}; '
                  f'solutions: {solutions}; lines: {Trace.line_no}')
            print(f'{"~" * 90}\n')


##    ################################### Not currently used ###################################    ##

def ensure_is_FD_Var(x: Union[FD_Var, int, str]) -> FD_Var:
    """
      Applied to each argument in a Structure.
      Applies PyValue to those that are not already Terms.
      If x is not a logic variable, i.e., an instance of Term, it must be a Python value.
      Wrap it in PyValue. (It must be immutable.)
    """
    return x if isinstance(x, FD_Var) else FD_Var({x})


def flatten_sets_to_set(sets):
    return {elt for set in sets for elt in set}


@euc
def unify_FD(left: FD_Var, right: FD_Var):
    """
    Unify two FD_Vars or constants.

    The strategy is to keep track of the "unification unification_chain" for all variables.

    The unification unification_chain is a linked list of logic variables, which are all unified.

    The final element on the unification_chain is either
    o a non-Var, in which case the value of all preceding variables is the value of that non-Var, or
    o a Var (which is not linked to any further element), in which case, all variables on the unification_chain
      are unified but do not (yet) have a value.
    """

    # Make sure both Left and other are logic variables. This allows us to call, e.g, unify(X, 'abc').
    # ensure_is_logic_variable will wrap 'abc' in a PyValue.
    (left, right) = map(ensure_is_FD_Var, (left, right))
    range_intersection = left.range & right.range
    if not range_intersection: return

    left.unification_chain_next = left.unification_chain_next = FD_Var(range_intersection)
    yield
    left.unification_chain_next = left.unification_chain_next = None

    # if self.value() is not None and self.value() == other.value():
    #     yield
    #
    # # The rest consists of special cases: both PyValues, both Structures, at least one Var.
    #
    # # Case 1. Both are PyValues, and exactly one is instantiated.
    # # "Assign" it's value to the other. This is similar to (but simpler than)
    # # how we handle two Var's. But instead of building a unification_chain, we "assign"
    # # one value to the other.
    # elif isinstance(Left, PyValue) and isinstance(other, PyValue) and \
    #     (not Left.is_instantiated() or not other.is_instantiated()) and \
    #     (Left.is_instantiated() or other.is_instantiated()):
    #     (assignedTo, assignedFrom) = (Left, other) if other.is_instantiated() else (other, Left)
    #     assignedTo._set_py_value(assignedFrom.get_py_value())
    #     yield
    #     # See discussion in unify below for why we do this.
    #     assignedTo._set_py_value(None)
    #     #
    #     # # If they are both PyValues, treat specially.
    #     # yield from unify_PyValues(Left, other)
    #
    #     # # Case 2. Both  Structures. They can be unified if
    #     # # (a) they have the same functor and
    #     # # (b) their arguments can be unified.
    #     # elif isinstance(Left, Structure) and isinstance(other, Structure) and Left.functor == other.functor:
    #     #     yield from unify_sequences(Left.args, other.args)
    #     #
    #     # # Case 3. At least one is a Var. Since we use @euc, it's the end of its unification_chain.
    #     # # Make the other an extension of its unification_chain.
    #     # # (If both are Vars, it makes no functional difference which extends which.)
    #     # elif isinstance(Left, Var) or isinstance(other, Var):
    #     #     (pointsFrom, pointsTo) = (Left, other) if isinstance(Left, Var) else (other, Left)
    #     #     pointsFrom.unification_chain_next = pointsTo
    #     #     yield
    #
    #     # All yields create a context in which more of the program is executed--like
    #     # the body of a while-loop or a for-loop. A "next()" request asks for alternatives.
    #     # But there is only one functional way to do unification. So on "backup," unlink the
    #     # two and exit without a further yield, i.e., fail.
    #
    #     # This is fundamental! It's what makes it possible for a Var to become un-unified outside
    #     # the context in which it was unified, e.g., unifying a Var with (successive) members
    #     # of a list. The first successful unification must be undone before the second can occur.
    #     pointsFrom.unification_chain_next = None
