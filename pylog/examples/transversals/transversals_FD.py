from __future__ import annotations

from random import randint, sample
from typing import List, Set, Union

from control_structures import Trace
from logic_variables import euc

nbr_sets = 5

sets_size_low = 2
sets_size_high = nbr_sets

vals_size = nbr_sets
(vals_range_start_min, vals_range_start_max) = (ord('a'), ord('z') + 1 - vals_size)

alpha_low = randint(vals_range_start_min, vals_range_start_max)
set_vals = [chr(alpha_low + k) for k in range(vals_size)]
sets = [{k for k in sample(set_vals, randint(sets_size_low, sets_size_high))}
        for _ in range(nbr_sets)]


class All_Different:

    # sibs_dict = {FD_Var_x: {FD_Var_i that must be different from FD_Var_x}}
    sibs_dict = {}

    def __init__(self, vars: Set[FD_Var]):
        self.vars = vars
        for v in vars:
            All_Different.sibs_dict[v] = All_Different.sibs_dict.setdefault(v, set()) | (vars - {v})

    def __str__(self):
        return f'<{", ".join([v.name for v in vars])}>'

    def all_diff(self):
        instantiated_vars = {v for v in self.vars if v.is_instantiated()}
        vals = {list(v.range)[0] for v in instantiated_vars}
        return len(vals) == len(instantiated_vars)

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
        self.was_set = False
        self.range_was_set_stack = []
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
        return list(self.range)[0] if len(self.range) == 1 else None


@Trace
def FD_solver(vars: Set[FD_Var]):

    if any(not v.range for v in vars):
        return
    elif not All_Different.all_satisfied():
        return
    elif all(v.is_instantiated() for v in vars):
        yield
        return

    else:
        not_set_vars: Set[FD_Var] = {v for v in vars if not v.was_set}
        nxt_var = min(not_set_vars, key=lambda v: len(v.range)) if FD_Var.smallest_first else \
                  not_set_vars.pop()

        for elt in nxt_var.range:
            for _ in nxt_var.set_value(elt):
                yield from FD_solver(vars)


if __name__ == '__main__':
    # Run transversal
    print()
    for FD_Var.propagate in [False, True]:
        for FD_Var.smallest_first in [False, True]:
            FD_Var.id = 0
            All_Different.sibs_dict = {}
            # Create an FV_Var for each set
            vars = {FD_Var(init_range=set) for set in sets}
            All_Different(vars)
            print(f"{Trace.to_str(vars)}")
            Trace.line_no = 0
            Trace.trace = False
            solutions = 0
            print(f'{"~" * 90}')
            print(f'propagate: {FD_Var.propagate}; smallest_first: {FD_Var.smallest_first};')
            for _ in FD_solver(vars):
                solutions += 1
                print(f"{Trace.to_str(vars)}")
            print(f'propagate: {FD_Var.propagate}; smallest_first: {FD_Var.smallest_first}; '
                  f'solutions: {solutions}; lines: {Trace.line_no}')
            print(f'{"~" * 90}\n')


def flatten_sets_to_set(sets):
    return {elt for set in sets for elt in set}


def member_FD(V: FD_Var, a_list: List[Union[FD_Var, int, str]]):
    """
    Is v in a_list?
    """
    # If a_list is empty, it can't have a member. So fail.
    if not a_list: return

    yield from unify_FD(V, a_list[0])
    yield from member_FD(V, a_list[1:])


def ensure_is_FD_Var(x: Union[FD_Var, int, str]) -> FD_Var:
    """
      Applied to each argument in a Structure.
      Applies PyValue to those that are not already Terms.
      If x is not a logic variable, i.e., an instance of Term, it must be a Python value.
      Wrap it in PyValue. (It must be immutable.)
    """
    return x if isinstance(x, FD_Var) else FD_Var({x})


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


# @Trace
# def FD_solver_prop(sets, tnvsl):
#   remaining_indices = uninstantiated_indices(tnvsl)
#   if not remaining_indices: return tnvsl
#
#   if any(not sets[indx] for indx in remaining_indices):
#     return None
#
#   nxt_indx = min(remaining_indices)
#   for elmt in sets[nxt_indx]:
#     if elmt not in tnvsl:
#       new_tnvsl = tnvsl[:nxt_indx] \
#                   + (elmt, ) \
#                   + tnvsl[nxt_indx+1:]
#       new_sets = [set - {elmt} for set in sets]
#       solution = FD_solver_prop(new_sets, new_tnvsl)
#       if solution is not None: return solution
#
#
# if __name__ == '__main__':
#     print(f'\n{"-" * 75}'
#           f'\nFD_solver_prop({sets}, (_, _, _))\n')
#     print(f"\nFirst transversal: {FD_solver_prop(sets, (unassigned, unassigned, unassigned))}")
#
#
# @Trace
# def FD_solver_smallest(sets, tnvsl):
#   remaining_indices = uninstantiated_indices(tnvsl)
#   if not remaining_indices: return tnvsl
#
#   nxt_indx = min(remaining_indices,
#                  key=lambda indx: len(sets[indx]))
#   for elmt in sets[nxt_indx]:
#     if elmt not in tnvsl:
#       new_tnvsl = tnvsl[:nxt_indx] \
#                   + (elmt, ) \
#                   + tnvsl[nxt_indx+1:]
#       solution = FD_solver_smallest(sets, new_tnvsl)
#       if solution is not None: return solution
#
#
# if __name__ == '__main__':
#     print(f'\n{"-" * 75}'
#           f'\nFD_solver_smallest({sets}, (_, _, _))\n')
#     print(f"\nFirst transversal: {FD_solver_smallest(sets, (unassigned, unassigned, unassigned))}")
#
#
# @Trace
# def FD_solver_both(sets, tnvsl):
#   remaining_indices = uninstantiated_indices(tnvsl)
#   if not remaining_indices: return tnvsl
#
#   if any(not sets[indx] for indx in remaining_indices):
#     return None
#
#   nxt_indx = min(remaining_indices,
#                  key=lambda indx: len(sets[indx]))
#   for elmt in sets[nxt_indx]:
#     if elmt not in tnvsl:
#       new_tnvsl = tnvsl[:nxt_indx] \
#                   + (elmt, ) \
#                   + tnvsl[nxt_indx+1:]
#       new_sets = [set - {elmt} for set in sets]
#       solution = FD_solver_both(new_sets, new_tnvsl)
#       if solution is not None: return solution
#
#
# if __name__ == '__main__':
#     print(f'\n{"-" * 75}'
#           f'\nFD_solver_both({sets}, (_, _, _))\n')
#     print(f"\nFirst transversal: {FD_solver_both(sets, (unassigned, unassigned, unassigned))}")
#
#
# @Trace
# def FD_solver_gen(sets, tnvsl):
#     remaining_indices = uninstantiated_indices(tnvsl)
#     if not remaining_indices:
#         yield tnvsl
#     else:
#         if any(not sets[i] for i in remaining_indices):
#             return None
#
#         nxt_indx = min(remaining_indices,
#                        key=lambda indx: len(sets[indx]))
#         for elmt in sets[nxt_indx]:
#             if elmt not in tnvsl:
#                 new_tnvsl = tnvsl[:nxt_indx] \
#                             + (elmt,) \
#                             + tnvsl[nxt_indx + 1:]
#                 new_sets = [set - {elmt} for set in sets]
#                 yield from FD_solver_gen(new_sets, new_tnvsl)
#
#
# if __name__ == '__main__':
#     print(f'\n{"-" * 75}'
#           f'\nFD_solver_gen({sets}, (_, _, _))\n')
#     for tnvsl in FD_solver_gen(sets, (unassigned, unassigned, unassigned)):
#         print('=> ', tnvsl)
#
#     Trace.trace = False
#     for tnvsl in FD_solver_gen(sets, (unassigned, unassigned, unassigned)):
#         sum_string = ' + '.join(str(i) for i in tnvsl)
#         equals = '==' if sum(tnvsl) == 6 else '!='
#         print(f'{sum_string} {equals} 6')
#         if sum(tnvsl) == 6: break
#
#
# def uninstan_indices_lv(tnvsl):
#   return [indx for indx in range(len(tnvsl))
#                if not tnvsl[indx].is_instantiated()]
#
#
# @Trace
# def FD_solver_gen_lv(vars):
#     var_indxs = uninstan_indices_lv(vars)
#
#     if not var_indxs: yield vars
#     else:
#         # empty_sets = [sets[indx].is_empty()
#         #               for indx in var_indxs]
#         if any(not v.range for v in vars): return None
#
#         nxt_indx = min(var_indxs,
#                        key=lambda indx: len(sets[indx]))
#         used_values = [vars[i]
#                               for i in range(len(vars))
#                               if i not in var_indxs]
#         T_Var = vars[nxt_indx]
#         for _ in member(T_Var, sets[nxt_indx]):
#             for _ in fails(member)(T_Var, used_values):
#                 new_sets = [set.discard(T_Var)
#                             for set in sets]
#                 yield from FD_solver_gen_lv(new_sets,
#                                             vars)
#
#
# if __name__ == '__main__':
#     print('\n\n latest')
#     Trace.trace = True
#     print(f'\n{"=" * 15}')
#     # (A, B, C) = (Var(), Var(), Var())
#     # Py_Sets = [PySet(set) for set in sets]
#     vars = tuple([FD_Var(init_range=set) for set in sets])
#     N = 6
#     for _ in FD_solver_gen_lv(vars):
#         vals = [v.value() for v in vars]
#         sum_string = ' + '.join(str(i) for i in vals)
#         equals = '==' if sum(vals) == N else '!='
#         print(f'{sum_string} {equals} 6')
#         if sum(vals) == N: break
#     print(f'{"=" * 15}')
#

# propagate = True
# smallest_first = True
# def find_transversal_with_sum_n(py_sets: List[PySet], n: PyValue):
#     (A, B, C) = (Var(), Var(), Var())
#     for _ in FD_solver_gen_lv(py_sets, (A, B, C)):
#         if A + B + C == n:
#             return (A, B, C)
#         else:
#             print(f'{A} + {B} + {C} != {n}')
#     print(f'No more transversals')
#     # This is the default even without the following statement
#     return None
#

# if __name__ == '__main__':
#     for smallest_first in [False, True]:
#         for propagate in [False, True]:
#             print(f'\n{"-" * 75}'
#                   f'\ntransversal_yield_lv({sets_lv_string}, (PyValue(None), PyValue(None), PyValue(None)))'
#                   f'\n  propagate: {propagate}; smallest_first: {smallest_first}\n')
#             transversal = (PyValue(None), PyValue(None), PyValue(None))
#             for _ in transversal_yield_lv(sets_lv, transversal):
#                 print(f'Yielded logic-variable traversal: {Trace.to_str(transversal)}\n')
#
# """
# ---------------------------------------------------------------------------
# transversal_yield_lv([{1, 2, 3}, {1, 2, 4}, {1}], (PyValue(None), PyValue(None), PyValue(None)))
#   propagate: False; smallest_first: False
#
# sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (_, _, _)
#   sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (1, _, _)
#     sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (1, 2, _)
#     sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (1, 4, _)
#   sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (2, _, _)
#     sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (2, 1, _)
#     sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (2, 4, _)
#       sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (2, 4, 1)
# Yielded logic-variable traversal: (2, 4, 1)
#
#   sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (3, _, _)
#     sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (3, 1, _)
#     sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (3, 2, _)
#       sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (3, 2, 1)
# Yielded logic-variable traversal: (3, 2, 1)
#
#     sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (3, 4, _)
#       sets: [{1, 2, 3}, {1, 2, 4}, {1}], transversal: (3, 4, 1)
# Yielded logic-variable traversal: (3, 4, 1)
#
#
# """
#
# """
# transversal_prolog(Sets, Partial_Transversal, _Complete_Transversal) :-
#     writeln('Sets': Sets,'  Partial_Transversal': Partial_Transversal),
#     fail.
#
# transversal_prolog([], Complete_Transversal, Complete_Transversal) :-
#     format(' => '),
#     writeln(Complete_Transversal), nl.
#
# transversal_prolog([S|Ss], Partial_Transversal, Complete_Transversal_X) :-
#     member(X, S),
#     \+ member(X, Partial_Transversal),
#     append(Partial_Transversal, [X], Partial_Transversal_X),
#     transversal_prolog(Ss, Partial_Transversal_X, Complete_Transversal_X).
#
#
#
#
#
#
#
# ?- transversal_prolog([[1, 2, 3], [2, 4], [1]], [], Complete_Transversal).
#
# Sets:[[1, 2, 3], [2, 4], [1]]; Partial_Transversal:[]
# Sets:[[2, 4], [1]]; Partial_Transversal:[1]
# Sets:[[1]]; Partial_Transversal:[1, 2]
# Sets:[[1]]; Partial_Transversal:[1, 4]
# Sets:[[2, 4], [1]]; Partial_Transversal:[2]
# Sets:[[1]]; Partial_Transversal:[2, 4]
# Sets:[]; Partial_Transversal:[2, 4, 1]
#  => [2, 4, 1]
#
# Sets:[[2, 4], [1]]; Partial_Transversal:[3]
# Sets:[[1]]; Partial_Transversal:[3, 2]
# Sets:[]; Partial_Transversal:[3, 2, 1]
#  => [3, 2, 1]
#
# Sets:[[1]]; Partial_Transversal:[3, 4]
# Sets:[]; Partial_Transversal:[3, 4, 1]
#  => [3, 4, 1]
#
#
#
# """
