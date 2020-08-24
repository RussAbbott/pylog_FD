from random import randint, sample
from typing import List, Tuple

from control_structures import Trace
# from logic_variables import Var

# Use this for all non-lv tests.
# Is there a better example?
nbr_sets = 5

sets_size_low = 2
sets_size_high = nbr_sets-1

set_vals_size = nbr_sets
set_range_start_max = 27-set_vals_size

alpha_low = randint(ord('a'), ord('a')+set_range_start_max)
set_vals = [chr(alpha_low+k) for k in range(set_vals_size)]
sets = [frozenset(k for k in sample(set_vals, randint(sets_size_low, sets_size_high)))
        for _ in range(nbr_sets)]

class FD_Var:
  """
  A Finite Domain variable
  """

  id=0

  def __init__(self, init_range=frozenset({}), name=None):
    # self.unification_chain_next points to the next element on the unification_chain, if any.
    FD_Var.id += 1
    self.id = FD_Var.id
    self.name = name if name is not None else f'V{str(self.id)}'
    self.range = init_range
    self.locked = False
    self.range_locked_stack = []

  def __hash__(self):
      return hash(self.id)

  def __str__(self):
    name_part = '' if self.name is None else self.name + ('*' if self.locked else '') + ': '
    (left, right) = ("{", "}")
    return f'{name_part}{left}{", ".join([str(x) for x in self.range])}{right}'

  def undo_update_range(self):
    (self.range, self.locked) = self.range_locked_stack[-1]
    self.range_locked_stack = self.range_locked_stack[:-1]

  def update_range(self, new_range, locked=False):
    self.range_locked_stack = self.range_locked_stack + [(self.range, self.locked)]
    self.range = new_range
    self.locked = self.locked or locked


class All_Different:
    def __init__(self, vars):
        self.vars = vars
        self.used = set()
        self.instantiated_vars = set()

    def __str__(self):
        return f'<{", ".join([v.name for v in vars])}>'

    def all_diff(self):
        instantiated_vars = {v for v in self.vars if len(v.range) == 1}
        vals = {list(v.range)[0] for v in instantiated_vars}
        return len(vals) == len(instantiated_vars)

    # def update_all_diff(self):
    #     new_instantiations = {v for v in self.vars if not v in self.instantiated_vars and len(v.range) == 1}



def flatten_sets_to_set(sets):
    return {elt for set in sets for elt in set}


def siblings(all_diffs, nxt_var):
    sibs = set(v for ad in all_diffs if nxt_var in ad.vars
                 for v in ad.vars if v is not nxt_var)
    return sibs


def tnvsl_FD(vars: Tuple[FD_Var], all_diffs: List[All_Different]):
    # {FD_Var_x: {FD_Var_i that must be different from FD_Var_x}}
    sibs_dict = {}

    @Trace
    def tnvsl_FD_aux(vars: Tuple[FD_Var]):
      if any(v for v in vars if not(v.range)): return None
      if any(ad for ad in all_diffs if not ad.all_diff()): return None
      uninstan_vars = [v for v in vars if len(v.range) > 1]
      if not uninstan_vars:
          # print(', '.join([f'{v.name}->[{", ".join([v1.name for v1 in sibs_dict[v]])}]' for v in sibs_dict]))
          return vars

      unlocked_vars = {v for v in vars if not v.locked}
      nxt_var = unlocked_vars.pop() if not smallest_first else \
                min(unlocked_vars, key=lambda v: len(v.range))
      for val in nxt_var.range:
          nxt_var.update_range({val}, locked=True)
          if nxt_var not in sibs_dict:
            sibs_dict[nxt_var] = siblings(all_diffs, nxt_var)
          sibs = sibs_dict[nxt_var]
          if propagate:
              for v in sibs:
                  v.update_range(v.range - {val})
          full_tnvsl = tnvsl_FD_aux(vars)
          if full_tnvsl is not None: return full_tnvsl
          else:
              nxt_var.undo_update_range()
              if propagate:
                for v in sibs:
                  v.undo_update_range()

    return tnvsl_FD_aux(vars)


if __name__ == '__main__':
    print()
    for propagate in [False, True]:
        for smallest_first in [False, True]:
            FD_Var.id = 0
            vars = tuple([FD_Var(init_range=set) for set in sets])
            all_diff = All_Different(vars)
            Trace.line_no = 0
            print(f'{"~" * 90}')
            print(f'smallest_first: {smallest_first}; propagate: {propagate};')
            print(f"First transversal: {Trace.to_str(tnvsl_FD(vars, [all_diff]))}")
            print(f'smallest_first: {smallest_first}; propagate: {propagate}; lines: {Trace.line_no}')
            print(f'{"~" * 90}\n')


# @Trace
# def tnvsl_FD_prop(sets, tnvsl):
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
#       full_tnvsl = tnvsl_FD_prop(new_sets, new_tnvsl)
#       if full_tnvsl is not None: return full_tnvsl
#
#
# if __name__ == '__main__':
#     print(f'\n{"-" * 75}'
#           f'\ntnvsl_FD_prop({sets}, (_, _, _))\n')
#     print(f"\nFirst transversal: {tnvsl_FD_prop(sets, (unassigned, unassigned, unassigned))}")
#
#
# @Trace
# def tnvsl_FD_smallest(sets, tnvsl):
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
#       full_tnvsl = tnvsl_FD_smallest(sets, new_tnvsl)
#       if full_tnvsl is not None: return full_tnvsl
#
#
# if __name__ == '__main__':
#     print(f'\n{"-" * 75}'
#           f'\ntnvsl_FD_smallest({sets}, (_, _, _))\n')
#     print(f"\nFirst transversal: {tnvsl_FD_smallest(sets, (unassigned, unassigned, unassigned))}")
#
#
# @Trace
# def tnvsl_FD_both(sets, tnvsl):
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
#       full_tnvsl = tnvsl_FD_both(new_sets, new_tnvsl)
#       if full_tnvsl is not None: return full_tnvsl
#
#
# if __name__ == '__main__':
#     print(f'\n{"-" * 75}'
#           f'\ntnvsl_FD_both({sets}, (_, _, _))\n')
#     print(f"\nFirst transversal: {tnvsl_FD_both(sets, (unassigned, unassigned, unassigned))}")
#
#
# @Trace
# def tnvsl_FD_gen(sets, tnvsl):
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
#                 yield from tnvsl_FD_gen(new_sets, new_tnvsl)
#
#
# if __name__ == '__main__':
#     print(f'\n{"-" * 75}'
#           f'\ntnvsl_FD_gen({sets}, (_, _, _))\n')
#     for tnvsl in tnvsl_FD_gen(sets, (unassigned, unassigned, unassigned)):
#         print('=> ', tnvsl)
#
#     Trace.trace = False
#     for tnvsl in tnvsl_FD_gen(sets, (unassigned, unassigned, unassigned)):
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
# def tnvsl_FD_gen_lv(sets, tnvsl):
#     var_indxs = uninstan_indices_lv(tnvsl)
#
#     if not var_indxs: yield tnvsl
#     else:
#         empty_sets = [sets[indx].is_empty()
#                       for indx in var_indxs]
#         if any(empty_sets): return None
#
#         nxt_indx = min(var_indxs,
#                        key=lambda indx: len(sets[indx]))
#         used_values = PyList([tnvsl[i]
#                               for i in range(len(tnvsl))
#                               if i not in var_indxs])
#         T_Var = tnvsl[nxt_indx]
#         for _ in member(T_Var, sets[nxt_indx]):
#             for _ in fails(member)(T_Var, used_values):
#                 new_sets = [set.discard(T_Var)
#                             for set in sets]
#                 yield from tnvsl_FD_gen_lv(new_sets,
#                                             tnvsl)
#
#
# if __name__ == '__main__':
#     print('\n\n latest')
#     Trace.trace = True
#     print(f'\n{"=" * 15}')
#     (A, B, C) = (Var(), Var(), Var())
#     Py_Sets = [PySet(set) for set in sets]
#     N = PyValue(6)
#     for _ in tnvsl_FD_gen_lv(Py_Sets, (A, B, C)):
#         sum_string = ' + '.join(str(i) for i in (A, B, C))
#         equals = '==' if A + B + C == N else '!='
#         print(f'{sum_string} {equals} 6')
#         if A + B + C == N: break
#     print(f'{"=" * 15}')
#

# propagate = True
# smallest_first = True
# def find_transversal_with_sum_n(py_sets: List[PySet], n: PyValue):
#     (A, B, C) = (Var(), Var(), Var())
#     for _ in tnvsl_FD_gen_lv(py_sets, (A, B, C)):
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