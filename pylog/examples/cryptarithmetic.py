from typing import Iterable, List, Union

from logic_variables import n_Vars, PyValue, unify, unify_pairs, Var


def are_we_done(carry_out: int, sum_dig: int, Tot_Dig: Var, Carry_Out_Dig: Var, digits_in: List[int], Non_Zero_Vars):
  """
  Instantiate If Tot_Dig is not yet instantiated, instantiate it to the sum (if that digit is available)
  If Total[index] is already instantiated, ensure it is consistent with the sum.
  Instantiate Carries[index - 1]
  """
  # (c, d) = divmod(total, 10)
  tot_digit_py_value = Tot_Dig.get_py_value( )
  # If Total[index] is instantiated, is it consistent with d?
  # If so, instantiate Carry_Out_Dig and yield the current digits_in
  if sum_dig == tot_digit_py_value:
    for _ in unify(Carry_Out_Dig, carry_out):
      yield digits_in
  # If Total[index] is not instantiated, i.e., tot_digit_py_value is None, can it be instantiated to d?
  # If so, instantiate Tot_Dig and Carry_Out_Dig and remove d from the available digits.
  elif tot_digit_py_value is None:
    try:
      # digits_in.index(sum_dig) throws a ValueError if sum_dig is not in digits_in
      i = digits_in.index(sum_dig)
      if digits_in[i] != 0 or Tot_Dig not in Non_Zero_Vars:
        for _ in unify_pairs([(Tot_Dig, sum_dig), (Carry_Out_Dig, carry_out)]):
          yield digits_in[:i] + digits_in[i + 1:]
    except ValueError:
      pass


def solve(Carries: List[Var],
          Term1: List[Union[Var, PyValue]],
          Term2: List[Union[Var, PyValue]],
          Total: List[Union[Var, PyValue]],
          Non_Zero_Vars: List[Var]):
  """
  Solve the problem.
  The two embedded functions below refer to the lists in solve's params.
  The lists never change, but their elements are unified with values.
  No point is copying the lists repeatedly. So embed the functions that refer to them.
  """

  def b_to_0(c):
    """ Convert ' ' to 0 when adding. Used only by are_we_done. """
    return 0 if c == ' ' else c

  def instantiate_all(Vars: List[Var], index: int, digits_in: List[int]):
    """
    Vars are the digits we are currently adding, one from each term and one from the sum.
    Unify them with digit values.
    digits-in are the digits that have not yet been assigned to a Var.
    Return (through yield) the digits that are not yet used after the new assignments.
    We do this recursively on Vars.
    """
    if not Vars:
      # Are we done? We've instantiated the term digits.
      # Instantiate Tot_Dig (if possible) and Carries[index - 1]
      (carry_in, d1, d2) = (b_to_0(d.get_py_value( )) for d in [Carries[index], Term1[index], Term2[index]])
      total = sum([carry_in, d1, d2])
      (c, d) = divmod(total, 10)
      yield from are_we_done(c, d, Total[index], Carries[index-1], digits_in, Non_Zero_Vars)
    elif not digits_in:
      # No more digits. Fail.
      return
    else:
      # Get head and tail of Vars.
      [V, *Vs] = Vars
      # If V already has a value nothing to do. Go on to the next Vars.
      if isinstance(V.trail_end( ), PyValue):
        yield from instantiate_all(Vs, index, digits_in)
      else:
        # Give V one of the available digits. Through "backup" all digits will be tried.
        for i in range(len(digits_in)):
          # Make sure we don't assign 0 to one of the leading digits.
          if digits_in[i] != 0 or V not in Non_Zero_Vars:
            for _ in unify(V, digits_in[i]):  # Don't have to wrap digits_in[i] in PyValue explicitly.
              yield from instantiate_all(Vs, index, digits_in[:i] + digits_in[i + 1:])

  # def are_we_done(total: int, Tot_Dig: Var, Carry_Out_Dig: Var, digits_in: List[int]):
  #   """
  #   Instantiate If Total[index] is not yet instantiated, instantiate it to the sum (if that digit is available)
  #   If Total[index] is already instantiated, ensure it is consistent with the sum.
  #   Instantiate Carries[index - 1]
  #   """
  #   (c, d) = divmod(total, 10)
  #   tot_digit_py_value = Tot_Dig.get_py_value( )
  #   # If Total[index] is instantiated, is it consistent with d?
  #   # If so, instantiate Carry_Out_Dig and yield the current digits_in
  #   if d == tot_digit_py_value:
  #     for _ in unify(Carry_Out_Dig, c):
  #       yield digits_in
  #   # If Total[index] is not instantiated, i.e., tot_digit_py_value is None, can it be instantiated to d?
  #   # If so, instantiate Tot_Dig and Carry_Out_Dig and remove d from the available digits.
  #   elif tot_digit_py_value is None:
  #     try:
  #       # digits_in.index(d) throws a ValueError if d is not in digits_in
  #       i = digits_in.index(d)
  #       if digits_in[i] != 0 or Tot_Dig not in Non_Zero_Vars:
  #         for _ in unify_pairs([(Tot_Dig, d), (Carry_Out_Dig, c)]):
  #           yield digits_in[:i] + digits_in[i + 1:]
  #     except ValueError:
  #       pass
  #
  def solve_aux(index: int, digits_in: List[int]):
    """ Traditional addition: work from right to left. """
    # When we reach 0, we're done.
    if index == 0:
      # Can't allow a carry to that position.
      if Carries[0].get_py_value() == 0:
        yield
      else:
        # If we reach index == 0 but have a carry into the last column, fail.
        # Won't have such a carry with only two terms. But it might happen with many terms,.
        return
    else:
      for digits_out in instantiate_all([Term1[index], Term2[index]], index, digits_in):
          yield from solve_aux(index-1, digits_out)
    
  yield from solve_aux(len(Carries)-1, list(range(10)))


def solution_to_string(solution):
  """ Convert a list of digits to a single number represented as a string. """
  return ''.join([str(c) for c in PyValue.get_py_values(solution)])


def letters_to_vars(st: Iterable, d: dict) -> List:
  return [d[s] for s in st]


def set_up_puzzle(t1, t2, total):
  var_letters = sorted(list(set(t1 + t2 + total)))
  vars_dict = dict(zip(var_letters, n_Vars(len(var_letters))))
  Z = PyValue(' ')
  length = len(total) + 1
  T1 = [Z for _ in range((length - len(t1)))] + letters_to_vars(t1, vars_dict)
  T2 = [Z for _ in range((length - len(t2)))] + letters_to_vars(t2, vars_dict)
  Tot = [Z for _ in range((length - len(total)))] + letters_to_vars(total, vars_dict)
  non_zero_vars = letters_to_vars({t1[0], t2[0], total[0]}, vars_dict)
  carries = [*list(n_Vars(length - 1)), PyValue(0)]
  return (T1, T2, Tot, non_zero_vars, carries)


def solve_crypto(t1: str, t2: str, total: str):
  (T1, T2, Tot, non_zero_vars, carries) = set_up_puzzle(t1, t2, total)
  want_more = None
  for _ in solve(carries, T1, T2, Tot, non_zero_vars):
    # Discard the leading blanks and convert number each to a string.
    (t1_out, t2_out, tot_out) = map(solution_to_string, (T1[1:], T2[1:], Tot[1:]))
    print()
    print(f'  {t1}  -> {t1_out}')
    print(f'+ {t2}  -> {t2_out}')
    print(f'{"-" * (len(total)+1)}     {"-" * len(total)}')
    print(f' {total}  -> {tot_out}')
    ans = input('\nLook for more solutions? (y/n) > ').lower( )
    want_more = ans[0] if len(ans) > 0 else 'n'
    if want_more != 'y':
      break
  if want_more == 'y':
    print('No more solutions.')


if __name__ == '__main__':

  # See http://bach.istc.kobe-u.ac.jp/llp/crypt.html (and links) for many(!) others.
  for puzzle in [('SEND', 'MORE', 'MONEY'),
                 ('BASE', 'BALL', 'GAMES'),
                 ('SATURN', 'URANUS', 'PLANETS'),
                 ('POTATO', 'TOMATO', 'PUMPKIN')
                 ]:
    solve_crypto(*puzzle)
