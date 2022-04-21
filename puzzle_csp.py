#Look for #IMPLEMENT tags in this file.
'''
All models need to return a CSP object, and a list of lists of Variable objects
representing the board. The returned list of lists is used to access the
solution.

For example, after these three lines of code

    csp, var_array = caged_csp_model(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array[0][0].get_assigned_value() should be the correct value in the top left
cell of the FunPuzz puzzle.

The grid-only models do not need to encode the cage constraints.

1. binary_ne_grid (worth 10/100 marks)
    - A model of a FunPuzz grid (without cage constraints) built using only
      binary not-equal constraints for both the row and column constraints.

2. nary_ad_grid (worth 10/100 marks)
    - A model of a FunPuzz grid (without cage constraints) built using only n-ary
      all-different constraints for both the row and column constraints.

3. caged_csp_model (worth 25/100 marks)
    - A model built using your choice of (1) binary binary not-equal, or (2)
      n-ary all-different constraints for the grid.
    - Together with FunPuzz cage constraints.

'''
import copy

from cspbase import *
import itertools


def binary_ne_grid(fpuzz_grid):
    n = fpuzz_grid[0][0]

    vars = []
    for i in range(n*n):
        new_var = Variable(i, list(range(1, n+1)))
        vars.append(new_var)
    vars_list_of_list = list_to_matrix(vars, n)

    cons = []
    for vi in range(1, n+1):
        for vj in range(vi+1, n+1):
            con = Constraint("C(v{}, v{})".format(vi, vj), [vars[vi], vars[vj]])
            sat_tuples = []
            all_combo = itertools.product(list(range(1, n+1)), list(range(1, n+1)))
            for t in all_combo:
                if t[0] != t[1]:
                    sat_tuples.append(t)
            con.add_satisfying_tuples(sat_tuples)
            cons.append(con)
    csp = CSP("{} by {} binary non-equal".format(n, n), vars)
    for c in cons:
        csp.add_constraint(c)
    return csp, vars_list_of_list


def list_to_matrix(lst, n):
    result = []
    for i in range(n):
        row = []
        for j in range(n):
            index = i*n + j
            row.append(lst[index])
        result.append(row)
    return result


def nary_ad_grid(fpuzz_grid):
    n = fpuzz_grid[0][0]
    vars = []
    for i in range(n*n):
        new_var = Variable(i, list(range(1, n+1)))
        vars.append(new_var)
    vars_list_of_list = list_to_matrix(vars, n)
    cons = []

    diagonals = find_diagonal_indices(n)
    for i in range(len(diagonals)):
        diag_index = diagonals[i]
        curr_row, curr_col = find_row_and_column(diag_index, n)
        row_vars, col_vars = find_row_col_vars(curr_row, curr_col, vars)
        con_row = Constraint("C(row:{})".format(i), row_vars)
        con_col = Constraint("C(col:{})".format(i), col_vars)
        sat_tuples = find_all_valid_options(n)
        con_row.add_satisfying_tuples(sat_tuples.copy())
        con_col.add_satisfying_tuples(sat_tuples.copy())
        cons.append(con_row)
        cons.append(con_col)
    csp = CSP("{} by {} binary non-equal".format(n, n), vars)
    for c in cons:
        csp.add_constraint(c)
    return csp, vars_list_of_list


def find_row_and_column(index, n):
    """
    >>> find_row_and_column(1, 2)
    ([0, 1], [1, 3])
    >>> find_row_and_column(3, 3)
    ([3, 4, 5], [0, 3, 6])
    """
    flag = False
    for row_num in range(n):
        for col_num in range(n):
            curr_index = row_num * n + col_num
            if index == curr_index:
                flag = True
                break
        if flag:
            break
    row_indices = []
    col_indices = []
    for x in range(n):
        index_row = row_num * n + x
        row_indices.append(index_row)
        index_col = x * n + col_num
        col_indices.append(index_col)
    return row_indices, col_indices


def find_diagonal_indices(n):
    """
    >>> find_diagonal_indices(2)
    [0, 3]
    >>> find_diagonal_indices(3)
    [0, 4, 8]
    """
    diagonals = []
    for num in range(n):
        diagonals.append(num * n + num)
    return diagonals


def find_row_col_vars(row_vertices, col_vertices, vars):
    row_vars = []
    col_vars = []
    for row_vertex in row_vertices:
        row_vars.append(vars[row_vertex])
    for col_vertex in col_vertices:
        col_vars.append(vars[col_vertex])
    return row_vars, col_vars


def find_all_valid_options(n):
    domain = list(range(1, n+1))
    lst = []
    for i in range(n):
        lst.append(domain.copy())
    all_combo = itertools.product(*lst)
    result = []
    for temp in all_combo:
        if len(set(temp)) == len(temp):
            result.append(temp)
    return result


def caged_csp_model(fpuzz_grid):
    n = fpuzz_grid[0][0]
    vars = []
    operations = {0: "+", 1: "-", 2: "/", 3: "*"}
    for i in range(n*n):
        new_var = Variable(i, list(range(1, n+1)))
        vars.append(new_var)
    vars_list_of_list = list_to_matrix(vars, n)

    all_cords = itertools.product(list(range(n)), list(range(n)))
    all_satisfying_pairs = pair_distinct_pairs(n)
    cons = []
    for coord in all_cords:
        col_coord = coord[0]
        row_coord = coord[1]
        curr_variable = vars_list_of_list[col_coord][row_coord]
        for following_row in range(row_coord + 1, n):
            assigned_variable = vars_list_of_list[col_coord][following_row]
            constraint_name = "var{}{}&var{}{}".format(col_coord+1, row_coord+1, col_coord+1, following_row+1)
            new_constraint = Constraint(constraint_name, [curr_variable, assigned_variable])
            new_constraint.add_satisfying_tuples(tuple(all_satisfying_pairs.copy()))
            cons.append(new_constraint)
        for following_col in range(col_coord + 1, n):
            assigned_variable = vars_list_of_list[following_col][row_coord]
            constraint_name = "var{}{}&var{}{}".format(col_coord+1, row_coord+1, following_col+1, row_coord+1)
            new_constraint = Constraint(constraint_name, [curr_variable, assigned_variable])
            new_constraint.add_satisfying_tuples(tuple(all_satisfying_pairs.copy()))
            cons.append(new_constraint)

    for cons_in_grid in range(1, len(fpuzz_grid)):
        curr_con_in_grid = fpuzz_grid[cons_in_grid]
        comp_result = curr_con_in_grid[-2]  # result we need
        op_i = curr_con_in_grid[-1]         # operation in the block
        num_vars = len(curr_con_in_grid) - 2
        nested_list = [list(range(1, n+1)) for _ in range(num_vars)]
        all_combinations = itertools.product(*nested_list)      # produce all potential assignment variables for existing num of vars
        variable_list = []

        for var_index in range(num_vars):
            row_coord = curr_con_in_grid[var_index] // 10 - 1
            col_coord = curr_con_in_grid[var_index] % 10 - 1
            variable_list.append(vars_list_of_list[row_coord][col_coord])
        new_constraint = Constraint("block {}".format(cons_in_grid), variable_list)
        for combinations in all_combinations:
            if evaluate(combinations, operations[op_i], comp_result) is True:
                new_constraint.add_satisfying_tuples([combinations])
        cons.append(new_constraint)

    new_csp = CSP("{} by {} caged csp".format(n, n), vars)
    for con in cons:
        new_csp.add_constraint(con)
    return new_csp, vars_list_of_list


def pair_distinct_pairs(board_size):
    satisfying_pair = []
    sample_list = [i for i in range(1, board_size + 1)]
    for i in range(1, board_size + 1):
        removed_l = sample_list.copy()
        removed_l.remove(i)
        cartesian_product = itertools.product([i], removed_l)
        for product in cartesian_product:
            satisfying_pair.append(product)
    return satisfying_pair


def evaluate(nums, op, result):
    """
    Evaluate if all permutations of nums with operation op can produce result
    """

    all_combo = itertools.permutations(nums)
    for combo in all_combo:
        eval_str = ""
        for i in range(len(combo)):
            eval_str += str(combo[i])
            if i != len(combo) - 1:
                eval_str += str(op)
        temp_result = eval(eval_str)
        if temp_result == result:
            return True
    return False




