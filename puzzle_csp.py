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

from cspbase import *
import itertools


def binary_ne_grid(fpuzz_grid):
    board_length = fpuzz_grid[0][0]

    variable_domain = [i for i in range(1, board_length + 1)]
    variable_list = [[Variable("element {}{}".format(row, column), variable_domain)
                      for column in range(board_length)]
                     for row in range(board_length)]

    coor = [i for i in range(board_length)]
    coordinates = itertools.product(coor, coor)
    all_satisfying_pairs = pair_distinct_pairs(board_length)
    constraints = []
    variable_list_flat = []
    for coordinate in coordinates:
        vertic = coordinate[0]
        horizon = coordinate[1]
        curr_variable = variable_list[vertic][horizon]
        variable_list_flat.append(curr_variable)

        for further_column in range(horizon + 1, board_length):
            assigned_variable = variable_list[vertic][further_column]
            constraint_name = "{}{} + {}{}".format(vertic, horizon, vertic, further_column)
            new_constraint = Constraint(constraint_name, [curr_variable, assigned_variable])
            new_constraint.add_satisfying_tuples(tuple(all_satisfying_pairs.copy()))
            constraints.append(new_constraint)

        for further_row in range(vertic + 1, board_length):
            assigned_variable = variable_list[further_row][horizon]
            constraint_name = "{}{} + {}{}".format(vertic, horizon, further_row, horizon)
            new_constraint = Constraint(constraint_name, [curr_variable, assigned_variable])
            new_constraint.add_satisfying_tuples(tuple(all_satisfying_pairs.copy()))
            constraints.append(new_constraint)

    new_csp = CSP("{} by {} binary non-equal".format(board_length, board_length), variable_list_flat)
    for c in constraints:
        new_csp.add_constraint(c)
    return new_csp, variable_list


def list_to_matrix(lst, board_length):
    result = []
    for i in range(board_length):
        row = []
        for j in range(board_length):
            index = i * board_length + j
            row.append(lst[index])
        result.append(row)
    return result


def nary_ad_grid(fpuzz_grid):
    board_length = fpuzz_grid[0][0]
    variable_domain = [i for i in range(1, board_length + 1)]
    variable_list = [[Variable("element {}{}".format(row, column), variable_domain)
                      for column in range(board_length)]
                     for row in range(board_length)]

    coor = [i for i in range(board_length)]
    coordinates = itertools.product(coor, coor)
    variable_list_flat = []
    for coordinate in coordinates:
        vertic = coordinate[0]
        horizon = coordinate[1]
        curr_variable = variable_list[vertic][horizon]
        variable_list_flat.append(curr_variable)

    constraints = []


    for i in range(board_length):
        row_vars, col_vars = find_row_col_vars(i, variable_list)
        con_row = Constraint("row:{}".format(i), tuple(row_vars))
        con_col = Constraint("col:{}".format(i), tuple(col_vars))
        sat_tuples = find_all_valid_options(board_length)
        con_row.add_satisfying_tuples(tuple(sat_tuples.copy()))
        con_col.add_satisfying_tuples(tuple(sat_tuples.copy()))
        constraints.append(con_row)
        constraints.append(con_col)

    new_csp = CSP("{} by {} binary non-equal".format(board_length, board_length), variable_list_flat)
    for constraint in constraints:
        new_csp.add_constraint(constraint)
    return new_csp, variable_list


def find_row_col_vars(index, variable_list):
    row_vars = variable_list[index]
    col_vars = []
    for rows in variable_list:
        col_vars.append(rows[index])
    return row_vars, col_vars


def find_all_valid_options(board_length):
    domain = list(range(1, board_length + 1))
    permutations = itertools.permutations(domain)
    result = []
    for temp in permutations:
        result.append(temp)
    return result


def caged_csp_model(fpuzz_grid):
    board_length = fpuzz_grid[0][0]
    # a list of list of constrains for [var1, 2, 3 ... 9]
    variable_domain = [i for i in range(1, board_length + 1)]
    variable_list = [[Variable("element {}{}".format(row, column), variable_domain)
                      for column in range(board_length)]
                     for row in range(board_length)]

    coor = [i for i in range(board_length)]
    coordinates = itertools.product(coor, coor)
    all_satisfying_pairs = pair_distinct_pairs(board_length)
    constraints = []
    variable_list_flat = []
    for coordinate in coordinates:
        vertic = coordinate[0]
        horizon = coordinate[1]
        curr_variable = variable_list[vertic][horizon]
        variable_list_flat.append(curr_variable)
        # row: preserve vertic, but change horizons
        for further_column in range(horizon + 1, board_length):
            assigned_variable = variable_list[vertic][further_column]
            constraint_name = "{}{} + {}{}".format(vertic, horizon, vertic, further_column)
            new_constraint = Constraint(constraint_name, [curr_variable, assigned_variable])
            new_constraint.add_satisfying_tuples(tuple(all_satisfying_pairs.copy()))
            constraints.append(new_constraint)
        # column: preserve horizon
        for further_row in range(vertic + 1, board_length):
            assigned_variable = variable_list[further_row][horizon]
            constraint_name = "{}{} + {}{}".format(vertic, horizon, further_row, horizon)
            new_constraint = Constraint(constraint_name, [curr_variable, assigned_variable])
            new_constraint.add_satisfying_tuples(tuple(all_satisfying_pairs.copy()))
            constraints.append(new_constraint)

    for constraint_index in range(1, len(fpuzz_grid)):
        curr_analysis = fpuzz_grid[constraint_index]
        result_needed = curr_analysis[-2]
        operation_index = curr_analysis[-1]
        operation = ['+', '-', '/', '*']
        num_variables = len(curr_analysis) - 2
        nested_list = [variable_domain.copy() for i in range(num_variables)]
        all_combinations = itertools.product(*nested_list)
        variable_list_tmp_analysis = []
        for variable_index in range(0, num_variables):
            row = curr_analysis[variable_index] // 10 - 1
            col = curr_analysis[variable_index] % 10 - 1
            variable_list_tmp_analysis.append(variable_list[row][col])
        new_constraint = Constraint("block {}".format(constraint_index), variable_list_tmp_analysis)
        for combinations in all_combinations:
            if evaluate(combinations, operation[operation_index], result_needed):
                new_constraint.add_satisfying_tuples([combinations])
        constraints.append(new_constraint)

    new_csp = CSP("{} by {} binary non-equal".format(board_length, board_length), variable_list_flat)
    for c in constraints:
        new_csp.add_constraint(c)
    return new_csp, variable_list


def pair_distinct_pairs(board_length):
    satisfying_pair = []
    sample_list = [i for i in range(1, board_length + 1)]
    for i in range(1, board_length + 1):
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






