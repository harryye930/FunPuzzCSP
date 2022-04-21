#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.
import random

import cspbase
import itertools

'''This file will contain different constraint propagators to be used within
   bt_search.

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instaniated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method).
      bt_search NEEDS to know this in order to correctly restore these
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated
        constraints)
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
   '''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no
    propagation at all. Just check fully instantiated constraints'''

    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []


def prop_FC(csp: cspbase.CSP, newVar=None):
    '''Do forward checking. That is check constraints with
       only one uninstantiated variable. Remember to keep
       track of all pruned variable,value pairs and return '''

    # newVar = None: we look for unary constraints of the csp (constraints whose scope
    # contains only one unassigned variable) and we forward_check these constraints.
    # newVar not None: for forward checking we forward check all constraints with V
    # that have one unassigned variable left

    success, pruned = True, []
    result_pruned = []
    if newVar is None:
        for constraint in csp.get_all_cons():
            if constraint.get_n_unasgn() == 1:
                newVar = constraint.get_unasgn_vars()[0]
                DWO = False
                for constraint in csp.get_cons_with_var(newVar):
                    if constraint.get_n_unasgn() == 1:
                        unassigned_var1 = constraint.get_unasgn_vars()[0]
                        result, pruned_values = fccheck(constraint, unassigned_var1)
                        for pruned_value in pruned_values:
                            result_pruned.append((unassigned_var1, pruned_value))
                        if result == "DWO":
                            DWO = True
                            break
                success = not DWO
                pruned.extend(result_pruned)
        return success, pruned
    else:
        DWO = False
        for constraint in csp.get_cons_with_var(newVar):
            if constraint.get_n_unasgn() == 1:
                unassigned_var1 = constraint.get_unasgn_vars()[0]
                result, pruned_values = fccheck(constraint, unassigned_var1)
                for pruned_value in pruned_values:
                    result_pruned.append((unassigned_var1, pruned_value))
                if result == "DWO":
                    DWO = True
                    break
        return not DWO, result_pruned


def fccheck(con: cspbase.Constraint, x: cspbase.Variable):
    value_pruned = []
    for d in x.cur_domain():
        x.assign(d)
        vals = []
        vars = con.get_scope()
        for var in vars:
            vals.append(var.get_assigned_value())
        if con.check(vals) is False:
            value_pruned.append(d)
            x.prune_value(d)
        x.unassign()
    if True not in x.curdom:
        return "DWO", value_pruned  # domain wipe out
    else:
        return "OK", value_pruned  # everything is okay


def pick_an_unassigned_variable(csp: cspbase.CSP) -> cspbase.Variable:
    """
    pick a random unassigned variables
    """
    return random.choice(csp.get_all_unasgn_vars())

#++++++++++++++++++++++END OF forward check+++++++++++++++++++++++++++++++++++++

def product(unassigned_vars):
    """
    produce the cartesian product of all combination of domain values for variables
    """
    result = []
    for var in unassigned_vars:
        result.append(var.cur_domain())
    result = list(itertools.product(*result))
    result_lst = [list(x) for x in result]
    return result_lst


def prop_GAC(csp: cspbase.CSP, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    """
    newVar=None : for gac we establish initial GAC by initializing the GAC queue
    with all constaints of the csp
    newVar not None: for gac we initialize the GAC queue with all constraints containing V.
    """

    if newVar is None:
        gac_queue = csp.get_all_cons()
    else:
        gac_queue = csp.get_cons_with_var(newVar)

    return gac_enforce(csp, gac_queue)


def gac_enforce(csp: cspbase.CSP, gac_q):
    """
    GAC-Queue contains all constraints one of whose variables has
    had its domain reduced. At the root of the search tree
    first we run GAC_Enforce with all constraints on GAC-Queue

    """
    pruned_list = []
    while not len(gac_q) == 0:
        curr_constraint = gac_q.pop(0)  #gac_q.extract

        for var in curr_constraint.get_unasgn_vars():
            for values in var.cur_domain():
                assgnmt_found = False
                cspbase.Variable.assign(var, values)
                unassigned_vars = cspbase.Constraint.get_unasgn_vars(curr_constraint)
                all_combo_with_vars = product(unassigned_vars)
                for i in range(len(all_combo_with_vars)):
                    for var_i in range(len(unassigned_vars)):
                        cspbase.Variable.assign(unassigned_vars[var_i], all_combo_with_vars[i][var_i])
                    vals = []
                    vars = curr_constraint.get_scope()
                    for var_1 in vars:
                        vals.append(var_1.get_assigned_value())
                    if cspbase.Constraint.check(curr_constraint, vals):
                        assgnmt_found = True

                    for var_i in range(len(unassigned_vars)):
                        cspbase.Variable.unassign(unassigned_vars[var_i])
                    if assgnmt_found is True:
                        break

                cspbase.Variable.unassign(var)
                if not assgnmt_found:
                    cspbase.Variable.prune_value(var, values)
                    pruned_list.append((var, values))
                    if cspbase.Variable.cur_domain(var) == []:
                        gac_q = []  # does nothing but means emptying gac q
                        return False, pruned_list
                    else:   # pushing new constraints to gac q
                        extra_constraints = csp.get_cons_with_var(var)
                        for extra in extra_constraints:
                            if extra not in gac_q:
                                gac_q.append(extra)

    return True, pruned_list



