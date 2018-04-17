#!/usr/bin/env python3
# vim: tabstop=8 expandtab shiftwidth=4 softtabstop=4

# Framework written by 
# Pascal Bongaertz
# Daniel Gossen
# Hendrik Willing

"""
SYNOPSIS
    co_rr_solver [OPTION] [DIRECTORY]

DESCRIPTION
    All found recurrence relations in DIRECTORY that have filenames matching "comass??.txt"
    are inspected and a direct formula describing these recurrence relations is stored in the
    file "comass??-dir.txt". If DIRECTORY is omitted, the location of "co_rr_solver" is taken
    as directory.

    -v, --verbose
        print debugging information during execution of "co_rr_solver"
"""

import glob # Library for filename pattern-matching
import sympy as sy
from sympy.solvers.solveset import linsolve
import sys # For access to the given argument
import os  # Gives access to current location of co_rr_solver
import pandas
import math

# Global variables:
next_symbolic_var_index = 0 # This variable indicates the next index for the p_x variable names needed for Theorem 6.
print_debug_information = False # This variable indicates whether debug information should be printed (this is read in using the command line argument list)

"""Print the given list line by line, each line started and ended with a quotation mark."""
def print_list(listing):
    for line in listing:
        print("\"" + line + "\"")

"""Print the dictionary element per element: First key, then ":" and value."""
def print_dict(dictionary):
    for key in dictionary:
        print(str(key) + ": " + str(dictionary[key]))

"""First checks if debug printing is allowed.
   Then checks the type of the input of the function.
   Then prints the input based on the type of input."""
def debug_print(debug_information):
    global print_debug_information
    if print_debug_information:
        if type(debug_information) == dict:
            print_dict(debug_information)
        elif type(debug_information) == list:
            print_list(debug_information)
        else:
            print(str(debug_information))

"""Determines for each line in lines:
    The x-value of s(x) and the corresponding y-value of s(x)=y.
    This is returned as dictionary where x is the integer-key and y the string-value."""
def det_init_conditions(lines):
    conditions = {}
    for line in lines:
        pos_s_bracket = line.find("s(") # Position of "s("
        start_index_nr = pos_s_bracket + 2 # First index of x-value
        pos_bracket_equal = line.find(")=", pos_s_bracket) # Position of ")="
        start_index_y = pos_bracket_equal + 2 # First position after the "=" symbol
        x_value = int(line[start_index_nr:pos_bracket_equal])
        y_value = line[start_index_y:]
        conditions[x_value] = y_value
    return conditions

"""Searches for the left begin of the term (beginning at start) and returns the first position belonging to the term, where the symbols are still
    counted as part of the term (may be handy for "+" and "-", but REMIND THIS if the symbols list also contains "*" and "/")..
    The begin of a new term is indicated with one of the symbols in the list "symbols", but only if there are no opened brackets at this position."""
def search_left_term_begin(equation, start, symbols):
    bracket_count = 0 # Indicating the number of opened bracket-scopes
    index = start
    while index >= 0:
        if equation[index] == ")":
            bracket_count += 1
        elif equation[index] == "(":
            bracket_count -= 1
        elif bracket_count == 0 and equation[index] in symbols:
            return index
        index -= 1
    return 0 # If we got until here the term starts at the begin of equation

"""Searches for the right end of the term (beginning at start) and returns the last position belonging to the term.
    The begin of a new term is indicated with one of the symbols in the list "symbols", but only if there are no opened brackets at this position."""
def search_right_term_end(equation, start, symbols):
    bracket_count = 0  # Indicating the number of opened bracket-scopes
    index = start
    while index < len(equation):
        if equation[index] == "(":
            bracket_count += 1
        elif bracket_count == 0 and equation[index] in symbols and index > 0:
            return index - 1
        elif equation[index] == ")":
            bracket_count -= 1
        index += 1
    return len(equation) - 1  # If we got until here the term ends at the end of equation

"""Determines and returns:
    1. The value of x in s(n-x) as integer, where pos_s should be the index of "s" in equation
    2. equation where "s(n-x)" is replaced by "1"."""
def recurrent_step_length(equation, pos_s):
    exclusive_end_pos = equation.find(")", pos_s)
    value = equation[pos_s + 4:exclusive_end_pos]
    equation = equation.replace("s(n-" + value + ")", "1") # Replace "s(n-x)" with "1"
    return int(value), equation


"""Determines and returns:
    1. A dictionary of the associated homogeneous recurrence relation in default form, where:
        -The integer-key is x of s(n-x) (thus without minus)
        -The string-value is y of y*s(n-x)
    2. A list of string-terms of F(n)."""
def analyze_recurrence_equation(equation):
    associated = {}
    f_n_list = []
    equation = equation[5:len(equation)] # Remove the "s(n)="-part
    pos_s = equation.find("s(n-") # First position of recurrent part
    while pos_s >= 0: # There is another recurrent s(n-x) part
        debug_print(equation)
        step_length, equation = recurrent_step_length(equation, pos_s) # Determines step length and replaces recurrent part with a "1"
        debug_print(step_length)
        left_pos = search_left_term_begin(equation, pos_s, ["+", "-"])
        right_pos = search_right_term_end(equation, pos_s, ["+", "-"])
        c_n = equation[left_pos:right_pos + 1] # Substring with both indexes inclusive
        debug_print("c_n "+ c_n)
        equation = equation.replace(c_n, "", 1) # Remove the actual c_n from the equation (only once)
        associated[step_length] = c_n # Add the recursive step length and factor to the dictionary
        pos_s = equation.find("s(n-") # First position of recurrent part (because other "s(n-"-part is already removed)
    # Sorry, but you will have to implement the treatment of F(n) yourself!
    if equation != "" and equation != "+0":
        f_n_list = equation
    return associated, f_n_list

"""Reads in all lines of the file except the first, second and last one.
    The lines are returned as list of strings."""
def read_file(filename):
    lines = []
    with open(filename, "r") as input_file:
        for index, line in enumerate(input_file):
            if not (index in [0, 1]) and line != "];\n" and line != "\n": # Filter out first and second row and the last that contains "];\n"
                lines.append(line.strip()) # Append and remove leading and closing whitspaces
    return lines

"""Goes through all rows except the last and delete the "," at the end.
    The result is returned (again as list of strings)."""
def clear_commas(lines):
    for index, line in enumerate(lines):
        if index < len(lines) - 1: # This is not the last line
            comma_pos = len(line) - 1 # The last index position where the "," stands
            lines[index] = line[:comma_pos]
    return lines

"""Deletes all remaining whitespace and converts "^" to "**".
    The result is returned (again as list of strings)."""
def fix_syntax(lines):
    for index, line in enumerate(lines):
        line = str.replace(line, " ", "")
        line = str.replace(line, "^", "**")
        lines[index] = line
    return lines

"""Finds a closed formula for a homogeneous recurrence relation.
    The return value is a string of the right side of the equation "s(n) = ..."""
def solve_homogeneous_equation(init_conditions, associated):
    print("Starting homogeneous solver")
    # Create symbols for late usage
    x, y, z, a, b, c, d, e, f, g, h, k, l, m, n, o, p, q, r, s, t, u, v, w = sy.symbols(
        'x, y, z, a, b, c, d, e, f, g, h, k, l, m, n, o, p, q, r, s, t, u, v, w')
    # Write down characteristic equation for r
    eq_length = len(init_conditions)
    associated[0] = str('r^' + str(eq_length))
    for i in range(eq_length, 0, -1):
        if i in associated.keys() :
            associated[i] = associated[i] + str('*r^(') + str(eq_length) + str('-') + str(i) + str(')')
    print("Associated equation: " + str(associated))
    eq_string = ''
    for i in range(0, eq_length+1, 1):
        if i in associated.keys():
            if i < eq_length:
                eq_string = eq_string + associated[i] + '-'
            else:
                eq_string = eq_string + associated[i]
    print("Equation: " + eq_string)

    # Find the roots for r
    r_symbol = sy.Symbol('r')
    r_solutions = sy.solve(eq_string, r_symbol)
    r_length = len(r_solutions)
    print("Solutions: " + str(r_solutions))
    print("Eq length: " + str(eq_length) + " ; Amount of solutions: " + str(r_length))

    # If equation length is equal to solutions (the multiplicity is 1 for all roots)
    if eq_length == r_length:

        # Write down general solution (for solver)
        general_solution_matrix = []
        for item in r_solutions:
            item = (item)**n
            general_solution_matrix.append(item)
        print("General solution list: " + str(general_solution_matrix))

        # Generate system of equations
        system_of_equations = []
        for item in init_conditions:
            init_n = item
            init_solution = init_conditions[item]
            current_solution = []

            for i in general_solution_matrix:
                j = i.subs(n, init_n)
                current_solution.append(j)
            current_solution.append(int(init_solution))
            system_of_equations.append(current_solution)
        print("System of equations: " + str(system_of_equations))

        # Solve the system of equations
        solution_set = linsolve(sy.Matrix(system_of_equations), (x, y, z, a, b, c, d, e, f, g, h, k, l, m,
                                                                     o, p, q, r, s, t, u, v, w))
        solution = []
        for item in solution_set:
            solution = list(item)
        print("Solutions: " + str(solution))

        # Write the solution down as a string to return
        solution_full = ""
        for i in range(0, eq_length):
            if i > 0:
                solution_full = solution_full + " + "
            solution_full = solution_full + "(" + str(solution[i]) + ")" + "*" + "(" + str(r_solutions[i]) + ")" + "^n"
        print("Solved equation: " + solution_full)

    # If equation length is not equal to solutions (the multiplicity isn't 1 for all roots)
    else:
        # Because sympy.solve doesn't return the multiplicity you have to use sympy.roots
        r_solutions = sy.roots(eq_string, r_symbol)
        print("Solutions (/w mult): " + str(r_solutions))

        # Write down the general solution
        general_solution_matrix = []
        for item in r_solutions:
            multiplicity = r_solutions[item]
            for i in range(0, multiplicity):
                if i == 0:
                    general_solution_variable = (item ** n)
                    general_solution_matrix.append(general_solution_variable)
                else:
                    general_solution_variable = (item ** n) * (n ** i)
                    general_solution_matrix.append(general_solution_variable)
        print("General solution list: " + str(general_solution_matrix))

        # Create a system of equations for the initial values with the general solution
        system_of_equations = []
        for item in init_conditions:
            init_outcome = init_conditions[item]
            init_n = item
            current_solution = []

            for i in general_solution_matrix:
                j = i.subs(n, init_n)
                current_solution.append(j)
            current_solution.append(int(init_outcome))
            system_of_equations.append(current_solution)
        print("System of equations: " + str(system_of_equations))

        # Solve the system of equations
        solution_set = linsolve(sy.Matrix(system_of_equations), (x, y, z, a, b, c, d, e, f, g, h, k, l, m,
                                                                     o, p, q, r, s, t, u, v, w))
        solutions = []
        for item in solution_set:
            solutions = list(item)
        print("Solutions: " + str(solutions))

        # Write the solution down as a string to return
        solution_full = ""
        for i in range(0, len(general_solution_matrix)):
            if i > 0:
                solution_full = solution_full + " + "
            solution_full = solution_full + "((" + str(general_solution_matrix[i]) + ") * " + str(solutions[i]) + ")"
        print("Solved equation: " + solution_full)

    # Check the found solution with the initial values to see if the formula works (only for initial values)
    solution_check = []
    correct = True
    for item in init_conditions:
        init_conditions_solution = init_conditions[item]
        j = solution_full.replace("n", str(item))
        j = j.replace("^", "**")
        j = j.replace("sqrt", "math.sqrt")
        solution = eval(j)
        print("Solution with formula: " + str(solution) + "  Solution from init_conditions: " + str(init_conditions_solution))
        if not float(init_conditions_solution) - 1 / 1000 <= float(solution) <= float(init_conditions_solution) + 1 / 1000:
            correct = False
        solution_check.append([solution, init_conditions_solution])

    # Return the solution and the checks
    return solution_full, correct, solution_check

"""Finds a closed formula for a nonhomogeneous equation, where the nonhomogeneous part consists
    of a linear combination of constants, "r*n^x" with r a real number and x a positive natural number,
    and "r*s^n" with r and s being real numbers.
    The return value is a string of the right side of the equation "s(n) = ..."""
def solve_nonhomogeneous_equation(init_conditions, associated, f_n_list, homogeneous_type):
    print("Starting non-homogeneous solver")
    # Create symbols for late usage
    x, y, z, a, b, c, d, e, f, g, h, k, l, m, n, o, p, q, r, s, t, u, v, w = sy.symbols(
        'x, y, z, a, b, c, d, e, f, g, h, k, l, m, n, o, p, q, r, s, t, u, v, w')
    # Write down characteristic equation for r
    eq_length = len(init_conditions)
    associated[0] = str('r^' + str(eq_length))
    for i in range(eq_length, 0, -1):
        if i in associated.keys():
            associated[i] = associated[i] + str('*r^(') + str(eq_length) + str('-') + str(i) + str(')')
    print("Associated equation: " + str(associated))
    eq_string = ''
    for i in range(0, eq_length + 1, 1):
        if i in associated.keys():
            if i < eq_length:
                eq_string = eq_string + associated[i] + '-'
            else:
                eq_string = eq_string + associated[i]
    print("Equation: " + eq_string)

    # Find the roots for r
    r_symbol = sy.Symbol('r')
    r_solutions = sy.solve(eq_string, r_symbol)
    r_length = len(r_solutions)
    print("Solutions: " + str(r_solutions))
    print("Eq length: " + str(eq_length) + " ; Amount of solutions: " + str(r_length))

    # If equation length is equal to solutions (the multiplicity is 1 for all roots)
    if eq_length == r_length:

        # Write down general solution (for solver)
        homogeneous_general_solution_matrix = []
        for item in r_solutions:
            item = (item) ** n
            homogeneous_general_solution_matrix.append(item)
        print("General solution list: " + str(homogeneous_general_solution_matrix))

    # If equation length is not equal to solutions (the multiplicity isn't 1 for all roots)
    else:
        # Because sympy.solve doesn't return the multiplicity you have to use sympy.roots
        r_solutions = sy.roots(eq_string, r_symbol)
        print("Solutions (/w mult): " + str(r_solutions))

        # Write down the general solution
        homogeneous_general_solution_matrix = []
        for item in r_solutions:
            multiplicity = r_solutions[item]
            for i in range(0, multiplicity):
                if i == 0:
                    general_solution_variable = (item ** n)
                    homogeneous_general_solution_matrix.append(general_solution_variable)
                else:
                    general_solution_variable = (item ** n) * (n ** i)
                    homogeneous_general_solution_matrix.append(general_solution_variable)
        print("General solution list: " + str(homogeneous_general_solution_matrix))

    # Simplify fn
    fn = sy.simplify(f_n_list)
    print("Simplified fn: " + str(fn))
    # The associated homogeneous solution has been found, now the particular solution has to be calculated
    if homogeneous_type == "c":
        0
    if homogeneous_type == "e":
        0
    if homogeneous_type == "p":
        0

    # merge the two
    # TODO

    return 0

"""Transforms the string equation, that is of the right side of the form "s(n) = ...",
    and wirtes it towards the file "filename", which also needs to contain the desired path."""
def write_output_to_file(filename, equation):
    nr_written_chars = 0
    with open(filename, "w") as output_file:
        nr_written_chars = output_file.write("sdir := n -> {0};\n".format(equation))
    debug_print("Wrote {0} characters to file {1}.".format(str(nr_written_chars), filename))

"""Reformats the for Python needed syntax of equations back to specified output format:
    - "**" is transformed back to "^";
    - "sqrt(...)" is transformed back to "(...)^(1/2)".
    The return value is a string of the modified equation."""
def reformat_equation(equation):
    equation = equation.replace("**", "^")
    pos_sqrt = equation.find("sqrt(")
    while pos_sqrt >= 0:
        pos_end = search_right_term_end(equation, pos_sqrt + 5, [')'])
        equation = "{0}^(1/2){1}".format(equation[0:pos_end + 2], equation[pos_end + 2:])
        equation = equation.replace("sqrt", "", 1)
        pos_sqrt = equation.find("sqrt(")
    return equation

# Write down the solutions
solution_check_file = []

# Begin of program:
if len(sys.argv) > 3:
    print("Error: Illegal number of arguments.")
else:
    path = str(os.path.dirname(os.path.abspath(__file__)))
    print_debug_information = True
    print("Sys.arvg: " + str(sys.argv))
    if len(sys.argv) > 1:
        argv_index = 1
        if "-v" in sys.argv:
            print_debug_information = True
            if len(sys.argv) > 2:
                argv_index = 2
        elif "--verbose" in sys.argv:
            print_debug_information = True
            if len(sys.argv) > 2:
                argv_index = 2
        if sys.argv[argv_index].find("/") != -1:
            path = sys.argv[argv_index]
    print("Path: " + path)
    for filename in glob.glob(path + "\comass[0-9][0-9].txt"):
        print("File: "+filename)
        next_symbolic_var_index = 0 # Reset this index for every file
        debug_print("Beginning for file \"{0}\"".format(filename))
        lines = read_file(filename)
        lines = clear_commas(lines)
        lines = fix_syntax(lines)
        print("Len lines: " + str(len(lines)))
        debug_print(lines)
        # The following quick fix was done because some input files had two newlines at their end and the list "lines" thus may contain one empty line "" at the end
        tmp = len(lines)
        if lines[len(lines) - 1] == "":
            tmp -= 1
        init_conditions = det_init_conditions([lines[index] for index in range(1, tmp)]) # Determine initial conditions with all but the first line as input
        print("----------------Analyze the recurrence relation----------------")
        associated, f_n_list = analyze_recurrence_equation(lines[0])
        print("---------------------------------------------------------------")

        # Print debugging information:
        debug_print(filename)
        debug_print("Initial conditions:")
        debug_print(init_conditions)
        debug_print("Associated homogeneous recurrence relation:")
        debug_print(associated)
        debug_print("F(n):")
        if not f_n_list:
            print("Homogeneous equation")
        else:
            debug_print(f_n_list)

        output_filename = filename.replace(".txt", "-dir.txt")
        resulting_equ = ""
        # Check if the equation is a homogeneous relation
        if not f_n_list: # The list is empty
            resulting_equ, correct, solution_check = solve_homogeneous_equation(init_conditions, associated)
            solution_check_file.append([filename, resulting_equ, correct, solution_check])
        else:
            # Input for type of homogeneous equation. 'e' for exponential, 'p' for polynomial, 'c' for constant.
            # Any other value to skip this equation
            print("Currently solving " + filename)
            print("Type of equation (e for exponential, p for polynomial, c for constant, s for skip): ")
            homogeneous_type = input()
            if homogeneous_type == "e" or homogeneous_type == "p" or homogeneous_type == "c":
                resulting_equ = solve_nonhomogeneous_equation(init_conditions, associated, f_n_list, homogeneous_type)
                solution_check_file.append([filename, "TODO", False, "TODO"])
            else:
                resulting_equ = "a**n"
                solution_check_file.append([filename, "SKIPPED", False, "SKIPPED"])
        resulting_equ = reformat_equation(resulting_equ)
        write_output_to_file(output_filename, resulting_equ)

        debug_print("#################################\n")

    # Write the solution checker to a .csv file
    df = pandas.DataFrame(data=solution_check_file)
    df.to_csv("./calculated_solutions.csv", sep=';', index=False, header=["FileName", "Equation", "Correct", "Output"])

    print("Program is completely executed. There are no more recurrence relations to compute.")
