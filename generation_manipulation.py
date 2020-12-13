########################################################################################################################
# Projet L3 - Solveur SAT                                                                                              #
# Semestre 5 - 2020 / 2021                                                                                             #
# Verrecchia Thomas                                                                                                    #
# Godefroy Théo                                                                                                        #
########################################################################################################################

"Group together a range of function to generate, import and export CNF"

from random import*
import csv

# Tools
########################################################################################################################

def calc_diagonal(i,j,n) :
    """
    A tool we will use with the queen generator

    :param i: The column where we start the diagonal.
    :param j: The row where we start the diagonal.
    :param n: The lenght of the diagonal.
    :return: A list of tuple representing every cell of the diagonal.
    """

    output = [[i,j]]
    for k in range(n-1) :
        i += 1
        j += 1
        output += [[i,j]]
    return output

def calc_anti_diagonal(i,j,n) :
    """
    A tool we will use with the queen generator

    :param i: The column where we start the anti-diagonal.
    :param j: The row where we start the anti-diagonal.
    :param n: The lenght of the diagonal.
    :return: A list of tuple representing every cell of the anti-diagonal.
    """

    output = [[i,j]]
    for k in range(n-1) :
        i = i - 1
        j += 1
        output += [[i,j]]
    return output

def add_clause_from_diagonal(nb_qn,clauses) :
    """
    A tool we use with the queen generator

    :param nb_qn: The number of column.
    :param clauses: The previous list of clauses
    :return: nothing, It add directly the new clauses to the previous ones.
    """

    lenght_diagonal = nb_qn - 1                                                                           # Diagonal sup
    for k in range(1, nb_qn - 1):
        diagonal = calc_diagonal(k, 0, lenght_diagonal)
        for m in range(len(diagonal)):
            x_i_k = (diagonal[m][0] * (nb_qn) * 2) + (diagonal[m][1] * 2) + 1
            for l in range(m + 1, len(diagonal)):
                x_j_k = (diagonal[l][0] * (nb_qn) * 2) + (diagonal[l][1] * 2) + 1
                clause = {x_i_k, x_j_k}
                clauses += [clause]
        lenght_diagonal = lenght_diagonal - 1

    lenght_diagonal = nb_qn                                                                      # Diagonal mean and inf
    for k in range(nb_qn):
        diagonal = calc_diagonal(0, k, lenght_diagonal)
        for m in range(len(diagonal)):
            x_i_k = (diagonal[m][0] * (nb_qn) * 2) + (diagonal[m][1] * 2) + 1
            for l in range(m + 1, len(diagonal)):
                x_j_k = (diagonal[l][0] * (nb_qn) * 2) + (diagonal[l][1] * 2) + 1
                clause = {x_i_k, x_j_k}
                clauses += [clause]
        lenght_diagonal = lenght_diagonal - 1

    lenght_diagonal = nb_qn                                                                 # Anti-diagonal mean and inf
    for k in range(nb_qn):
        diagonal = calc_anti_diagonal((nb_qn - 1), k, lenght_diagonal)
        for m in range(len(diagonal)):
            x_i_k = (diagonal[m][0] * (nb_qn) * 2) + (diagonal[m][1] * 2) + 1
            for l in range(m + 1, len(diagonal)):
                x_j_k = (diagonal[l][0] * (nb_qn) * 2) + (diagonal[l][1] * 2) + 1
                clause = {x_i_k, x_j_k}
                clauses += [clause]
        lenght_diagonal = lenght_diagonal - 1

    lenght_diagonal = 2                                                                              # Anti-diagonal sup
    for k in range(1, nb_qn-1):
        diagonal = calc_anti_diagonal(k, 0, lenght_diagonal)
        for m in range(len(diagonal)):
            x_i_k = (diagonal[m][0] * (nb_qn) * 2) + (diagonal[m][1] * 2) + 1
            for l in range(m + 1, len(diagonal)):
                x_j_k = (diagonal[l][0] * (nb_qn) * 2) + (diagonal[l][1] * 2) + 1
                clause = {x_i_k, x_j_k}
                clauses += [clause]
        lenght_diagonal = lenght_diagonal + 1



# Generators
########################################################################################################################

def generate_randomly(nb_cl_inf = 0, nb_cl_sup = 10, lg_cl_min = 0, lg_cl_sup = 10, nb_pv_min = 0, nb_pv_max = 10 ) :
    """
    :param nb_cl_inf: Inferior bound for the number of clauses.
    :param nb_cl_sup: Superior bound for the number of clauses.
    :param lg_cl_min: Inferior bound for the number of literals in each clause.
    :param lg_cl_sup: Superior bound for the number of literals in each clause.
    :param nb_pv_min: Inferior bound for the number of propositional variables.
    :param nb_pv_max: Superior bound for the number of propositional variables.
    :return: A list composed of as many sub set as clauses composed randomly.
    """
    output = []
    nbr_lit = ( max(2*randint(nb_pv_min,nb_pv_max) - 1, 0 ))
    nbr_cl = randint(nb_cl_inf,nb_cl_sup)
    for clauses in range(nbr_cl):
        clause = set()
        lg_cl = randint(lg_cl_min,lg_cl_sup)
        if lg_cl != 0 :
            for literals in range(lg_cl) :
                literal = randint(0,nbr_lit)
                clause.add(literal)
            output += [clause]
    return output

def generate_pigeon(nb_pg, nb_dc) :
    """
    :param nb_pg: The number of pigeons.
    :param nb_dc: The number of Dovecote.
    :return: A list of as many sub set as clauses representing the pigeon's problem.

    Each propositional variable is associated with a number using the following rule:
    If nb_pg is the number of pigeon ( starting at 0 ), nb_dc the number of dovecote and P(i,j) meaning the pigeon i
    is in the dovecote j ( starting at 0 ),
    P(i,j) correspond to the number x = (i*(nb_dc)*2) + (j*2) and !P(i,j) correspond to y = x+1
    """
    clauses = []
    for i in range(nb_pg) :                                                 # Each pigeon must enter one single Dovecote
        list_clause = []
        for j in range(nb_dc) :
            x = (i*(nb_dc)*2) + (j*2)
            list_clause += [x]
            clause = set(list_clause)
        clauses += [clause]
    for i in range(nb_pg) :                                                       # Each pigeon is in 1 dovecote or less
        for j in range(nb_dc) :
            x_i_j = (i*(nb_dc)*2) + (j*2) + 1
            for k in range(j+1,nb_dc) :
                x_i_k = (i*(nb_dc)*2) + (k*2) + 1
                clause = {x_i_j,x_i_k}
                clauses += [clause]
    for k in range(nb_dc) :                                                # Each dovecote must contain 1 pigeon or less
        for i in range(nb_pg) :
            x_i_k = (i*(nb_dc)*2) + (k*2) + 1
            for j in range(i+1,nb_pg) :
                x_j_k = (j*(nb_dc)*2) + (k*2) + 1
                clause = {x_i_k,x_j_k}
                clauses += [clause]
    return clauses

def generate_queen(nb_qn):
    """
    :param nb_qn: The number of queen
    :return: A list of as many sub set as clauses representing the queen's problem.

    We have as many queen as column so we each queen is placed on a column.
    If nb_qn is the number of queen ( starting at 0 ) and P(i,j) meaning the queen from the column i is on the row j.
    P(i,j) correspond to the number x = (i*(nb_qn)*2) + (j*2) and !P(i,j) correspond to y = x+1
    """
    clauses = []
    for i in range(nb_qn) :                                                       # Each queen must be in at least 1 row
        list_clause = []
        for j in range(nb_qn) :
            x = (i*(nb_qn)*2) + (j*2)
            list_clause += [x]
            clause = set(list_clause)
        clauses += [clause]
    for i in range(nb_qn) :                                                             # Each queen is on 1 row or less
        for j in range(nb_qn) :
            x_i_j = (i*(nb_qn)*2) + (j*2) + 1
            for k in range(j+1,nb_qn) :
                x_i_k = (i*(nb_qn)*2) + (k*2) + 1
                clause = {x_i_j,x_i_k}
                clauses += [clause]
    for k in range(nb_qn) :                                                      # Each row must contain 1 queen or less
        for i in range(nb_qn) :
            x_i_k = (i*(nb_qn)*2) + (k*2) + 1
            for j in range(i+1,nb_qn) :
                x_j_k = (j*(nb_qn)*2) + (k*2) + 1
                clause = {x_i_k,x_j_k}
                clauses += [clause]
    add_clause_from_diagonal(nb_qn,clauses)                        # Each diagonal must contain one queen or less
    return clauses


# Import / Export
########################################################################################################################

def export_csv(CNF,fname) :
    """
    :param CNF: A CNF
    :param fname: the Name of the csv file
    :return: Save the CNF in a csv
    """
    file = open(fname,"w")
    writer = csv.writer(file,delimiter = ',')
    for clauses in range(len(CNF)) :
        clause = CNF[clauses]
        list = ["C"+str(clauses), ":"]
        for literal in clause :
            list += [literal]
        writer.writerow(list)
    file.close()

def import_csv(fname) :
    """
    :param fname: the Name of the csv file
    :return: A list composed of as many sub set as clauses
    """
    file = open(fname, "r")
    reader = csv.reader(file, delimiter=',')
    output = []
    for row in reader:
        if row != []:
            del row[0]
            del row[0]
            clause_list = [int(i) for i in row]
            clause = set(clause_list)
            output += [clause]
    return output

# For Display purposes ONLY
########################################################################################################################
""" Export the CNF in a purely ornemental csv we can't use anymore but it's more readable   """

def export_display_csv(CNF,fname) :
    """
    :param CNF: A CNF
    :param fname: the Name of the csv file
    :return: Save CNF in an ornemental csv
    DO NOT USE FOR AN OTHER PURPOSE THAN DISPLAYING THE CNF
    """
    file = open(fname,"w")
    writer = csv.writer(file,delimiter = ' ')
    for clauses in range(len(CNF)) :
        clause = CNF[clauses]
        list = ["C"+str(clauses), ":"]
        for literal in clause :
            list += [literal]
            list += ["v"]
        list.pop()
        writer.writerow(list)
    file.close()


