__author__ = "GODEFROY"
__filename__ = "DPLL.py"
__date__ = "04/11/20"

from copy import *
from random import *
import numpy as np


def maxliteral(C):
    # retour le litéral max(ca valeur non)( renvoie toujour un impaire)
    sup = 0
    for c in C:
        if max(c) > sup:
            sup = max(c)
    if sup % 2 == 0:
        return sup + 1
    else:
        return sup


################################################################################
# algo de simplification

def tierexclu(c):
    # prend en entré une clause et dis si il faut la suprimer(p ou nonp)
    for i in range(int((max(c) + 1) / 2)):
        if 2 * i in c and ((2 * i + 1) in c):
            return True
    return False


def simplifier(C):
    # prend en argument un ensemble de clause (liste d'ensemble) et
    # renvoie une version simplilifier"
    CNFs = []
    for i in range(len(C)):
        if tierexclu(C[i]):
            continue
        C2 = copy(C)
        del C2[i]
        cond = True
        for c2 in C2:
            if c2 <= C[i]:
                cond = False
        if cond:
            CNFs.append(C[i])
    return CNFs


################################################################################
# Base de données

def etatclause(C):
    return np.zeros(len(C))


def etatliteraux(C):
    return np.zeros(maxliteral(C) + 1)


def lgclause(C):
    # renvoie une liste avec la longeur de chaque clause
    return [len(c) for c in C]


################################################################################
# Heuristique de sélection de litéraux

def clauseuni(C):
    C1 = deepcopy(C)
    # revoie, si elle existe, une clause unitaire de l'ensemble de clause, None sinon
    for j in range(len(lgclause(C))):
        if lgclause(C1)[j] == 1:
            return C1[j].pop()


def literalpur(C):
    # renvoie si il existe, un litéral pur de l'ensemble de clause, None sinon
    for l in range(maxliteral(C) + 1):
        litpur = False
        for c in C:
            if l in c:
                litpur = True
                break
        if l % 2 == 0 and litpur:
            for c in C:
                if l + 1 in c:
                    litpur = False
        if l % 2 == 1 and litpur:
            for c in C:
                if l - 1 in c:
                    litpur = False
        if litpur:
            return l


def freq(C):
    # prend en entré un ensemble de clause et renvoie une liste
    # des fréquence des variables
    freq = [0 for i in range(maxliteral(C) + 1)]
    for c in C:
        for i in range(maxliteral(C) + 1):
            if i in c:
                freq[i] += 1
    return freq


def firstsatisfy(C):
    return freq(C).index(max(freq(C)))


def firstfail(C):
    litmax = firstsatisfy(C)
    if litmax % 2 == 0:
        return litmax + 1
    else:
        return litmax - 1


################################################################################
# Fonction pour l'algo DPLL

def assignation(C, l):
    # suprime les littéraux et les clauses nécessaires après une assignation
    newCNF = []
    for c in C:
        if l in c:
            continue
        if l % 2 == 0:
            x = c - {l + 1}
            if len(x) != 0:
                newCNF.append(x)
        else:
            x = c - {l - 1}
            if len(x) != 0:
                newCNF.append(x)
    return simplifier(newCNF)


def CNFf(C):
    # dis si une CNF est insatifaisable ( une clause p et une clause non p)
    for i in range(int((maxliteral(C) + 1) / 2)):
        if {2 * i} in C and {2 * i + 1} in C:
            return True
    return False


def estVide(C):
    # dis si un ensemble de clause est vide (si il donc satisfaisable)
    return len(C) == 0


def selction(C, h1, h2):
    # Prend en entré un ensemble de clause et renvoie(en utilisant les heuristiues
    # le litéral à utiliser
    uni = False
    if clauseuni(C) != None:
        uni = True
        return clauseuni(C), uni

    if literalpur(C) != None:
        return literalpur(C), uni
    if h1:
        return firstsatisfy(C), uni
    if h2:
        return firstfail(C), uni
    C1 = deepcopy(C)
    return choice(C1).pop(), uni


def litop(l):
    # renvoie le litéral oposée
    if l % 2 == 0:
        return l + 1
    else:
        return l - 1


def creationmod(iteration, nbvar):
    # à partir de la liste d'itération crée les models corespondants
    model = []
    mod = [0 for i in range(nbvar)]
    afect = [0 for i in range(nbvar)]
    for c in iteration:
        if c[0] % 2 == 0:
            mod[int(c[0] / 2)] = 1
            afect[int(c[0] / 2)] = 1
        else:
            afect[int((c[0] - 1) / 2)] = 1
    model.append(mod)
    nbmod = 2 ** (nbvar - len(iteration))
    for i in range(1, nbmod):
        newmod = copy(mod)
        nbin = ''.join(['0' for i in range(len(bin(nbmod - 1)[2:]) - len(bin(i)[2:]))]) + bin(i)[2:]
        p = 0
        for j in range(len(newmod)):
            if afect[j] == 0:
                newmod[j] = int(nbin[p])
                p += 1
        model.append(newmod)
    return model


def nbmod(iteration, nbvar):
    return 2 ** (nbvar - len(iteration))


# renvoie le literal a utiliser en cas de bactrack ET None si
# tout est exploré
def bactrack(iteration, etatlit):
    p = iteration.pop()
    cont = True
    lit = None
    newCNF = None
    uni = False
    while cont:
        if etatlit[litop(p[0])] == 0:
            cont = False
            lit = litop(p[0])
            newCNF = p[1]
        else:
            if len(iteration) == 0:
                cont = False
            else:
                etatlit[litop(p[0])] = 0
                etatlit[p[0]] = 0
                p = iteration.pop()
    return lit, newCNF, uni


################################################################################
# Algo DPLL

def DPLL(C, h1=False, h2=False, all=True):
    newCNF = simplifier(C)
    etatlit = etatliteraux(C)
    iteration = []
    model = 0
    nbvar = len(etatlit) / 2
    if estVide(newCNF):
        return "Tautologie"

    if CNFf(newCNF):
        return "Insatifaisable"

    lit, uni = selction(newCNF, h1, h2)

    iterat = True

    while iterat:

        iteration.append([lit, newCNF])

        newCNF = assignation(newCNF, lit)

        if uni:
            etatlit[lit] = 1
            etatlit[litop(lit)] = 1
        else:
            etatlit[lit] = 1

        if estVide(newCNF):
            if not all:
                return "satifaisable"
            model += nbmod(iteration, nbvar)
            lit, newCNF, uni = bactrack(iteration, etatlit)
            if lit == None:
                iterat = False

        elif CNFf(newCNF):
            lit, newCNF, uni = bactrack(iteration, etatlit)
            if lit == None:
                iterat = False
        else:
            lit, uni = selction(newCNF, h1, h2)
    if model == 0:
        return 'Insat'
    else:
        return 'Sat nb model= ' + str(model)

