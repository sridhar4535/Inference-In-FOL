def main():
    textFile = open(sys.argv[2], 'r')
    outputFile = open('output.txt', 'w')
    number_queries = int(textFile.readline())
    queries = []
    kb = dict()
    for i in range(number_queries):
        goal = textFile.readline().strip()
        queries.append(goal)
    kb_size = int(textFile.readline())
    for i in range(kb_size):
        clause = textFile.readline().strip().replace(' ', '')
        standard_clause = clause
        if clause.find('>') != -1:
            split_clause = standard_clause.split('=>')
            split_clause[1] = standardize(split_clause[1], i)
            split_and_clause = split_clause[0].split('^')
            for j in range(0, len(split_and_clause)):
                split_and_clause[j] = standardize(split_and_clause[j], i)
            split_clause[0] = split_and_clause[0]
            for j in range(1, len(split_and_clause)):
                split_clause[0] += "^" + split_and_clause[j]
            clause = split_clause[0]+"=>"+split_clause[1]
        if clause.find('>') != -1:
            key = clause[clause.find('>') + 1:len(clause)]
            if key in kb:
                kb[key].append(clause[0:clause.find('>') - 1])
            else:
                kb[key] = [clause[0:clause.find('>') - 1]]
        else:
            kb[clause] = [TRUE]
    counter = 1
    for i in range(number_queries):
        #try:
        infinite.clear()
        if number_queries == counter:
            outputFile.write(FOL_BC_ASK(kb, queries[i]))
        else:
            outputFile.write(FOL_BC_ASK(kb, queries[i]) + '\n')
        counter += 1
        """except:
            if number_queries == counter:
                outputFile.write("FALSE")
            else:
                outputFile.write("FALSE" + '\n')
            counter +=1"""

FAILURE = 'FAILURE'
TRUE = 'TRUE'
FALSE = 'FALSE'
infinite = dict()

def standardize(clause, i):
    variables = []
    temp = [get_op(clause), '(']
    if get_args(clause):
        args = get_args(clause).split(",")
        for v in args:
            if is_variable(v):
                temp.append(v + str(i))
                temp.append(',')
                variables.append(v)
            else:
                temp.append(v)
                temp.append(',')
        temp[len(temp)-1] = ')'
        clause = "".join(temp)
    return clause

def unify(x, y, subst):
    if subst:
        if FAILURE in subst:
            return subst
    if x == y:
        return subst
    if is_variable(x):
        unify_var(x, y, subst)
    elif is_variable(y):
        unify_var(y, x, subst)
    elif is_compound(x) and is_compound(y):
        unify(get_op(x), get_op(y), subst)
        return unify(get_args(x), get_args(y), subst)
    elif is_list(x) and is_list(y):
        if x.count(')') > 0:
            first_a = x[0:x.find(')')+1]
            rest_a = x[x.find(')') + 2:len(x)]
        else:
            first_a = x[0:x.find(',')]
            rest_a = x[x.find(',') + 1:len(x)]
        if y.count(')') > 0:
            first_b = y[0:y.find(')')+1]
            rest_b = y[y.find(')') + 2:len(y)]
        else:
            first_b = y[0:y.find(',')]
            rest_b = y[y.find(',') + 1:len(y)]
        unify(first_a, first_b, subst)
        return unify(rest_a, rest_b, subst)
    else:
        subst[FAILURE] = FAILURE
        return subst

def unify_var(var, x, subst):
    if var in subst.keys():
        return unify(subst[var], x, subst)
    if occur_check(var, x, subst):
        subst[FAILURE] = FAILURE
        return subst
    else:
        subst[var] = x

def occur_check(var, x, s):
    if var == x:
        return True
    elif is_variable(x) and x in s:
        return occur_check(var, s[x], s)
    elif is_compound(x):
        return occur_check(var, get_op(x), s) or occur_check(var,
                get_args(x), s)
    else:
        return False

def substitution(var, x, s):
    if var == x:
        return True
    elif is_variable(x) and x in s:
        return substitution(var, s[x], s)
    elif is_compound(x):
        return substitution(var, get_op(x), s) or substitution(var,
                get_args(x), s)
    elif is_list(x):
        first_a = x[0:x.find(',')]
        rest_a = x[x.find(',') + 1:len(x)]
        return substitution(var, first_a, s) or substitution(var,
                rest_a, s)
    else:
        return False

def is_compound(x):
    if '(' in x:
        return True
    else:
        return False

def get_args(a):
    if is_compound(a):
        return a[a.find('(') + 1:len(a) - 1]

def get_op(a):
    return a[0:a.find('(')]

def is_list(x):
    if ',' in x:
        return True

def is_variable(x):
    if x.islower() and not is_list(x) and not is_compound(x):
        return True
    else:
        return False


def subst(subslist, x):
    args = get_args(x).split(',')
    for a in args:
        if is_compound(a):
            subst(subslist, x)
        elif is_variable(a):
            if a in subslist.keys():
                substitution_value = subslist[a]
                if is_variable(substitution_value) and substitution_value in subslist:
                    substitution_value = subslist[substitution_value]
                for n, i in enumerate(args):
                    if i == a:
                        args[n] = substitution_value
                x = get_op(x) + '(' + ','.join(args) + ')'
    return x

def substitute(subst, sentence):
    for key in subst:
        first_b = key
        rest_b = sentence
        if substitution(first_b, rest_b, subst):
            if is_variable(first_b) and first_b in subst:
                rest_b = rest_b[0:rest_b.find(first_b)] \
                    + subst[first_b] + rest_b[rest_b.find(first_b) + 1:]
        sentence = rest_b
    return sentence


def FOL_BC_ASK(kb, query):
    s = dict()
    s3 = FOL_BC_OR(kb, query, s)
    for s2 in s3:
        if FAILURE in s2:
            continue
        elif TRUE in s2 and FAILURE not in s2:
            return TRUE
    return FALSE

def updateList(s2):
    for (key, value) in s2.iteritems():
        if value in s2.keys():
            s2[key] = s2[value]
    return s2

def is_fact(goal):
    for i in get_args(goal).split(","):
        if is_variable(i):
            return False
    return True

def FOL_BC_OR(kb, goal, s):
    unify_list = []
    flag = False
    if goal in infinite:
        s[FAILURE] = FAILURE
        unify_list.append(s)
        return unify_list
    if is_fact(goal):
        infinite[goal] = TRUE
    if goal in kb and TRUE in kb[goal]:
        s[TRUE] = TRUE
        infinite.pop(goal, None)
        unify_list.append(s)
        return unify_list
    for (key, value) in kb.iteritems():
        if get_op(key) == get_op(goal):
            flag = True
            for val in value:
                s2 = dict()
                if val != TRUE:
                    unify(key, goal, s2)
                    FOL_BC_AND(kb, val, s2)
                else:
                    unify(key, goal, s2)
                    FOL_BC_AND(kb, goal, s2)
                if TRUE in s2 and not FAILURE in s2:
                    infinite.pop(goal, None)
                    s2.update(s)
                    updateList(s2)
                    unify_list.append(s2)
    if not flag or not unify_list:
        s[FAILURE] = FAILURE
        unify_list.append(s)
    return unify_list

def FOL_BC_AND(kb, goal, unify_list):
    if unify_list:
        if FAILURE in unify_list:
            return unify_list
    if not goal:
        return unify_list
    goals = goal.split("^")
    clause = goals[0]
    goals.remove(clause)
    rest = "^".join(goals)
    clause = subst(unify_list, clause)
    rest_list = FOL_BC_OR(kb, clause, unify_list)
    flag = True
    for l1 in rest_list:
        if rest and FAILURE not in l1:
            FOL_BC_AND(kb, rest, l1)
        if FAILURE not in l1 and TRUE in l1:
            unify_list.update(l1)
            updateList(unify_list)
            flag = False
    if flag:
        unify_list[FAILURE] = FAILURE
    return unify_list

main()
