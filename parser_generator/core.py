from typing import NamedTuple, List, Tuple, Set, FrozenSet, Dict, Optional, Union
from itertools import chain

from enum import Enum, auto

class ETable(Enum):
    shift = auto()
    reduce = auto()
    shift_reduce = auto()
    reduce_reduce = auto()
    invalid = auto()
    error = auto()

class Production(NamedTuple):
    name : int
    definition : Tuple[int, ...]

    def __contains__(self, other):
        return other in self.definition


class Item(NamedTuple):
    production : Production
    dot : int
    look_ahead : Tuple[int, ...]

    def is_at_end(self):
        return self.dot == len(self.production.definition)

    def current(self):
        return self.production.definition[self.dot]

    def to_string(self, grammar: "Grammar"):
        name = grammar.names[self.production.name]
        pre_dot = " ".join(map(lambda x: grammar.names[x], self.production.definition[:self.dot]))
        pos_dot = " ".join(map(lambda x: grammar.names[x], self.production.definition[self.dot:]))
        return f"{name} -> {pre_dot} · {pos_dot} {grammar.names[self.look_ahead[0]]}"

class Grammar:
    def __init__(self,
        start : int,
        productions: Dict[int, List[Production]],
        terminals: Set[int],
        empty: int,
        names: List[str]
        ):
        self.start = start
        self.productions = productions
        self.terminals = terminals
        self.names = names
        self.empty = empty
        self.input = len(names) 
        terminals.add(len(names))
        names.append("INPUT_SYMBOL")
        self.end = len(names)
        terminals.add(len(names))
        names.append("END_SYMBOL")



def rules_list2dict(rules: List[Production])-> Dict[int, List[Production]] :
    out: Dict[int, List[Production]] = dict()
    for rule in rules :
        if rule.name in out : 
            out[rule.name].append(rule)
        else :
            out[rule.name] = [rule]
    return out

def names2productions(productions:List[List[str]], name2int:List[str])->List[Production]:
    return [ Production(name2int[x[0]], tuple([name2int[y] for y in x[1:]])) for x in productions]

def names2terminals(terminals: List[str], name2int:List[str])->Set[int]:
    return set([name2int[i] for i in terminals])


def first_on_rules(grammar: Grammar)-> Dict[int, Set[int]]:
    out : Dict[int, Set[int]]= dict()
    productions = grammar.productions
    terminals = grammar.terminals
    for key in productions:
        out[key]=set()
    
    added = True
    while added:
        added=False
        for key,rule in productions.items():
            current_set = out[key]
            for production in rule:
                for count, elem in enumerate(production.definition):
                    if elem in terminals:
                        if (elem != grammar.empty) :
                            if not(elem in current_set):
                                out[key].add(elem)
                                added=True
                            break
                    else :
                        elem_set = out[elem]
                        elem_no_null = elem_set - {grammar.empty}
                        if not (elem_no_null <= current_set):
                            current_set.update(elem_no_null)
                            added=True
                        if not grammar.empty in elem_set:
                            break

                if (count == len(production.definition)-1):
                    #terminal at end of production 
                    if ((elem in terminals) and (grammar.empty == elem)) :
                        current_set.add(grammar.empty)
                    #nullable non terminal at end of production
                    elif grammar.empty in elem_set:
                        current_set.add(grammar.empty)


    return out


def first(rules : List[int], first_sets : Dict[int, Set[int]], grammar : Grammar)->Set[int]: 
    out = set()
    for count, x in enumerate(rules) : 
        if x in grammar.terminals:
            if x == grammar.empty:
                continue 
            else : 
                out.add(x)
                break
        else : 
            elem_set = first_sets[x]
            if grammar.empty in elem_set: 
                out.update(elem_set- {grammar.empty})
            else : 
                out.update(elem_set)
                break
    if count == len(rules)-1:
        if (x in grammar.terminals) :
            if (x == grammar.empty):
                out.add(grammar.empty)
        elif  (grammar.empty in elem_set):
            out.add(grammar.empty)
            
    return out


def follow(first_sets : Dict[int, Set[int]], grammar : Grammar)->Dict[int, Set[int]]: 
    out : Dict[int, Set[int]]= dict()
    for key in grammar.productions:
        out[key]=set()
    out[grammar.start].add(grammar.input)
    added = True
    while added:
        added=False
        for key,rule in grammar.productions.items():
            for production in rule:
                for count, x in enumerate(production.definition) : 
                    if not (x in grammar.terminals):
                        sufix = production.definition[count+1:]
                        current  = out[x]
                        if sufix:
                            fsufix = first(sufix, first_sets, grammar)
                            if grammar.empty in fsufix:
                                fsufix_no_empty =fsufix-{grammar.empty} 
                                production_follow = out[production.name]
                                union = fsufix_no_empty.union(production_follow)
                                if not (union <= current):
                                    added=True
                                    out[x].update(union)
                            else : 
                                if not (fsufix <= current):
                                    added=True
                                    out[x].update(fsufix)
                        else : 
                            production_follow = out[production.name]
                            if not (production_follow <= current):
                                added=True
                                current.update(production_follow)
    return out


def clousure(I: List[Item], first_sets : Dict[int, Set[int]], grammar:Grammar)->List[Item]: 
    C = I
    added = True
    while added:
        added = False
        #print(items2str(C, grammar))
        for item in C : 
            if not item.is_at_end():
                current_symbol = item.current()
                suffix = item.production.definition[item.dot+1:]
                #print(grammar.names[current_symbol], *map(lambda x: grammar.names[x], suffix))
                if current_symbol in grammar.terminals:
                    continue
                for production in grammar.productions[current_symbol]: 
                    aux = first([*suffix,*item.look_ahead], first_sets, grammar)
                    for maybe_terminal in first([*suffix,*item.look_ahead], first_sets, grammar):
                        #print(aux)
                        if maybe_terminal in grammar.terminals:
                            to_add = Item(production, 0, (maybe_terminal,))
                            #print("TOAD ", items2str([to_add], grammar))
                            if not to_add in C:
                                C.append(to_add)
                                added = True
    return C

def goto(state: List[Item], symbol: int, first_sets: Dict[int, Set[int]], grammar: Grammar):
    out = []
    for item in state:
        if not item.is_at_end():
            if item.current() == symbol:
                out.append(Item(item.production, item.dot+1, item.look_ahead))
    #print("PRECLOUSURE")
    #print(items2str(out, grammar))
    return clousure(out, first_sets, grammar)

def make_items(grammar: Grammar)->Tuple[List[List[Item]], Dict[int, Set[int]]]:
    #n = len(grammar.names)
    #grammar.names.append("NEW_START_SYMBOL")
    #grammar.productions[n] = [Production(n, (grammar.start,))]
    first_sets = first_on_rules(grammar)
    #C = [clousure([Item(grammar.productions[n][0],0, (grammar.end, ))],first_sets, grammar)]
    #print(items2str(C[0], grammar))

    #exit()
    C = [clousure([Item(n,0, (grammar.end, )) for n in (grammar.productions[grammar.start]) ],first_sets, grammar)]
    
    added = True
    acc = 0
    while added :
        added=False
        #for i,c in enumerate(C) :
        #    print("ITER ", acc, i)
        #    print(items2str(c, grammar))
        #if acc >0:
        #    exit()
        #current_len = len(C)
        for I in C: #[:current_len]: 
            for symbol in range(len(grammar.names)):
                #print(symbol)
                #print("Calll goto ", items2str(I, grammar))
                got = goto (I, symbol, first_sets, grammar)
                if got and (not got in C):
                    added = True
                    C.append(got)
        #print(items2str(got, grammar))
        #exit()
        acc+=1
    return C, first_sets


def make_table(grammar: Grammar):
    states, first_sets = make_items(grammar)
    action = [[(ETable.error,-1) for _ in range(len(grammar.names))] for _ in range(len(states))]
    got = [[-1 for _ in range(len(grammar.names))] for _ in range(len(states))]
    for i, state in enumerate(states):
        for rule_name in grammar.productions:
            new = goto(state, rule_name, first_sets, grammar)
            if new : 
                value = states.index(new)
                got[i][rule_name] =  value

    for i,state in enumerate(states) : 
        print(i, " {")
        print("    ", items2str(state, grammar))
        print("}")

    shifts : List[List[Tuple[ETable, int]]] = []
    reduces : List[List[Tuple[ETable, int]]]= []
    for i,state in enumerate(states):
        shifts.append([])
        reduces.append([])
        for item in state:
            if item.is_at_end():
                print(item.to_string(grammar), item.is_at_end())
                if action[i][item.look_ahead[0]][1] == -1 :
                    action[i][item.look_ahead[0]] = (ETable.reduce, (item.production.name, len(item.production.definition)))
                else:
                    reduces[-1].append((ETable.reduce, (item.production.name, len(item.production.definition))))
            else : 
                new = goto(state, item.look_ahead[0], first_sets, grammar)
                if new : 
                    value = states.index(new)
                    if action[i][item.look_ahead[0]][1] == -1 :
                        action[i][item.look_ahead[0]] = (ETable.shift, value)
                    else : 
                        shifts[-1].append((ETable.shift, value))
    return action, got, shifts, reduces


def items2str(state: List[Item], grammar: Grammar):
    out = []
    for it in state : 
        name = grammar.names[it.production.name]
        pre_dot = " ".join(map(lambda x: grammar.names[x], it.production.definition[:it.dot]))
        pos_dot = " ".join(map(lambda x: grammar.names[x], it.production.definition[it.dot:]))
        out.append(f"{name} -> {pre_dot} · {pos_dot} {grammar.names[it.look_ahead[0]]}")
    return "\n    ".join(out)

def test_ll1():
    names = ["!", "?", "(", ")", "STRING", "empty", "Session", "Question", "Fact", "Facts"]
    names2int = dict((j,i) for i,j in enumerate(names))
    string_productions = [
            ["Session", "Facts", "Question"],
            ["Session", "(", "Session", ")" , "Session"],
            ["Facts", "Fact", "Facts"],
            ["Facts", "empty"] ,
            ["Fact", "!", "STRING"],
            ["Question", "?", "STRING"]
            ]
    string_non_terminals = set(x[0] for x in string_productions)
    string_terminals = [x for x in names if not (x in string_non_terminals)]

    rules = names2productions(string_productions, names2int)
    terminals = names2terminals(string_terminals, names2int)
    productions = rules_list2dict(rules)

    grammar = Grammar(names2int["Session"], productions, terminals, names2int["empty"],names)
    f = first_on_rules(grammar)
    print(names2int)
    print(f)
    print(follow(f, grammar))

def test():
    names = ["n", "-", "(", ")", "S", "E", "T", "empty"]
    names2int = dict((j,i) for i,j in enumerate(names))
    string_productions = [
        ["S", "E" ],
        ["E", "E", "-", "T"],
        ["E", "T"],
        ["T", "n"],
        ["T", "(", "E", ")"],
            ]
    #names = ["S", "C", "c", "d", "empty"]
    #names2int = dict((j,i) for i,j in enumerate(names))
    #string_productions = [
    #        ["S", "C", "C"],
    #        ["C", "c", "C"],
    #        ["C", "d"],
    #        ]
    string_non_terminals = set(x[0] for x in string_productions)
    string_terminals = [x for x in names if not (x in string_non_terminals)]

    rules = names2productions(string_productions, names2int)
    terminals = names2terminals(string_terminals, names2int)
    productions = rules_list2dict(rules)

    grammar = Grammar(names2int["S"], productions, terminals, names2int["empty"],names)
    #f = first_on_rules(grammar)
    
    actions, got, shifts, reduces = make_table(grammar)

    out= []
    print("    "," ".join(map(lambda x : x[:5].ljust(5), grammar.names)))
    for i, row in enumerate(actions):
        out.append(str(i).ljust(4))
        for code, number in row : 
            if code == ETable.error:
                out.append("e".ljust(5))
            elif code == ETable.shift:
                out.append("s{}".format(number).ljust(5))
            elif code == ETable.reduce:
                rule_name, lenght = number
                out.append("r{}".format(grammar.names[rule_name]).ljust(5))
        print(" ".join(out))
        out=[]

    for row in got:
        print("   "," ".join(map(lambda x : str(x).ljust(5), row)))
    



    

test()


        



