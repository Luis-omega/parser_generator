from typing import NamedTuple, List, Tuple, Set, FrozenSet, Dict, Optional, Union
from itertools import chain

from enum import Enum, auto

class ETable(Enum):
    shift = auto()
    reduce = auto()
    shift_reduce = auto()
    reduce_reduce = auto()
    invalid = auto()


class Production(NamedTuple):
    name : int
    definition : Tuple[int, ...]
    terminal : bool = False

    def __contains__(self, other):
        return other in self.definition

class Item(NamedTuple):
    production : Production
    dot : int
    look_ahead : Tuple[int, ...]

    def __eq__(self, other):
        return (self.dot == other.dot) and (self.production == other.production)

    def is_at_end(self):
        return self.dot == len(self.production.definition)

    def current(self):
        return self.production.definition[self.dot]



def list2dict(rules: List[Production])-> Dict[int, List[Production]]:
    out: Dict[int, List[Production]] = dict()
    for rule in rules :
        if rule.name in out : 
            out[rule.name].append(rule)
        else :
            out[rule.name] = [rule]
    return out
        



def clousure( items : List[Item], rules : Dict[int, Production], debug = None)-> List[Item]:
    C = items 
    added_new = True
    while added_new : 
        added_new = False
        for item in C : 
            if (not item.production.terminal) and (not item.is_at_end()):
                for rule in rules[item.current()]:
                    if not rule.terminal:
                        new = Item(rule, 0, (0,))
                        if not (new in C) :
                            added_new = True
                            C.append(new)
    return C


    
def primitive_goto(items: List[Item], start : int,
        rules : Dict[int, Production], debug = None):
    initial : List[Item] = []
    for item in items : 
        if (not item.production.terminal) and ( not item.is_at_end()):
            if item.current() == start:
                new = Item(item.production, 
                    item.dot+1, item.look_ahead)
                if not new in initial:
                    initial.append(new)
    return clousure(initial, rules, debug)

def check_state_conflicts(state : List[Item])->Tuple[List[Item],List[Item],List[Item]]:
    shifts = []
    reduces = []
    for item in state:
        if item.is_at_end():
            reduces.append(item)
        else : 
            shifts.append(item)

    if shifts and (not reduces):
        return shifts, [], []
    elif reduces and (not shifts):
        rule_name = reduces[0].production.name
        reduce_conflicts = [reduces[0]]
        for item in reduces:
            if item.production.name != rule_name:
                reduce_conflicts.append(item)
        if len(reduce_conflicts)>1:
            #reduce reduce conflict
            return [], reduces,reduce_conflicts
        else :
            return [], reduces,[]
    else : 
        #shift reduce conflict 
        return shifts, reduces, []


def check_and_add_state(
        state: List[Item],
        states: List[List[Item]],
        shifts: List[Tuple[int, List[Item], List[Item]]], 
        reduces: List[Tuple[int, List[Item]]],
        is_reduce:List[ETable],
        table:List[List[Optional[int]]]
    ):
    try : 
        go_to = states.index(state)
        table[-1].append(go_to)
    except: 
        shifts2, reduces2, reduce_conflicts = check_state_conflicts(state)
        if shifts2 and reduces2:
            shifts.append((len(states), shifts2, reduces2))
            is_reduce.append(ETable.shift_reduce)
        elif reduce_conflicts:
            reduces.append((len(states), reduce_conflicts))
            is_reduce.append(ETable.reduce_reduce)
        else : 
            if reduces2:
                is_reduce.append(ETable.reduce)
            else : 
                is_reduce.append(ETable.shift)
        states.append(state)
        table[-1].append(len(states)-1)
    return

def make_action_goto_table(
        table:List[List[Optional[int]]],
        is_reduce:List[ETable],
        states: List[List[Item]]
        ):
    end_table = []
    for row, status, state in zip(table, is_reduce, states) : 
        # At this point we al ready verify that shift and reduce are free of conlflicts
        if status == ETable.reduce:
            # state must be of len 1 or else we have a reduce/reduce confict (or a repeated item in state)
            new_row = [(ETable.reduce, (state[0].production.name, len(state[0].production.definition))) for _ in row]
        elif status == ETable.shift : 
            new_row = [(ETable.shift, i) for i in row ]
        elif status == ETable.shift_reduce:
            new_row = []
            for i,value in enumerate(row) : 
                if value:
                    new_row.append((ETable.shift_reduce,value))
                else : 
                    new_row.append((ETable.shift_reduce,-1))
        elif status == ETable.reduce_reduce:
            new_row = [(ETable.reduce_reduce,0) for _ in row]
        end_table.append(new_row)
    return end_table


def compute_states(start : Item, rules: Dict[int, Production], 
        grammar_symbols, debug = None):
    states = [clousure([start], rules, debug)]
    table : List[List[Optional[int]]]= []
    shifts: List[Tuple[int, List[Item], List[Item]]] = []
    reduces: List[Tuple[int, List[Item]]] = []
    is_reduce : List[ETable]= [ETable.shift] #this Shift is a hack, we need to add  a correct check for state 0
    old_index = 0
    added_new = True
    while added_new:
        added_new = False
        start_index = old_index
        old_index = len(states)
        for i, items in enumerate(states[start_index:]):
            if is_reduce[i+start_index] == ETable.reduce:
                table.append([None for _ in grammar_symbols])
                continue
            else : 
                table.append([])
            #table.append([])
            for symbol in grammar_symbols:
                if (state := primitive_goto(items, symbol, rules, debug)):
                    check_and_add_state(
                        state, 
                        states,
                        shifts, 
                        reduces,
                        is_reduce,
                        table
                    )
                    added_new = True
                    #try : 
                    #    go_to = states.index(state)
                    #    table[-1].append(go_to)
                    #except: 
                    #    shifts, reduces, reduce_conflicts = check_state(state)
                    #    if shifts and reduces:
                    #        conflicts_shift.append((len(states), shifts, reduces))
                    #        is_reduce.append(ETable.shift_reduce)
                    #    elif reduce_conflicts:
                    #        conflicts_reduce.append((len(states), reduce_conflicts))
                    #        is_reduce.append(ETable.reduce_reduce)
                    #    else : 
                    #        if reduces:
                    #            is_reduce.append(ETable.reduce)
                    #        else : 
                    #            is_reduce.append(ETable.shift)
                    #    states.append(state)
                    #    table[-1].append(len(states)-1)
                    #    added_new = True
                else :
                    table[-1].append(None)
    end_table = make_action_goto_table(table, is_reduce, states)
    #end_table = []
    #for row, status,state in zip(table, is_reduce, states) : 
    #    # At this point we al ready verify that shift and reduce are free of conlflicts
    #    if status == ETable.reduce:
    #        # state must be of len 1 or else we have a reduce/reduce confict (or a repeated item in state)
    #        new_row = [(ETable.reduce, state[0].production.name) for _ in row]
    #    elif status == ETable.shift : 
    #        new_row = [(ETable.shift, i) for i in row ]
    #    elif status == ETable.shift_reduce:
    #        new_row = []
    #        for i,value in enumerate(row) : 
    #            if value:
    #                new_row.append((ETable.shift_reduce,value))
    #            else : 
    #                new_row.append((ETable.shift_reduce,-1))
    #    elif status == ETable.reduce_reduce:
    #        new_row = [(ETable.reduce_reduce,0) for _ in row]
    #    end_table.append(new_row)
    return states, end_table, (shifts, reduces)
                        


def find_expressions_for_rules(rules : Dict[int, List[Production]]):
    solved : Dict[int, List[int]] = dict()
    unsolved : Dict[int, List[List[int]]] = dict()
    for name, productions in rules.items() : 
        if productions[0].terminal :
            solved[name] = [name]
        else : 
            ref : List[List[int]] = []
            unsolved[name] = ref
            for i in productions:
                ref.append([* (i.definition)]) 
    

    def subs(ps: List[List[int]], key : int, value: List[int]):
        for p in ps:
            for i,val in enumerate(p):
                if val == key:
                    p[i] = value
        return

    def is_solved(ps: List[List[Union[List[int], int]]])->Optional[List[int]]:
        for p in ps:
            has_int = False
            for val in p:
                if isinstance(val, int):
                    has_int = True
            if not has_int:
                out : List[int] = []
                for w in p : 
                    out+=w
                return out
        return None

    cant_solve = False
    while unsolved:
        to_delete = []
        for name,rule in unsolved.items(): 
            for solution_name ,solution in solved.items() : 
                subs(rule, solution_name, solution)
            msolved = is_solved(rule)
            if not (msolved is None): 
                solved[name] = msolved
                to_delete.append(name)
                continue

        for name in to_delete:
            unsolved.pop(name)

        if not to_delete:
            cant_solve = True
            break

    return solved, cant_solve

def find_path(state1: int, state2: int, table:List[List[Tuple[ETable, int]]])->List[int]:

    visited: List[int] = []
    paths: List[List[int]] = [[state1]]
    added_new = False

    while added_new : 
        for path in paths : 
            top = path[-1]
            new_paths = []
            for status, next_state in table[top]:
                if (status == ETable.shift) and (next_state) and (not next_state in visited):
                    if next_state == state2:
                        path.append(state2)
                        return path
                    new_paths.append(path.copy())
                    new_paths[-1].append(next_state)
                    added_new = True
            visited.appen(top)
        paths = new_paths
                
    return []

def find_childs(state : int, table:List[List[Tuple[ETable, int]]])->List[List[int]]:
    out : List[List[int]] = [[state]]

    def is_in(key:int, l:List[List[int]])->bool:
        for deep in l: 
            if key in deep:
                return True
        return False

    while out[-1]: 
        out.append([])
        for state in out[-2]:
            row = table[state]
            # skip reduce case since all the row would be a reduce.
            if row[0][0] != ETable.shift:
                continue
            for status,value in row : 
                if (status == ETable.shift) and (value) and (not is_in(value,out)) :
                    out[-1].append(value)
    out.pop()
    return out

def find_valid_values(state : int, table:List[List[Tuple[ETable, int]]])->List[int]:
    children = find_childs(state, table)
    values : Set[int] = set()
    for deep, deep_values in enumerate(children[1:]):
        for c in deep_values : 
            # Reduce elements of table has 
            # table[c] = [(status, (rule_name, production_len)) for _ in range(len(table[c]))]
            status, value = table[c][0]
            if status == ETable.reduce:
                if deep+1 == value[1]:
                    values.add(value[0])
    return  [i for i in values]

                    
                
            


def test(a:int)->None:
    names = ["S", "E", "$", "-", "T", "n", "(", ")"]
    nmap: Dict[str, int] = dict()
    for i,name in  enumerate(names):
        nmap[name] = i
    rules = list2dict([
            Production(nmap["S"], (nmap["E"], nmap["$"])),
            #Production(nmap["S"], (nmap["E"],)),
            Production(nmap["E"], (nmap["E"], nmap["-"], nmap["T"])),
            Production(nmap["E"], (nmap["T"],)),
            Production(nmap["T"], (nmap["n"],)),
            Production(nmap["T"], (nmap["("], nmap["E"], nmap[")"])),
            Production(nmap["n"], (0,), True),
            Production(nmap["-"], (0,), True),
            Production(nmap["$"], (0,), True),
            Production(nmap["("], (0,), True),
            Production(nmap[")"], (0,), True),
    ])
    #dic = Map(names, nmap)
    #logg.debug("Grammar : \n%s", dic.rules2str(rules))
    #logg.debug("Names to Int \n%s", nmap)
    #logg.debug("Compute States")
    states, table, conflicts= compute_states(
            Item(rules[nmap["S"]][0], 0, (0, )), rules,
            grammar_symbols = [i for i,j in enumerate(names)], debug=None)
    for i,state in enumerate(states) : 
        print(i,"{")
        for item in state : 
            pre_dot = " ".join(map(lambda x: names[x], item.production.definition[:item.dot]))
            pos_dot = " ".join(map(lambda x: names[x], item.production.definition[item.dot:]))
            name = names[item.production.name]
            print(f"    {name} -> {pre_dot} · {pos_dot} {item.look_ahead}")
        print("}")

    #Purge states

    non_terminals : List[int] = []

    for p in rules.values():
        if not p[0].terminal : 
            non_terminals.append(p[0].name)

    for number, row in enumerate(table) : 
        if row[0][0] == ETable.reduce:
            continue
        valid_values = find_valid_values(number, table)
        for mark in non_terminals:
            code, state = row[mark]
            if (code == ETable.shift) and ((state is None) and (not mark in valid_values)):
                table[number][mark] = (ETable.invalid, None)

    print("  ",end="")
    for name in names:
        print(name,"     ", end="")
    print()
    for i, row in enumerate(table):
        to_print=[]
        for code, state in row: 
            if code ==ETable.reduce:
                to_print.append("r{}".format(state).ljust(5))
            elif code ==ETable.shift:
                if state: 
                    to_print.append("s{}".format(state).ljust(5))
                else : 
                    to_print.append("e    ")
            elif code == ETable.shift_reduce:
                if state >-1:
                    to_print.append("sR{}".format(state).ljust(4))
                else : 
                    to_print.append("R/S  ")
            elif code == ETable.reduce_reduce:
                to_print.append("R/R  ")
            elif code == ETable.invalid:
                to_print.append("inv  ")

        print(i, "  ".join(to_print))

    expression, status = find_expressions_for_rules(rules)
    print(expression)
    for name, coded in expression.items(): 
        rule_name = names[name] 
        to_print = []
        for value in coded : 
            to_print.append(names[value])
        print(f"{rule_name} = {''.join(to_print)}")

    

    for i, row in enumerate(table):
        for code, state in row: 
            if code ==ETable.shift:
                if  not state: 
                    find_path(i, state, table):
                    
        

    








test(1)
