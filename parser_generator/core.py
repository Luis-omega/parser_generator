from typing import NamedTuple, List, Tuple, Set, FrozenSet, Dict, Optional, Union, Generic, TypeVar
from typing import Deque
from itertools import chain
from collections import deque

from enum import Enum, auto

T = TypeVar("T")
T1 = TypeVar("T1")
T2 = TypeVar("T2")

class Shift(NamedTuple):
    state :int

class Reduce(NamedTuple):
    production : "Production"

class ShiftReduce(NamedTuple):
    conflicts : List[Union[Shift, Reduce]] = []

class ReduceReduce(NamedTuple):
    conflicts : List[Reduce] = []


class Accept():
    pass

class StateError():
    pass

TableState = Union[Shift, Reduce, Accept, StateError, ShiftReduce, ReduceReduce]

class Production(NamedTuple):
    name : int
    definition : Tuple[int, ...]

    def __contains__(self, other):
        return other in self.definition

    def to_string(self, grammar:"Grammar"):
        name = grammar.names[self.name]
        production_string = " ".join(map(lambda x: grammar.names[x], self.definition))
        return f"{name} -> {production_string} "


class Item(NamedTuple):
    production : Production
    dot : int
    look_ahead : Tuple[int, ...]

    def is_reduce(self):
        return self.dot == len(self.production.definition)

    def is_predicted(self):
        return self.dot==0

    def is_shift(self):
        return self.dot == len(self.production.definition) and (self.current())
    
    def is_kernel(self):
        return not self.is_predicted()

    def current(self):
        return self.production.definition[self.dot]

    def to_string(self, grammar: "Grammar"):
        name = grammar.names[self.production.name]
        pre_dot = " ".join(map(lambda x: grammar.names[x], self.production.definition[:self.dot]))
        pos_dot = " ".join(map(lambda x: grammar.names[x], self.production.definition[self.dot:]))
        return f"{name} -> {pre_dot} · {pos_dot}     {grammar.names[self.look_ahead[0]]}"


class Grammar:
    def __init__(self,
        productions: Dict[int, List[Production]],
        terminals: Set[int],
        names: List[str]
        ):
        self.productions = productions
        self.terminals = terminals
        self.names = names

        #we asume grammar names has the structure
        self.start = 0
        self.end = 1
        self.empty = 2

        #and grammar start production is the first 
        self.init = self.productions[self.start][0].definition

class GuardedSet(Generic[T]):
    def __init__(self, to_guard: Set[T]):
        self.guarded = to_guard
    
    def update(self, other):
        previus_len = len(self.guarded)
        self.guarded.update(other)
        new_len = len(self.guarded)
        return new_len != previus_len
            
    def add(self, other:T):
        previus_len = len(self.guarded)
        self.guarded.add(other)
        new_len = len(self.guarded)
        return new_len != previus_len

    def union(self, other: Set[T]):
        previus_len = len(self.guarded)
        self.guarded = self.guarded.union(other)
        new_len = len(self.guarded)
        return new_len != previus_len

    def __sub__(self, other: Union["GuardedSet[T]", Set[T]]):
        if isinstance(other, set):
            return self.guarded - other 
        return self.guarded - other.guarded

    def __contains__(self, other):
        return other in self.guarded

    def __iter__(self):
        return self.guarded.__iter__()

class Tree(Generic[T1, T2]):
    def __init__(self, data : T1, children : List["Tree[T1, T2]"]):
        self.data = data
        self.children = children
    
    def pretty(self, level:int, grammar:Grammar)->str:
        out = ["\n", " "*4*level, grammar.names[self.data]]
        for i in self.children:
            for j in i.pretty(level+1, grammar):
                out.append(j)
        return "".join(out)


        
        



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


def compute_first(grammar :Grammar )->Dict[int, GuardedSet[int]]:
    out : Dict[int, GuardedSet[int]] = dict(
            (i, GuardedSet(set())) for i in grammar.productions
        )
    added = True 
    while added:
        added = False
        for key,rule in grammar.productions.items():
            current_set = out[key]
            # rule = [production,...]
            for production in rule:
                # elem = Grammar symbol represented as int 
                for count,elem in enumerate(production.definition):
                    # add non empty terminal to first
                    if elem in grammar.terminals:
                        if (elem != grammar.empty) :
                            if not out[key].add(elem):
                                break
                            #a non empty terminal was added to first
                            added = True 
                    else :
                        elem_set = out[elem]
                        if current_set.update(elem_set-{grammar.empty}):
                            added = True 

                        if not grammar.empty in elem_set:
                            break

                if (count == len(production.definition)-1):
                    #terminal at end of production 
                    if (elem in grammar.terminals):
                        if (grammar.empty == elem):
                            if current_set.add(grammar.empty):
                                added = True
                    #nullable non terminal at end of production
                    elif grammar.empty in elem_set:
                        current_set.add(grammar.empty)
                        
    return out




def first(rules : Union[List[int], Tuple[int,...]], first_sets : Dict[int, GuardedSet[int]], grammar : Grammar)->GuardedSet[int]: 
    out : GuardedSet[int] = GuardedSet(set())
    for count, x in enumerate(rules) : 
        if x in grammar.terminals:
            if x == grammar.empty:
                continue 
            else : 
                out.add(x)
                break
        else : 
            elem_set = first_sets[x]
            out.update(elem_set- {grammar.empty})

    if count == len(rules)-1:
        if (x in grammar.terminals) :
            if (x == grammar.empty):
                out.add(grammar.empty)
        elif  (grammar.empty in elem_set):
            out.add(grammar.empty)
            
    return out


def follow(first_sets : Dict[int, GuardedSet[int]], grammar : Grammar)->Dict[int, GuardedSet[int]]: 
    out : Dict[int, GuardedSet[int]]= dict()
    for key in grammar.productions:
        out[key]=GuardedSet(set())
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
                                if out[x].update(union):
                                    added=True
                            else : 
                                if out[x].update(fsufix):
                                    added=True
                                    
                        else : 
                            production_follow = out[production.name]
                            if current.update(production_follow):
                                added=True
    return out


def clousure(C: List[Item], first_sets : Dict[int, GuardedSet[int]], grammar:Grammar)->List[Item]: 
    added = True
    while added:
        added = False
        #print(items2str(C, grammar))
        for item in C : 
            if not item.is_reduce():
                current_symbol = item.current()
                suffix = item.production.definition[item.dot+1:]
                #print(grammar.names[current_symbol], *map(lambda x: grammar.names[x], suffix))
                if current_symbol in grammar.terminals:
                    continue
                for production in grammar.productions[current_symbol]: 
                    #aux = first([*suffix,*item.look_ahead], first_sets, grammar)
                    for maybe_terminal in first([*suffix,*item.look_ahead], first_sets, grammar):
                        #print(aux)
                        if maybe_terminal in grammar.terminals:
                            to_add = Item(production, 0, (maybe_terminal,))
                            #print("TOAD ", items2str([to_add], grammar))
                            if not to_add in C:
                                C.append(to_add)
                                added = True
    return C

def primitive_goto(state: List[Item], symbol: int, first_sets: Dict[int, GuardedSet[int]], grammar: Grammar)->List[Item] :
    out : List[Item] = [] 
    for item in state:
        if not item.is_reduce():
            if item.current() == symbol:
                out.append(Item(item.production, item.dot+1, item.look_ahead))
    #print("PRECLOUSURE")
    #print(items2str(out, grammar))
    return clousure(out, first_sets, grammar)


def make_items(grammar: Grammar)->Tuple[List[List[Item]], Dict[int, GuardedSet[int]]]:
    #n = len(grammar.names)
    #grammar.names.append("NEW_START_SYMBOL")
    #grammar.productions[n] = [Production(n, (grammar.start,))]
    first_sets = compute_first(grammar)
    #C = [clousure([Item(grammar.productions[n][0],0, (grammar.end, ))],first_sets, grammar)]
    #print(items2str(C[0], grammar))

    #exit()
    C = [clousure(
                [
                    Item(n,0, (grammar.end, )) for n in (grammar.productions[grammar.start])
                ]
            ,first_sets, grammar)
        ]
    
    added = True
    #acc = 0
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
                goto = primitive_goto(I, symbol, first_sets, grammar)
                if goto and (not goto in C):
                    added = True
                    C.append(goto)
        #print(items2str(got, grammar))
        #exit()
        #acc+=1
    return C, first_sets


def make_table(grammar: Grammar)->Tuple[
        List[List[TableState]],
        List[List[Item]],
        Tuple[
            List[Optional[ShiftReduce]],
            List[Optional[ReduceReduce]],
            ]
    ]:
    states, firsts_sets = make_items(grammar)
    
    error_instance = StateError()

    table :List[List[TableState]] = [[error_instance for _ in range(len(grammar.names))] for _ in states]

    reduce_conflicts: List[Optional[ReduceReduce]] = []
    shift_conflicts: List[Optional[ShiftReduce]] = []

    for row, state in enumerate(states):
        for name in grammar.terminals:
            #print(row,name,  grammar.names[name])
            shift_state = primitive_goto(state, name, firsts_sets, grammar)
            if shift_state : 
                shift_value = states.index(shift_state)
                #print("done", shift_value)
                table[row][name]=Shift(shift_value)

        for rule_name in grammar.productions:
            shift_state = primitive_goto(state, rule_name, firsts_sets, grammar)
            if shift_state : 
                shift_value = states.index(shift_state)
                #print("done", shift_value)
                table[row][rule_name]=Shift(shift_value)


        #print(*map(lambda x : x.state if isinstance(x, Shift) else x.production if isinstance(x, Reduce) else "e" ,  table[row]))

        has_shift_conflicts = False
        has_reduce_conflicts = False
        new_conflict : Union[ReduceReduce, ShiftReduce]
        for item in state:
            if item.is_reduce():
                ahead = item.look_ahead[0]
                table_value =  table[row][ahead]
                maybe_new_value = Reduce(item.production)
                #print("hi", item.to_string(grammar), table_value)
                if isinstance(table_value , StateError):
                    #print("bye")
                    table[row][ahead] = maybe_new_value
                    #print(table[row][ahead])
                elif isinstance(table_value, Shift):
                    has_shift_conflicts = True
                    new_conflict = ShiftReduce([table_value, maybe_new_value])
                    shift_conflicts.append(new_conflict)
                elif isinstance(table_value, Reduce):
                    has_reduce_conflicts = True
                    new_conflict = ReduceReduce([table_value, maybe_new_value])
                    reduce_conflicts.append(new_conflict)
                elif isinstance(table_value, ShiftReduce):
                    table_value.conflicts.append(maybe_new_value)
                elif isinstance(table_value, ReduceReduce):
                    table_value.conflicts.append(maybe_new_value)

        if has_shift_conflicts:
            reduce_conflicts.append(None)
        elif has_reduce_conflicts:
            shift_conflicts.append(None)

    return table, states, (shift_conflicts, reduce_conflicts)

class Input:
    def __init__(self, tokens : List[Tree[int,int]], eof: int):
        self.tokens = tokens
        self.max_index = len(tokens)
        self.index = 0
        self.eof = Tree(eof, [])
        self.appends : Deque[Tree[int, int]] = deque([])

    def pop(self)->Tree[int,int]:
        if self.appends:
            return self.appends.popleft()
        if self.index < self.max_index : 
            self.index+=1
            return self.tokens[self.index-1]
        else : 
            return self.eof

    def add(self, new:Tree[int,int]):
        self.appends.append(new)
        

def show_stacks(stack : List[int], symbols:List[Tree[int, int]] , max_preview:int,  grammar)->str:
    if len(stack)==1:
        return str(stack[0])
    if len(stack)<=max_preview:
        max_preview = len(stack)-1
    out = [str(stack[len(stack)-max_preview-1])]
    for i,j in zip(stack[len(stack)-max_preview:], symbols[len(symbols)-max_preview:]):
        out.append(grammar.names[j.data])
        out.append(str(i))
    return " ".join(out)
            

def parse(tokens:List[Tree[int, int]], table : List[List[TableState]], grammar : Grammar):
    stream = Input(tokens, grammar.end)
    state_stack : List[int] = [0]
    symbol_stack : List[Tree[int, int]] = [] 
    next_symbol = Tree(-1, [])
    while (state_stack) :
        last_state = state_stack[-1]
        next_symbol = stream.pop()
        action = table[last_state][next_symbol.data]
        print(show_stacks(state_stack, symbol_stack, 7, grammar).ljust(20), grammar.names[next_symbol.data])
        # shift symbol from imput to symbol_stack  
        # reduce, pop stacks, make tree, and shift symbol or shift terminal
        if isinstance(action, Shift):
            state_stack.append(action.state)
            symbol_stack.append(next_symbol)
        elif isinstance(action, Reduce):
            stream.add(next_symbol)
            # make reduce
            n = len(action.production.definition)
            children = symbol_stack[len(state_stack)-n-1:]
            data = action.production.name
            tree = Tree(data, children)
            symbol_stack = symbol_stack[:-n]
            state_stack = state_stack[:-n]
            symbol_stack.append(tree)

            if data == grammar.start:
                break
            #make goto, since data is nonterminal the value of action must be shift
            action = table[state_stack[-1]][data]
            state_stack.append(action.state) #type: ignore
        elif isinstance(action, StateError):
            if next_symbol.data == grammar.end:
                msg = ["Unexpected end of input \n"]
            else : 
                msg = ["Unexpected terminal : ", grammar.names[next_symbol.data], "\n"]
            msg.append("The following terminals are expected \n")
            for symbol, action in enumerate(table[last_state]):
                if not isinstance(action, StateError):
                    msg+=["<", grammar.names[symbol], "> "]

            paths = find_lanes(table)
            symbols_examples = construct_examples(grammar)
            #for name,path in paths.items():
            #    print(name, *map(lambda x : examples[x][0][0], path))
            msg.append("\nA example of error is : \n")
            path = paths[last_state]
            example_prefix = "".join(map(lambda x : symbols_examples[x][0][0], path))
            example_prefix2 = "".join(map(lambda x : symbols_examples[x][-1][0], path))
            msg.append(example_prefix)
            if not next_symbol.data == grammar.end:
                msg.append(grammar.names[next_symbol.data])
            msg.append("\n")
            msg.append(" "*len(example_prefix))
            msg.append("^\n")
            if not example_prefix==example_prefix2:
                msg.append(example_prefix2)
                if not next_symbol.data == grammar.end:
                    msg.append(grammar.names[next_symbol.data])
                msg.append("\n")
                msg.append(" "*len(example_prefix2))
                msg.append("^")
            raise Exception("".join(msg))
        else :
            raise Exception("Unhandled case on parse")
    return symbol_stack[0].children[0]



def construct_examples(grammar : Grammar)->Dict[int, List[List[str]]]:
    solved = [(i, [grammar.names[i]]) for i in grammar.terminals]
    unsolved : List[Tuple[int, List[int]]] = []
    for name, rule in grammar.productions.items():
        for production1 in rule:
            unsolved.append((name, [*production1.definition]))
    modified = True
    production : List[Union[List[str], int]]
    while modified:
        modified = False
        for solved_name,value in solved:
            for unsolved_index, (unsolve_name, production) in enumerate(unsolved):
                if production:
                    for en, symbol in enumerate(production): 
                        if symbol == solved_name:
                            production[en] = value
                    is_solved = True
                    for symbol in production:
                        if not isinstance(symbol, list):
                            is_solved = False
                            break
                    if is_solved:
                        modified = True
                        concat :List[str] = []
                        for i in production:
                            concat+=i
                        solved.append((unsolve_name, [" ".join(concat)]))
                        unsolved[unsolved_index]=(unsolve_name, None)
                        

    out : Dict[int, List[List[str]]] = dict()
    for key, value in solved: 
        if not key in out : 
            out[key] = [value]
        else : 
            out[key].append(value)

    return out


def find_lanes(table:List[List[TableState]])->Dict[int, List[int]]:
    unvisited = {*range(1,len(table))}
    found = {0:[]}
    visited = {0}
    last_visited = {0}

    def all_children(state:int)->Set[Tuple[int,int]]:
        out = set()
        for i, value in enumerate(table[state]):
            if isinstance(value, Shift):
                out.add((i,value.state))
        return out
  
    while len(visited) != len(table):
        new_last_visited =set()
        for i in last_visited:
            for symbol, state in all_children(i):
                if not (state in found):
                    found[state] = found[i]+[symbol] 
                    new_last_visited.add(state)
        visited.update(last_visited)
        last_visited = new_last_visited
        
    return found
                        
                        

def test():
    names = ["S'", "#", "empty", "n", "-", "(", ")", "S", "E", "T"]
    names2int = dict((j,i) for i,j in enumerate(names))
    string_productions = [
        ["S'", "S", "#"],
        ["S", "E" ],
        ["E", "E", "-", "T"],
        ["E", "T"],
        ["T", "n"],
        ["T", "(", "E", ")"],
            ]

    string_non_terminals = set(x[0] for x in string_productions)
    string_terminals = [x for x in names if not (x in string_non_terminals)]

    rules = names2productions(string_productions, names2int)
    terminals = names2terminals(string_terminals, names2int)
    productions = rules_list2dict(rules)

    grammar = Grammar(productions, terminals, names)
    #f = first_on_rules(grammar)
    #items_sets, firsts_sets = make_items(grammar)

    table, states, conflicts = make_table(grammar)
    
    for count, state in enumerate(states) : 
        print(count, " {")
        for item in state:
            print("    ", item.to_string(grammar))
        print("}")


    out = []


    print("\n"*4)
    print("      ","  ".join(map(lambda x : x[:5].ljust(5), grammar.names)))
    for i, row in enumerate(table):
        out.append(str(i).ljust(5))
        for table_item in row : 
            if isinstance(table_item, StateError):
                out.append("e".ljust(5))
            elif isinstance(table_item, Shift):
                out.append("s{}".format(table_item.state).ljust(5))
            elif isinstance(table_item, Reduce):
                out.append("r{}".format(table_item.production.to_string(grammar)[:4]).ljust(5))
            elif isinstance(table_item, ShiftReduce):
                out.append("S/R{}".format(len(table_item.conflicts)).ljust(5))
            elif isinstance(table_item, ReduceReduce):
                out.append("R/R{}".format(len(table_item.conflicts)).ljust(5))
        print("  ".join(out))
        out=[]

    def totoken(s: List[str])->List[Tree[int, int]]:
        return [Tree(names2int[x], []) for x in s]
    string = [
       "(", "n" , "-"  ,"n" , "(", "(", "#"
    ]
    to_parse = totoken(string)
    #to_parse = [Tree(34343,[])]
    try : 
        parsed = parse(to_parse, table, grammar)
        print("".join(parsed.pretty(0, grammar)))
    except Exception as e:
        print(e)

    #samples = construct_examples(grammar)
    #for name, values in samples.items():
    #    print(grammar.names[name])
    #    for value in values :
    #        print("    ", value[0])

test()


        



