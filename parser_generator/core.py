from typing import Union, Callable, List, TypeVar, Generic, Dict, Tuple, Optional
import logging as logg

logg.basicConfig(format="", level=logg.DEBUG)

T = TypeVar("T")
T2 = TypeVar("T2")


# 1 -> 1 2 3 4  is Rule(1, [1,2,3,4])
# 1-> epsilon is Rule(1,[])
# 1 is terminal is Rule(1, None)

class Rule:
    def __init__(self, name:int, definition : Optional[List[int]]):
        self.name = name
        self.definition = definition

    def __contains__(self, other):
        return other in self.definition

    def __eq__(self, other):
        return (self.name == other.name ) and (self.definition == other.definition)

    def is_terminal(self):
        return self.definition is None

    def __str__(self):
        return f"{self.name} -> {self.definition}"

    def __repr__(self):
        return str(self)

    def __getitem__(self, k)-> Optional[int]:
        if self.definition:
            return self.definition[k]
        return None

class Rules : 
    def __init__(self, rules : List[Rule]): 
        self.rules :Dict[int, List[Rule]] = dict()
        for rule in rules:
            if rule.name in self.rules :
                self.rules[rule.name].append(rule)
            else :
                self.rules[rule.name]=[rule]

    def __getitem__(self, k)-> List[Rule]:
        return self.rules[k]

    def __str__(self):
        return str(self.rules)
    
    def __repr__(self):
        return str(self)

    def __contains__(self, other):
        return other in self.rules

class Item:
    def __init__(self, rule : Rule, dot:int, look_ahead:int):
        self.rule = rule
        self.dot = dot
        self.look_ahead = look_ahead

    def advanced(self):
        return Item(self.rule, self.dot+1, self.look_ahead)

    def current(self)->Optional[int]:
        return self.rule[self.dot]

    def is_at_end(self):
        return self.dot >= len(self.rule.definition)

    def __eq__(self, other):
        return (self.dot == other.dot) and (self.rule == other.rule)

    def __str__(self):
        return f"{self.dot} :- {self.rule} => {self.look_ahead}"

    def __repr__(self):
        return str(self)

class Tree(Generic[T, T2]):
    def __init__(self, data: T, children:List[T2]):
        self.data = data
        self.children = children

class Map:
    def __init__(self, names = None, map = None):
        self.names : List[str] = names if names else []
        self.map : Dict[str, int] = map if map else None

    def add_str(self, name: str, terminal = False):
        if not name in self.map:
            self.names.append(name)
            self.map[name] = len(self.names)

    def get_int(self, name : str):
        return self.map[name]

    def get_str(self, number: int):
        return self.names[number]

    def rule2str(self, rule:Rule):
        name = self.names[rule.name]
        if rule.definition is None:
            return f"{name}=TERMINAL"
        names = map( lambda x : self.names[x], rule.definition)
        out_list = " ".join(names)
        return f"{name} -> {out_list}"

    def item2str(self, item:Item):
        rule = self.rule2str(item.rule)
        return f"{item.dot} :- {rule} {item.look_ahead}"

    def rules2str(self, rules:Rules):
        out = []
        for rule_bag in rules.rules.values():
            for rule in rule_bag:
                out.append(self.rule2str(rule))
        return "\n".join(out)

    def list_rule2str(self, rules:List[Rule]):
        out = []
        for rule in rules:
            out.append(self.rule2str(rule))
        return "\n".join(out)


    def list_item2str(self, rules:List[Item]):
        out = []
        for rule in rules:
            out.append(self.item2str(rule))
        return "\n".join(out)


def clousure(items:List[Item], rules: Rules, debug = None):
    C = items
    added_new = True
    while added_new : 
        added_new = False
        for item in C : 
            if (not item.rule.is_terminal()) and (not item.is_at_end()) :
                new_rule = item.current()
                for rule in  rules[new_rule]:
                    if not rule.is_terminal():
                        new = Item(rule, 0, 0)
                        if not (new in C) :
                            added_new = True
                            C.append(new)
    return C


def primitive_goto(item_set : List[Item], symbol : int, rules: Rules, debug=None)-> List[Item]:
    initial_set :List[Item] = []
    for item in item_set : 
        if (not item.rule.is_terminal()) and (not item.is_at_end()) :
            if item.current() == symbol:
                initial_set.append(item.advanced())

    return clousure(initial_set, rules, debug)


def compute_states(start : Item, rules: Rules, grammar_symbols, debug=None)-> List[List[Item]]:
    C = [clousure([start], rules, debug)]
    added_new = True
    while added_new:
        added_new = False
        for item_set in C : 
            for symbol in grammar_symbols:
                if (maybe := primitive_goto(item_set, symbol, rules, debug)) and (not maybe in C):
                    added_new = True
                    C.append(maybe)
    return C

def compute_goto_table(states: List[List[Item]], rules: Rules, grammar_symbols, debug=None)-> List[List[Tuple[int,int]]]:
    # (1, n) - (reduce, n)
    # (2,n ) - (shift, n)
    # (0, 0) - (error)
    transitions :List[List[Tuple[int, int]]] = [[-1 for j in range(len(grammar_symbols))] for i in range(len(states))]
    for i,state in enumerate(states) :
        shift_items = []
        reduce_items = []
        for item in state : 
            if item.is_at_end():
                reduce_items.append(item)
            else :
                shift_items.append(item)
        if reduce_items and (not shift_items):
            conflict = [state[0]]
            for item in state:
                if not (item.rule == state[0].rule):
                    if not (item in conflict):
                        conflict.append(item)
            if len(conflict)>1:
                print("REDUCE REDUCE CONFLICT AT STATE ",i)
                for rule in conflict:
                    print(rule)
            transitions[i] = [(1,item.rule.name) for _ in range(len(grammar_symbols))]
        elif shift_items  and (not reduce_items):
            for j,symbol in enumerate(grammar_symbols):
                if (maybe := primitive_goto(state, symbol, rules, debug)):
                    transitions[i][j] = (2,states.index(maybe))
                else : 
                    transitions[i][j] = (0,0)
        else : 
            print("SHIFT REDUCE CONFLIC IN STATE ", i)
            return None


    return transitions
                


def test(a:int)->None:
    names = ["S", "E", "$", "-", "T", "n", "(", ")"]
    map2int: Dict[str, int] = dict()
    for i,name in  enumerate(names):
        map2int[name] = i
    rules = Rules([
            #Rule(map2int["S"], [map2int["E"], map2int["$"]]),
            Rule(map2int["S"], [map2int["E"]]),
            Rule(map2int["E"], [map2int["E"], map2int["-"], map2int["T"]]),
            Rule(map2int["E"], [map2int["T"]]),
            Rule(map2int["T"], [map2int["n"]]),
            Rule(map2int["T"], [map2int["("], map2int["E"], map2int[")"]]),
            Rule(map2int["n"], None),
            Rule(map2int["-"], None),
            Rule(map2int["$"], None),
            Rule(map2int["("], None),
            Rule(map2int[")"], None),
    ])
    dic = Map(names, map2int)
    logg.debug("Grammar : \n%s", dic.rules2str(rules))
    logg.debug("Names to Int \n%s", map2int)
    logg.debug("Compute States")
    states = compute_states(Item(rules.rules[map2int["S"]][0], 0, 0), rules, grammar_symbols = [i for i,j in enumerate(names)], debug=dic)
    logg.debug("States")
    for item_set in states:
        logg.debug("State")
        logg.debug(dic.list_item2str(item_set))
    goto_table = compute_goto_table(states, rules, grammar_symbols = [i for i,j in enumerate(names)], debug=dic)
    print("  ", "  ".join(names)) 
    for i,row in enumerate(goto_table):
        print(i, " ".join(map(lambda x : f"r{x[1]}" if x[0]==1  else " e" if x==(0,0) else f"s{x[1]}",row)))
    #I0 = clousure([Item(rules[map2int["S"]][0], 0, 0)], rules, dic)

test(1)
    
    



