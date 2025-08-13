
import argparse, json

from bauhaus import Encoding, proposition, And, Or
from nnf import dimacs

from lifter import lift_POP


class Hashable:
    def __hash__(self):
        return hash(str(self))

    def __eq__(self, __value: object) -> bool:
        return hash(self) == hash(__value)

    def __repr__(self):
        return str(self)

def encode_POP(pop, cmdargs):

    # For sanitization, make sure we close the pop
    pop.transativly_close()

    F = pop.F
    A = pop.A

    init = pop.init
    goal = pop.goal

    adders = {}
    deleters = {}

    for f in F:
        adders[f] = set([])
        deleters[f] = set([])

    for a in A:
        for f in a.adds:
            adders[f].add(a)
        for f in a.dels:
            deleters[f].add(a)

    E = Encoding()

    @proposition(E)
    class Action(Hashable):
        def _prop_name(self):
            return f"Action({self.name})"
        #_prop_name = "Action"
        def __init__(self, name):
            self.name = name

        def __repr__(self):
            return f"Action({self.name})"

        def __str__(self):
            return f"{self.name} in plan"

        def __hash__(self) -> int:
            return hash(self.name)

    @proposition(E)
    class Order(Hashable):
        def _prop_name(self):
            return f"Order({self.a1}, {self.a2})"
        def __init__(self, a1, a2):
            self.a1 = a1
            self.a2 = a2

        def __repr__(self):
            return f"Order({self.a1}, {self.a2})"

        def __str__(self):
            return f"{self.a1} -> {self.a2}"

    @proposition(E)
    class Support(Hashable):
        def _prop_name(self):
            return f"Support({self.a1}, {self.p}, {self.a2})"
        def __init__(self, a1, p, a2):
            self.a1 = a1
            self.p = p
            self.a2 = a2

        def __repr__(self):
            return f"Support({self.a1}, {self.p}, {self.a2})"

        def __str__(self):
            return f"{self.a1} supports {self.p} for {self.a2}"

    actions = [Action(a) for a in A]
    orders = [Order(a1, a2) for a1 in A for a2 in A]
    supports = [Support(a1, p, a2) for a2 in A for p in a2.pres for a1 in adders[p]]

    v2a = {action: action.name for action in actions}
    a2v = {action.name: action for action in actions}

    v2o = {order: (order.a1, order.a2) for order in orders}
    o2v = {(order.a1, order.a2): order for order in orders}

    v2s = {support: (support.a1, support.p, support.a2) for support in supports}

    clauses = []

    # Add the antisymmetric ordering constraints
    clauses.extend([~Order(a, a) for a in A])

    # Add the transitivity constraints
    for a1 in A:
        for a2 in A:
            for a3 in A:
                clauses.append((Order(a1, a2) & Order(a2, a3)) >> Order(a1, a3))

    # Add the ordering -> actions constraints
    for a1 in A:
        for a2 in A:
            clauses.append(Order(a1, a2) >> (Action(a1) & Action(a2)))

    # Make sure everything comes after the init, and before the goal
    for a in A:
        if a is not init:
            clauses.append(Action(a) >> Order(init, a))
        if a is not goal:
            clauses.append(Action(a) >> Order(a, goal))

    # Ensure that we have a goal and init action.
    clauses.append(Action(init))
    clauses.append(Action(goal))

    # Satisfy all the preconditions
    for a2 in A:
        for p in a2.pres:
            clauses.append(Action(a2) >> Or([Support(a1, p, a2) for a1 in [x for x in adders[p] if x is not a2]]))

    # Create unthreatened support
    for a2 in A:
        for p in a2.pres:
            for a1 in [x for x in adders[p] if x is not a2]:

                # Support implies ordering
                clauses.append(Support(a1, p, a2) >> Order(a1, a2))

                # Forbid threats
                for ad in deleters[p]:
                    if ad not in [a1, a2]:
                        clauses.append(Support(a1, p, a2) >> (~Action(ad) | Order(ad, a1) | Order(a2, ad)))


    if cmdargs.serial:
        for a1 in A:
            for a2 in A:
                if a1 is not a2:
                    clauses.append((Action(a1) & Action(a2)) >> (Order(a1, a2) | Order(a2, a1)))

    if cmdargs.allact:
        for a in A:
            clauses.append(Action(a))

    if cmdargs.deorder:
        for (ai,aj) in pop.get_links():
            clauses.append(~Order(aj, ai))

    cnf = And(clauses).compile().simplify().to_CNF()

    var_labels = dict(enumerate(cnf.vars(), start=1))
    var_labels_inverse = {v: k for k, v in var_labels.items()}
    cnf_dimacs = dimacs.dumps(cnf, mode='cnf', var_labels=var_labels_inverse).strip()

    order_cost = 1
    action_cost = len(orders) + 1
    top_cost = (len(orders) * order_cost) + (len(actions) * action_cost) + 1

    cnflines = cnf_dimacs.split('\n')

    assert "p cnf" in cnflines[0]
    (_, _, nv, nc) = cnflines[0].split()
    cnflines[0] = f"p wcnf {nv} {int(nc)+len(actions)+len(orders)} {top_cost}"

    for i in range(1, len(cnflines)):
        if cnflines[i] != "":
            cnflines[i] = f"{top_cost} {cnflines[i]}"

    for a in actions:
        v = var_labels_inverse[a]
        cnflines.append(f"{action_cost} -{v} 0")

    for o in orders:
        v = var_labels_inverse[o]
        cnflines.append(f"{order_cost} -{v} 0")

    with open(cmdargs.output, 'w') as f:
        f.write('\n'.join(cnflines))

    with open(cmdargs.output+'.map', 'w') as f:
        f.write(json.dumps({k: str(v) for k, v in var_labels.items()}, indent=4))

    print('')
    print(f"Vars: {nv}")
    print(f"Clauses: {int(nc)+len(actions)+len(orders)}")
    print(f"Soft: {len(actions)+len(orders)}")
    print(f"Hard: {nc}")
    print(f"Max Weight: {top_cost}")
    print('')

if __name__ == '__main__':

    parser = argparse.ArgumentParser(description='Generate a wcnf file for a planning problem.')

    parser.add_argument('-d', '--domain', dest='domain', help='Domain file', required=True)

    parser.add_argument('-p', '--problem', dest='problem', help='Problem file', required=True)

    parser.add_argument('-s', '--plan', dest='plan', help='Plan file', required=True)

    parser.add_argument('-o', '--output', dest='output', help='Output file', required=True)

    parser.add_argument('--allact', dest='allact', action='store_true', help='Include all actions in the plan')
    parser.add_argument('--serial', dest='serial', action='store_true', help='Force it to be serial')
    parser.add_argument('--deorder', dest='deorder', action='store_true', help='Force it to be a deordering')

    args = parser.parse_args()
    pop = lift_POP(args.domain, args.problem, args.plan, serialized=True)

    encode_POP(pop, args)
