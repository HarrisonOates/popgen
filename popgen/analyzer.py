import argparse, json
import networkx as nx

from .linearizer import count_linearizations
from .pop import POP
from . import tarskilite as tl


def get_mapping(map_file):
    with open(map_file) as f:
        mapping = json.load(f)
    return mapping


def print_solution(mapping, output):
    with open(output) as f:
        output = f.readlines()

    varline = [x for x in output if x.startswith("v ")][0]
    values = varline.strip().split(" ")[1:]

    print("\nSolution:")
    for v in values:
        if "-" not in v:
            print("  " + mapping[v])


def extract_pop(mapping, output):
    with open(output) as f:
        output = f.readlines()

    varline = [x for x in output if x.startswith("v ")][0]
    solline = [x for x in output if x.startswith("s ")][0]

    optimal = "OPTIMUM FOUND" in solline
    values = varline.strip().split(" ")[1:]

    actions = set()
    orderings = []
    supports = []

    for v in [x for x in values if "-" not in x]:
        if "in plan" in mapping[v]:
            act = mapping[v].split(" in plan")[0]
            actions.add(act)
        elif " -> " in mapping[v]:
            parts = mapping[v].split(" -> ")
            orderings.append((parts[0], parts[1]))
        elif "supports" in mapping[v]:
            parts = mapping[v].split(" supports ")
            supports.append(
                (parts[0], parts[1].split(" for ")[0], parts[1].split(" for ")[1])
            )
        else:
            pass  # These are auxiliary variables
            # print("Error: Unrecognized mapping line: %s" % mapping[v])

    pop = POP()

    for a in actions:
        pop.add_action(a)

    for u, v in orderings:
        pop.link_actions(u, "", v)

    for a1, p, a2 in supports:
        pop.link_actions(a1, p, a2)

    # for a1 in actions:
    #    for a2 in actions:
    #        if (a1,a2) not in orderings and (a2,a1) not in orderings:
    #            print a1
    #            print a2

    return pop, optimal


def get_domain_info(domain, problem):
    """Parse domain/problem to get action effects (adders and deleters for each fluent)."""
    prob = tl.STRIPS(domain, problem)
    adders = {}
    deleters = {}

    for f in prob.fluents:
        adders[f] = set()
        deleters[f] = set()

    for a in prob.actions:
        for f in a.adds:
            adders[f].add(a)
        for f in a.dels:
            deleters[f].add(a)

    return prob, adders, deleters


def parse_action_string(act_str):
    """Parse action string like 'move#5' into (name, instance_id)."""
    if "#" in act_str:
        parts = act_str.rsplit("#", 1)
        try:
            return parts[0], int(parts[1])
        except ValueError:
            return act_str, None
    return act_str, None


def find_actions_in_plan(prob, plan_actions):
    """Find Action objects in prob.actions matching the plan action strings."""
    action_map = {}
    for a in prob.actions:
        name, inst_id = parse_action_string(str(a))
        if inst_id is not None:
            key = (name, inst_id)
        else:
            key = name
        action_map[key] = a
    return action_map


def count_exploited_white_knights(domain, problem, mapping, output, verbose=False):
    """
    Count the number of exploited white knights in a solution.

    An exploited white knight occurs when:
    1. There's a causal link a1 --p--> a2 (a1 adds p, a2 needs p)
    2. There's a deleter ad of p in the plan
    3. ad is a "potential threat": it is NOT ordered before a1 AND NOT ordered after a2
       (meaning ad COULD come between a1 and a2 in some linearization)
    4. The threat is NOT resolved by standard ordering (ad is not before a1, not after a2)
    5. There exists a white knight aw such that:
       - aw adds p
       - aw is ordered after ad (path ad -> aw)
       - aw is ordered before a2 (path aw -> a2)

    Returns the count of exploited white knights and details.
    """
    pop, optimal = extract_pop(mapping, output)

    prob, adders, deleters = get_domain_info(domain, problem)

    plan_actions = set(pop.network.nodes())
    plan_action_names = {str(a) for a in plan_actions}

    reachability = dict(nx.all_pairs_shortest_path_length(pop.network))

    def has_path(from_node, to_node):
        """Check if there's a path from from_node to to_node."""
        if str(from_node) == str(to_node):
            return True
        try:
            return str(to_node) in reachability.get(str(from_node), {})
        except KeyError:
            return False

    def is_ordered_before(a1, a2):
        """Check if a1 is ordered before a2 (path from a1 to a2 exists)."""
        return has_path(a1, a2)

    exploited_white_knights = []

    for (a1_str, a2_str), reasons in pop.link_reasons.items():
        for reason in reasons:
            if (
                not reason
                or reason == "trans"
                or reason == "serial"
                or reason == "init"
                or reason == "goal"
            ):
                continue

            p = reason

            a1 = None
            a2 = None
            for node_str in pop.network.nodes():
                if str(node_str) == a1_str:
                    a1 = node_str
                if str(node_str) == a2_str:
                    a2 = node_str

            if a1 is None or a2 is None:
                continue

            name1, inst_id1 = parse_action_string(str(a1))
            name2, inst_id2 = parse_action_string(str(a2))

            key1 = name1
            key2 = name2

            action1 = prob.action_map.get(key1)
            action2 = prob.action_map.get(key2)

            # Skip if action1 is not found (shouldn't happen for real actions)
            if action1 is None:
                continue

            # For goal/init pseudo-actions, action2 will be None - this is expected
            # We can still analyze the causal link even without action2's preconditions

            if p not in action1.adds:
                continue

            # Only check action2.pres if action2 exists (real domain actions)
            # For goal/init pseudo-actions, we skip this check
            if action2 is not None and p not in action2.pres:
                continue

            for ad_str in plan_action_names:
                ad_name, ad_inst = parse_action_string(ad_str)
                ad_key = ad_name
                ad_action = prob.action_map.get(ad_key)

                if ad_action is None:
                    continue

                if p not in ad_action.dels:
                    continue

                if ad_str == a1_str or ad_str == a2_str:
                    continue

                ad_node = None
                for node in pop.network.nodes():
                    if str(node) == ad_str:
                        ad_node = node
                        break

                if ad_node is None:
                    continue

                # Check if ad is a potential threat:
                # ad is NOT ordered before a1 AND NOT ordered after a2
                # This means ad COULD come between a1 and a2 in some linearization
                ad_before_a1 = is_ordered_before(ad_node, a1)  # path ad -> a1
                ad_after_a2 = is_ordered_before(a2, ad_node)   # path a2 -> ad

                if ad_before_a1 or ad_after_a2:
                    # Threat is resolved by standard ordering
                    continue

                # ad is a potential threat - now look for white knights
                potential_white_knights = []
                for aw_str in plan_action_names:
                    if aw_str == a1_str or aw_str == a2_str or aw_str == ad_str:
                        continue

                    aw_name, aw_inst = parse_action_string(aw_str)
                    aw_key = aw_name
                    aw_action = prob.action_map.get(aw_key)

                    if aw_action is None:
                        continue

                    if p not in aw_action.adds:
                        continue

                    aw_node = None
                    for node in pop.network.nodes():
                        if str(node) == aw_str:
                            aw_node = node
                            break

                    if aw_node is None:
                        continue

                    # Check if aw is a valid white knight:
                    # aw is ordered after ad (path ad -> aw)
                    # aw is ordered before a2 (path aw -> a2)
                    aw_after_ad = is_ordered_before(ad_node, aw_node)  # path ad -> aw
                    aw_before_a2 = is_ordered_before(aw_node, a2)      # path aw -> a2

                    if aw_after_ad and aw_before_a2:
                        potential_white_knights.append((aw_str, aw_action))

                if potential_white_knights:
                    exploited_white_knights.append(
                        {
                            "causal_link": (a1_str, p, a2_str),
                            "threatened_by": ad_str,
                            "white_knights": [
                                wk[0] for wk in potential_white_knights
                            ],
                        }
                    )

    if verbose:
        print("\nExploited White Knights:")
        for wk in exploited_white_knights:
            print(
                f"  Link {wk['causal_link'][0]} --{wk['causal_link'][1]}--> {wk['causal_link'][2]}"
            )
            print(f"    Threatened by: {wk['threatened_by']}")
            print(f"    Protected by white knights: {wk['white_knights']}")

    return len(exploited_white_knights), exploited_white_knights


def do_popstats(mapping, output, show_linears=False):
    pop, optimal = extract_pop(mapping, output)

    if show_linears:
        print("\nLinearizations: %d\n" % count_linearizations(pop))

    print("\n%s\n" % str(pop))
    print("Optimal: %s\n" % str(optimal))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Analyze the output of the solved encoding"
    )

    parser.add_argument("--map", help="The mapping file", required=True)
    parser.add_argument("--rc2out", help="The output from RC2", required=True)

    parser.add_argument("--dot", help="Print the POP as a dot file")
    parser.add_argument("--compactdot", help="Print the POP as a compact dot file")

    parser.add_argument(
        "--print-solution", help="Print the solution", action="store_true"
    )
    parser.add_argument(
        "--show-popstats", help="Show the POP stats", action="store_true"
    )
    parser.add_argument(
        "--count-linearizations",
        help="Show the number of linearizations",
        action="store_true",
    )
    parser.add_argument(
        "--count-white-knights",
        help="Count exploited white knights",
        action="store_true",
    )
    parser.add_argument(
        "--domain", help="Domain file (required for --count-white-knights)"
    )
    parser.add_argument(
        "--problem", help="Problem file (required for --count-white-knights)"
    )
    parser.add_argument(
        "--verbose-wk",
        help="Verbose output for white knight analysis",
        action="store_true",
    )

    args = parser.parse_args()

    if args.print_solution:
        print_solution(get_mapping(args.map), args.rc2out)

    if args.show_popstats:
        do_popstats(get_mapping(args.map), args.rc2out, args.count_linearizations)

    if args.dot:
        pop, _ = extract_pop(get_mapping(args.map), args.rc2out)
        with open(args.dot, "w") as f:
            f.write(pop.dot())

    if args.compactdot:
        pop, _ = extract_pop(get_mapping(args.map), args.rc2out)
        with open(args.compactdot, "w") as f:
            f.write(pop.dot(compact=True))

    if args.count_white_knights:
        if not args.domain or not args.problem:
            print(
                "Error: --domain and --problem are required for --count-white-knights"
            )
            exit(1)
        wk_count, _ = count_exploited_white_knights(
            args.domain,
            args.problem,
            get_mapping(args.map),
            args.rc2out,
            verbose=args.verbose_wk,
        )
        print(f"\nExploited White Knights: {wk_count}\n")
