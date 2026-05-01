import tarski
from tarski.io import PDDLReader
from tarski.io import fstrips as iofs

from tarski.search import GroundForwardSearchModel
from tarski.grounding.lp_grounding import (
    ground_problem_schemas_into_plain_operators,
    LPGroundingStrategy,
)


def entails(state, partialstate):
    return partialstate <= state


def progress(state, act):
    assert entails(state, act.pres), (
        "Cannot progress with inconsistent state / action precondition:\n\t Action: "
        + act.name
        + "\n\t State: \n\t\t"
        + "\n\t\t".join(state)
    )
    return (state - act.dels) | act.adds


def regress(state, act):
    assert len(state & act.dels) == 0, (
        f"Cannot regress with inconsistent state / action delete effect:\n\t Action: "
        + act.name
        + "\n\t State: \n\t\t"
        + "\n\t\t".join(state)
    )
    return (state - act.adds) | act.pres


def fix_name(s):
    # (act param)
    if "(" == s[0] and ")" == s[-1]:
        return s[1:-1]
    # make it space separated
    s = s.replace(", ", " ").replace(",", " ")
    # act(param)
    if "(" in s:
        assert ")" == s[-1], f"Broken name? {s}"
        s = s.replace("(", " ").replace(")", "")
    # act param
    return s


class Action:
    def __init__(self, name, pre, add, delete, instance_id=None):
        self.name = name
        self.pres = pre
        self.adds = add
        self.dels = delete
        self.instance_id = instance_id

    def __str__(self):
        return (
            f"{self.name}#{self.instance_id}"
            if self.instance_id is not None
            else self.name
        )

    def __repr__(self):
        return (
            f"{self.name}#{self.instance_id}"
            if self.instance_id is not None
            else self.name
        )

    def __hash__(self):
        return hash((self.name, self.instance_id))

    def __eq__(self, other):
        return (
            isinstance(other, Action)
            and self.name == other.name
            and self.instance_id == other.instance_id
        )


class STRIPS:
    def __init__(self, domain, problem):
        reader = PDDLReader(raise_on_error=True)
        # Preprocess domain file to fix known issues before parsing
        domain = self._preprocess_domain(domain)
        reader.parse_domain(domain)
        problem = reader.parse_instance(problem)
        (grounded_fluents, init, goal, operators) = self.ground_problem(problem)

        self.fluents = set([fix_name(str(f)) for f in grounded_fluents])
        self.init = set([fix_name(str(f)) for f in init])
        self.goal = set([fix_name(str(f)) for f in goal])
        self.actions = set()
        self.action_map = {}

        for op in operators:
            adds = {
                fix_name(str(f.atom))
                for f in op.effects
                if isinstance(f, iofs.AddEffect)
            } & self.fluents
            dels = {
                fix_name(str(f.atom))
                for f in op.effects
                if isinstance(f, iofs.DelEffect)
            } & self.fluents
            # Handle empty preconditions (Tautology) and normal preconditions
            if hasattr(op.precondition, "subformulas"):
                pre = {
                    fix_name(str(f)) for f in op.precondition.subformulas
                } & self.fluents
            else:
                pre = set()

            act = Action(fix_name(str(op)), pre, adds, dels)
            self.actions.add(act)
            self.action_map[act.name] = act

    def action(self, name):
        return self.action_map[fix_name(name)]

    def fluent(self, name):
        return fix_name(name)

    def _preprocess_domain(self, domain_path):
        """
        Preprocess domain files to fix known parsing issues.

        Known fixes:
        - Storage domain: Fix duplicate 'area' type definition
        """
        import os
        import tempfile

        # Read the domain file
        with open(domain_path, "r") as f:
            content = f.read()

        # Fix storage domain issues
        if "storage" in domain_path.lower():
            modified = False

            # Fix 1: duplicate type definition
            # The storage domain has: "area crate - surface" but area is already defined as "- object"
            # This causes Tarski to fail with DuplicateSortDefinition
            # Fix: replace "area crate - surface" with "crate - surface"
            if "area crate - surface" in content:
                content = content.replace("area crate - surface", "crate - surface")
                modified = True

            # Fix 2: "either" type construct not supported by Tarski
            # The predicate uses: (in ?x - (either storearea crate) ?p - place)
            # Tarski doesn't support "either" types
            # Fix: replace with common parent type "object" (both storearea and crate are subtypes of object)
            if "(either storearea crate)" in content:
                content = content.replace("(either storearea crate)", "object")
                modified = True

            if modified:
                # Write the fixed content to a temporary file
                fd, temp_path = tempfile.mkstemp(suffix=".pddl", text=True)
                try:
                    with os.fdopen(fd, "w") as f:
                        f.write(content)
                    return temp_path
                except:
                    os.unlink(temp_path)
                    raise

        # No preprocessing needed
        return domain_path

    def ground_problem(self, problem):
        operators = ground_problem_schemas_into_plain_operators(problem)
        instance = GroundForwardSearchModel(problem, operators)
        grounder = LPGroundingStrategy(problem, include_variable_inequalities=True)
        grounded_fluents = set(
            [
                grounded_fluent.to_atom()
                for grounded_fluent in grounder.ground_state_variables().objects
            ]
        )
        init = [f for f in problem.init.as_atoms() if f in grounded_fluents]
        if isinstance(problem.goal, tarski.syntax.Atom):
            goal = [problem.goal]
        else:
            goal = [f for f in problem.goal.subformulas if f in grounded_fluents]

        return (grounded_fluents, init, goal, operators)
