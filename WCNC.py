"""
WCNC 2025 experiments — lossy semantic communication for the logical deduction
of the state of the world.

This merges what were WCNC.py and WCNC_deduc.py. Both ran the same encoding and
selection pipeline and differed in which corpus they read, which vocabulary they
grounded against, and what they did with the model counts afterwards. Select
between them with --experiment.

    folio       Semantic compression over FOLIO. Each story is a world; every
                subset of up to three premises is encoded, counted, and scored
                by how much of the state space it eliminates. Reports the bit
                cost and content of the most informative message at each subset
                size, or of every message under --selection random.

    deduction   Hypothesis deduction over the custom corpus. Each sentence is
                its own world, every subset size is enumerated, and the counts
                are reported ordered by model count.

Model counting happens outside Python, so a run has two stages:

    --stage generate    Write one DIMACS instance per candidate subset, and
                        accumulate the matching sharpSAT commands in script.txt.
                        Run those commands before continuing.

    --stage analyze     Walk the same candidates, read each model count back,
                        and run the analysis.

Examples:
    python3 WCNC.py --experiment folio --stage generate
    python3 WCNC.py --experiment folio --stage analyze
    python3 WCNC.py --experiment folio --stage analyze --selection random
    python3 WCNC.py --experiment deduction --stage generate
"""

import argparse
import os
import shutil
from collections import defaultdict
from functools import reduce
from itertools import combinations

from utilities import *
from bin_tree import *

# ── Configuration ────────────────────────────────────────────────────────────
BITS_PER_CHAR = 8

# Stories shorter than this are dropped from FOLIO, matching the Huffman baseline.
MIN_PREMISES = 7

# Vocabulary the deduction corpus is grounded against, used on its own.
DEDUC_PREDICATES = [
    "Teaches", "EnrolledIn", "Likes", "LivesIn", "PlaysInstrument",
    "IsFriendOf", "GraduatedFrom", "Course", "Piano", "Guitar",
]
DEDUC_ENTITIES = [
    "Piano", "Guitar", "DrSmith", "Calculus101", "History202", "Painting",
    "Soccer", "NewYork", "LosAngeles", "Violin", "James", "Emily", "Michael",
    "Sarah", "Christopher", "Olivia", "Harvard", "Stanford", "Lily", "Ethan",
    "Noah", "Mia", "Benjamin", "Ava", "Lucas", "Isabella", "Mason", "Sophia",
    "Jacob", "Emma", "Daniel", "Grace", "Samuel", "Chloe", "Aiden", "Madison",
    "Henry", "Abigail", "William",
]

EXPERIMENTS = {
    "folio": {
        "data": "folio-train.jsonl",
        "cnf_dir": "dimac_cnfs",
        "result_dir": os.path.join("WCNC", "dimac_cnfs_res"),
        "write_dimacs": lambda *a: write_dimacs_to_file_ubuntu(*a),
        "write_script": lambda *a: write_a_file(*a),
        "declared_vars": lambda variables: len(variables),
        # Subsets of up to three premises.
        "subset_sizes": lambda n: range(1, 4),
        "fixed_vocabulary": False,
        "record_content": True,
    },
    "deduction": {
        "data": "deduc_dataset_v2.jsonl",
        "cnf_dir": "dimac_cnfs_deduc",
        "result_dir": os.path.join("WCNC", "dimac_cnfs_deduc_res"),
        "write_dimacs": lambda *a: write_dimacs_to_file_deduc(*a),
        "write_script": lambda *a: write_a_file_deduc(*a),
        # Fixed so instances stay comparable across worlds.
        "declared_vars": lambda variables: 3005,
        "subset_sizes": lambda n: range(1, n + 1),
        "fixed_vocabulary": True,
        "record_content": False,
    },
}


# ── Data preparation ─────────────────────────────────────────────────────────
def read_folio_stories(frame, min_premises=MIN_PREMISES):
    """Return the FOL premises of each sufficiently long FOLIO story.

    FOLIO pairs one set of premises with several conclusions, so the same story
    appears in several records; they are deduplicated by `story_id`.
    """
    stories, seen = [], set()

    for ix in range(len(frame)):
        story_id = frame["story_id"][ix]
        if story_id in seen:
            continue
        seen.add(story_id)

        premises = frame["premises-FOL"][ix]
        if len(premises) >= min_premises:
            stories.append(premises)

    return stories


def read_deduction_stories(frame):
    """Return each sentence of the deduction corpus as its own one-sentence world."""
    return [[row[0]] for row in frame.values.tolist()]


def normalize_quantifiers(sentences):
    """Rewrite existentials as universals, flagging which were reversed.

    A sentence with an odd number of existential quantifiers has its logical
    probability complemented, so the flag records that its model count must be
    read as the complement. Sentences with no quantifiers pass through.
    """
    next_FOL, there_exists_flag = [], []

    for fol_expression in sentences:
        if not contains_quantifiers(fol_expression):
            next_FOL.append(fol_expression)
            there_exists_flag.append(False)
            continue

        if not contains_both_quantifiers(fol_expression) and contains_forall(
            fol_expression
        ):
            next_FOL.append(fol_expression)
            there_exists_flag.append(False)
            continue

        num_q = fol_expression.count("∃")
        there_exists_flag.append(num_q % 2 == 1)
        next_FOL.append(fol_expression.replace("∃", "∀"))

    return next_FOL, there_exists_flag


def flatten_stories(story_arr, grounded_override=None):
    """Normalize each world's quantifiers and record its entity sets."""
    flat_arr = []

    for next_story in story_arr:
        grounded_entity, variable_entity = get_all_entities(next_story)
        if grounded_override is not None:
            grounded_entity = grounded_override

        next_FOL, there_exists_flag = normalize_quantifiers(next_story)
        flat_arr.append(
            [next_FOL, grounded_entity, variable_entity, there_exists_flag]
        )

    return flat_arr


def unique_elements(story_arr, fixed_vocabulary=False):
    """Collect the vocabulary and the size of the enumeration it induces.

    `num_enum` is the number of grounded predicate-entity triples the language
    admits, which sets the width of the logical state space. `enums_per_story`
    is the same quantity computed from the vocabulary each world actually uses.
    """
    if fixed_vocabulary:
        unique_predicates = sorted(DEDUC_PREDICATES)
        unique_grounded_entities = sorted(DEDUC_ENTITIES)
        unique_variable_entities = sorted(["x", "y"])
    else:
        predicates, grounded, variables = set(), set(), set()
        for next_story in story_arr:
            for fol_expression in next_story:
                tree = parse_text_FOL_to_tree(fol_expression)
                if tree is not None:
                    predicates.update(extract_predicates_from_tree(tree))
                    grounded.update(extract_grounded_entities_from_tree(tree))
                    variables.update(extract_variable_entities_from_tree(tree))
        unique_predicates = sorted(predicates)
        unique_grounded_entities = sorted(grounded)
        unique_variable_entities = sorted(variables)

    enums_per_story = []
    for next_story in story_arr:
        predicates_tmp, entities_tmp = set(), set()
        for fol_expression in next_story:
            tree = parse_text_FOL_to_tree(fol_expression)
            if tree is not None:
                predicates_tmp.update(extract_predicates_from_tree(tree))
                entities_tmp.update(extract_grounded_entities_from_tree(tree))
        enums_per_story.append(
            len(predicates_tmp) * len(entities_tmp) * len(entities_tmp)
        )

    num_enum = (len(unique_grounded_entities) ** 2) * len(unique_predicates)

    print("Unique Predicates: ", unique_predicates)
    print("Unique Grounded Entities: ", unique_grounded_entities)
    print("Unique Variable Entities: ", unique_variable_entities)
    print("Number of Unique Predicates: ", len(unique_predicates))
    print("Number of Unique Grounded Entities: ", len(unique_grounded_entities))
    print("Number of Unique Variable Entities: ", len(unique_variable_entities))
    print("Number of Enumerations: ", num_enum)
    print("Number of Enumerations Per Story: ", enums_per_story)

    return (
        unique_predicates,
        unique_grounded_entities,
        unique_variable_entities,
        num_enum,
        enums_per_story,
    )


def get_term_orders(story_flat_arr, unique_predicates, unique_grounded_entities):
    """Parse each sentence to a tree and compute its truth table and term order.

    The predicate and entity lists fix the enumeration order, so a variable
    index means the same thing across every sentence in a world.
    """
    df_c, term_orders, there_exists = [], [], []

    for next_FOL_exp in story_flat_arr:
        FOL_sentences, grounded_ents = next_FOL_exp[0], next_FOL_exp[1]

        temp_arr, temp_arr_ord = [], []
        for fol_expression in FOL_sentences:
            tree = parse_text_FOL_to_tree(fol_expression)
            if tree is not None:
                isFOL, lvars, consts, preds = symbol_resolution(tree)
                rule = Rule(isFOL, lvars, consts, preds, tree, grounded_ents)
                rule.replace_logical_operations()
                rule.generate_enumerations()
                rule.calculate_term_orders(
                    unique_predicates, unique_grounded_entities
                )
            variables, truth_table = compute_truth_table(rule)
            cnf, bin_reps = truth_table_to_cnf(truth_table, variables)
            temp_arr.append([fol_expression, bin_reps, cnf, truth_table, rule])
            temp_arr_ord.append(rule.term_orders)

        df_c.append(temp_arr)
        term_orders.append(temp_arr_ord)
        there_exists.append(next_FOL_exp[3])

    return df_c, term_orders, there_exists


# ── Model counter interface ──────────────────────────────────────────────────
def script_for_ubuntu(story_id, permn, config):
    """Append the sharpSAT invocation for one instance to script.txt."""
    full_path = os.path.join(config["cnf_dir"], "script.txt")
    config["write_script"](story_id, permn, full_path)


def get_tokens(story_id, permn, index, last_tokens, var_len, enum, thereex,
               fols, config):
    """Read one model count back and record it.

    The counter writes its result as the last token of the output file.
    """
    file_path = os.path.join(
        config["result_dir"], f"output_{story_id}_{permn}.txt"
    )

    with open(file_path, "r") as handle:
        tokens = []
        for line in handle:
            tokens = line.strip().split()

    if not tokens:
        return last_tokens

    count = int(tokens[-1])
    record = [story_id, permn, index, count, var_len, enum]
    if config["record_content"]:
        # Content: the number of world states the message eliminates.
        record.append((2 ** var_len) - count)
    record.append(fols)

    last_tokens.append(record)
    return last_tokens


def move_txt(config):
    """Move counter output out of the CNF directory into the result directory."""
    source_dir = config["cnf_dir"]
    destination_dir = config["result_dir"]
    os.makedirs(destination_dir, exist_ok=True)

    for filename in os.listdir(source_dir):
        if filename.endswith(".txt"):
            shutil.move(
                os.path.join(source_dir, filename),
                os.path.join(destination_dir, filename),
            )
            print(f"Moved: {filename}")

    print("All .txt files have been moved.")


# ── Analysis ─────────────────────────────────────────────────────────────────
def group_by_story(last_tokens):
    """Split the flat record list into one list per story, sorted by count."""
    story_id = 0
    grouped, current = [], []

    for record in last_tokens:
        if record[0] > story_id:
            grouped.append(current)
            story_id += 1
            current = []
        else:
            current.append(record)
    grouped.append(current)

    return [sorted(group, key=lambda x: x[3]) for group in grouped]


def bucket_by_subset_size(group):
    """Partition a story's records by how many sentences the subset holds."""
    buckets = {1: [], 2: [], 3: []}
    for record in group:
        size = len(record[2])
        if size in buckets:
            buckets[size].append(record)
    return buckets[1], buckets[2], buckets[3]


def calc_inductive_probs(last_tokens):
    """Report the most informative message at each subset size.

    Within a story the single sentence with the lowest model count is the most
    informative, since it admits the fewest world states. The best pair is the
    lowest-count pair containing that sentence, and the best triple the
    lowest-count triple containing that pair, so each size extends the last.
    """
    grouped = group_by_story(last_tokens)
    min_ones, min_twos, min_threes = [], [], []

    for group in grouped:
        sub_ones, sub_twos, sub_threes = bucket_by_subset_size(group)
        for record in group:
            print(record)

        m_one = min(sub_ones, key=lambda x: x[3])
        min_ones.append(m_one)

        two_temp = [e for e in sub_twos if m_one[2][0] in e[2]]
        m_two = min(two_temp, key=lambda x: x[3])
        min_twos.append(m_two)

        three_temp = [
            e for e in sub_threes if m_two[2][0] in e[2] and m_two[2][1] in e[2]
        ]
        m_three = min(three_temp, key=lambda x: x[3])
        min_threes.append(m_three)

    print(min_ones)
    print(min_twos)
    print(min_threes)

    s_1, s_2, s_3 = [], [], []
    cont_1, cont_2, cont_3 = [], [], []
    var_1, var_2, var_3 = [], [], []

    for ids in range(len(min_ones)):
        one, two, three = min_ones[ids], min_twos[ids], min_threes[ids]
        s_1.append([ids, len(one[-1][0]) * BITS_PER_CHAR])
        s_2.append([ids, sum(len(s) * BITS_PER_CHAR for s in two[-1][:2])])
        s_3.append([ids, sum(len(s) * BITS_PER_CHAR for s in three[-1][:3])])
        cont_1.append([ids, one[-2]])
        cont_2.append([ids, two[-2]])
        cont_3.append([ids, three[-2]])
        var_1.append([ids, one[4]])
        var_2.append([ids, two[4]])
        var_3.append([ids, three[4]])

    for series in (s_1, s_2, s_3, cont_1, cont_2, cont_3, var_1, var_2, var_3):
        print(series)


def calc_inductive_probs_random(last_tokens):
    """Baseline: report every subset rather than the most informative one.

    Averaging over all subsets of a given size gives the expected cost of
    picking a message at random, which is what the selection rule is measured
    against.
    """
    grouped = group_by_story(last_tokens)

    s_1, s_2, s_3 = [], [], []
    cont_1, cont_2, cont_3 = [], [], []
    var_1, var_2, var_3 = [], [], []

    for ids, group in enumerate(grouped):
        sub_ones, sub_twos, sub_threes = bucket_by_subset_size(group)
        for record in group:
            print(record)

        for bucket, sizes, conts, variables in (
            (sub_ones, s_1, cont_1, var_1),
            (sub_twos, s_2, cont_2, var_2),
            (sub_threes, s_3, cont_3, var_3),
        ):
            for record in bucket:
                total = sum(len(s) * BITS_PER_CHAR for s in record[-1])
                sizes.append([ids, total])
                conts.append([ids, record[-2]])
                variables.append([ids, record[4]])

    for series in (s_1, s_2, s_3, cont_1, cont_2, cont_3, var_1, var_2, var_3):
        print(series)

    for series in (s_1, s_2, s_3):
        sums = defaultdict(list)
        for first, second in series:
            sums[first].append(second)
        print([[key, sum(v) / len(v)] for key, v in sums.items()])


def calc_inductive_probs_deduction(last_tokens):
    """Report the sentences of every candidate, ordered by model count."""
    for record in sorted(last_tokens, key=lambda x: x[3]):
        print([record[-1]])


# ── Main ─────────────────────────────────────────────────────────────────────
def build_candidates(term_orders, df_c, there_exists, enums_per_story, config,
                     collect_tokens):
    """Encode every candidate subset, and read its count back when asked.

    Each subset of sentences becomes one DIMACS instance. In the generate stage
    the instances and the counter commands are all that is produced; in the
    analyze stage the counts are read back alongside.
    """
    last_tokens = []

    for story_id in range(len(term_orders)):
        selected_elements = [
            list(dictionary.values()) for dictionary in term_orders[story_id]
        ]
        selected_truth_t = [element[3] for element in df_c[story_id]]
        selected_fol = [element[0] for element in df_c[story_id]]
        selected_there_exists = there_exists[story_id]

        permn = 0
        for size in config["subset_sizes"](len(selected_elements)):
            for index in combinations(range(len(selected_elements)), size):
                combin = [selected_elements[i] for i in index]
                combin_t = [selected_truth_t[i] for i in index]
                rev_p_t = [selected_there_exists[i] for i in index]
                fols = [selected_fol[i] for i in index]

                variables = list(set(sum(combin, [])))
                reversed_flag = reduce(lambda x, y: x ^ y, rev_p_t)

                selected_clauses = []
                for im in range(len(combin_t)):
                    _, clauses = truth_table_to_cnf_dimacs(
                        combin_t[im], combin[im], variables, reversed_flag
                    )
                    selected_clauses.append(clauses if clauses is not None else [])

                num_elem = len(list(sum(selected_clauses, [])))
                config["write_dimacs"](
                    selected_clauses,
                    story_id,
                    permn,
                    num_elem,
                    config["declared_vars"](variables),
                )
                script_for_ubuntu(story_id, permn, config)

                if collect_tokens:
                    last_tokens = get_tokens(
                        story_id, permn, index, last_tokens, len(variables),
                        enums_per_story[story_id], rev_p_t, fols, config,
                    )
                permn += 1

    return last_tokens


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[1])
    parser.add_argument(
        "--experiment", choices=sorted(EXPERIMENTS), default="folio"
    )
    parser.add_argument("--stage", choices=["generate", "analyze"], default="generate")
    parser.add_argument(
        "--selection",
        choices=["content", "random"],
        default="content",
        help="folio only: most informative message, or all of them",
    )
    parser.add_argument(
        "--move-results",
        action="store_true",
        help="move counter output into the result directory before analyzing",
    )
    parser.add_argument("--data", default=None, help="override the input corpus")
    args = parser.parse_args()

    config = EXPERIMENTS[args.experiment]
    data_path = args.data or config["data"]
    os.makedirs(config["cnf_dir"], exist_ok=True)
    os.makedirs(config["result_dir"], exist_ok=True)

    frame = pd.read_json(data_path, lines=True)
    if args.experiment == "deduction":
        stories = read_deduction_stories(frame)
    else:
        stories = read_folio_stories(frame)
    print(f"Loaded {len(stories)} worlds from {data_path}")

    story_flat = flatten_stories(
        story_arr=stories,
        grounded_override=DEDUC_ENTITIES if config["fixed_vocabulary"] else None,
    )
    unique_predicates, unique_grounded_entities, _, _, enums_per_story = (
        unique_elements(stories, fixed_vocabulary=config["fixed_vocabulary"])
    )
    df_c, term_orders, there_exists = get_term_orders(
        story_flat, unique_predicates, unique_grounded_entities
    )

    if args.stage == "analyze" and args.move_results:
        move_txt(config)

    last_tokens = build_candidates(
        term_orders, df_c, there_exists, enums_per_story, config,
        collect_tokens=(args.stage == "analyze"),
    )

    if args.stage == "generate":
        print(
            f"\nWrote DIMACS instances to {config['cnf_dir']}/ and counter "
            f"commands to {os.path.join(config['cnf_dir'], 'script.txt')}.\n"
            f"Run those, then re-run with --stage analyze."
        )
        return

    if args.experiment == "deduction":
        calc_inductive_probs_deduction(last_tokens)
    elif args.selection == "random":
        calc_inductive_probs_random(last_tokens)
    else:
        calc_inductive_probs(last_tokens)


if __name__ == "__main__":
    main()
