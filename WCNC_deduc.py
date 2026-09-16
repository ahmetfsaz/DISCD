import sys
import os
import shutil
from utilities_SPAWC import *
from bin_tree import *
from itertools import combinations
from decimal import Decimal
from functools import reduce
import huffman

deduc_predicates = [
    "Teaches",
    "EnrolledIn",
    "Likes",
    "LivesIn",
    "PlaysInstrument",
    "IsFriendOf",
    "GraduatedFrom",
    "Course",
    "Piano",
    "Guitar",
]
deduc_entities = [
    "Piano",
    "Guitar",
    "DrSmith",
    "Calculus101",
    "History202",
    "Painting",
    "Soccer",
    "NewYork",
    "LosAngeles",
    "Violin",
    "James",
    "Emily",
    "Michael",
    "Sarah",
    "Christopher",
    "Olivia",
    "Harvard",
    "Stanford",
    "Lily",
    "Ethan",
    "Noah",
    "Mia",
    "Benjamin",
    "Ava",
    "Lucas",
    "Isabella",
    "Mason",
    "Sophia",
    "Jacob",
    "Emma",
    "Daniel",
    "Grace",
    "Samuel",
    "Chloe",
    "Aiden",
    "Madison",
    "Henry",
    "Abigail",
    "William"
]



def read_stories(dataframe):
    ids, story_arr = [], []
    for ix in range(len(dataframe)):
        if dataframe['story_id'][ix] in ids:
            continue
        else:
            story_arr.append(dataframe['premises-FOL'][ix])
        ids.append(dataframe['story_id'][ix])

    return story_arr, ids


def flatten_stories(story_arr):
    flat_arr = []
    for i in range(len(story_arr)):
        next_story = story_arr[i]
        next_FOL = []
        there_exists_flag = []
        _, variable_entity = get_all_entities(next_story)
        grounded_entity = deduc_entities
        for j in range(len(next_story)):
            fol_expression = next_story[j]
            if contains_quantifiers(fol_expression):
                if not contains_both_quantifiers(fol_expression):
                    if contains_forall(fol_expression):
                        next_FOL.append(fol_expression)
                        there_exists_flag.append(False)
                    else:
                        num_q = sum(fol_expression.count(quantifier) for quantifier in ['∃'])
                        if num_q % 2 == 1:
                            there_exists_flag.append(True)
                        else:
                            there_exists_flag.append(False)
                        fol_expression = fol_expression.replace('∃', '∀')
                        next_FOL.append(fol_expression)
                else:
                    # Count the number of ∃ and replace them with ∀.
                    # If the number of ∃ is odd, put a negation sign at the beginning, and set rev_prob to True.
                    num_q = sum(fol_expression.count(quantifier) for quantifier in ['∃'])
                    if num_q % 2 == 1:
                        there_exists_flag.append(True)
                    else:
                        there_exists_flag.append(False)
                    fol_expression = fol_expression.replace('∃', '∀')
                    next_FOL.append(fol_expression)
            else:
                next_FOL.append(fol_expression)
                there_exists_flag.append(False)
        flat_arr.append([next_FOL, grounded_entity, variable_entity, there_exists_flag])
    return flat_arr

def unique_elements():
    unique_predicates = sorted(list(deduc_predicates))
    unique_grounded_entities = sorted(list(deduc_entities))
    unique_variable_entities = sorted(list(['x', 'y']))

    # Print the information
    print("Unique Predicates: ", unique_predicates)
    print("Unique Grounded Entities: ", unique_grounded_entities)
    print("Unique Variable Entities: ", unique_variable_entities)
    print("Number of Unique Predicates: ", len(unique_predicates))
    print("Number of Unique Grounded Entities: ", len(unique_grounded_entities))
    print("Number of Unique Variable Entities: ", len(unique_variable_entities))
    print("Number of Enumerations: ", (len(unique_grounded_entities) ** 2) * len(unique_predicates))

    num_enum = (len(unique_grounded_entities) ** 2) * len(unique_predicates)
    enums_per_story = num_enum

    return unique_predicates, unique_grounded_entities, unique_variable_entities, num_enum, enums_per_story

def unique_elements(story_arr):
    # Extract predicates, entities, and variables from each FOL expression into a set.
    unique_predicates = sorted(list(deduc_predicates))
    unique_grounded_entities = sorted(list(deduc_entities))
    unique_variable_entities = sorted(list(['x', 'y']))

    # Print the information
    print("Unique Predicates: ", unique_predicates)
    print("Unique Grounded Entities: ", unique_grounded_entities)
    print("Unique Variable Entities: ", unique_variable_entities)
    print("Number of Unique Predicates: ", len(unique_predicates))
    print("Number of Unique Grounded Entities: ", len(unique_grounded_entities))
    print("Number of Unique Variable Entities: ", len(unique_variable_entities))
    print("Number of Enumerations: ", (len(unique_grounded_entities) ** 2) * len(unique_predicates))
    enums_per_story = []
    for index in range(len(story_arr)):
        next_story = story_arr[index]
        predicates_tmp = set()
        entities_tmp = set()
        for j in range(len(next_story)):
            fol_expression = next_story[j]
            tree = parse_text_FOL_to_tree(fol_expression)
            if tree is not None:
                predicates = extract_predicates_from_tree(tree)
                predicates_tmp.update(predicates)
                grounded_entities = extract_grounded_entities_from_tree(tree)
                entities_tmp.update(grounded_entities)
                variable_entities = extract_variable_entities_from_tree(tree)
        num_p = len(list(predicates_tmp))
        num_e = len(list(entities_tmp))
        enums_per_story.append(num_p * num_e * num_e)
    print("Number of Enumerations Per Story: ", enums_per_story)

    # Assuming a lexical enumeration where each predicate is listed with corresponding list of entities, create an
    # ordering and store the cardinality of the enumerations in num_enum.
    num_enum = (len(unique_grounded_entities) ** 2) * len(unique_predicates)

    return unique_predicates, unique_grounded_entities, unique_variable_entities, num_enum, enums_per_story
def get_term_orders(story_flat_arr):
    df_c = []
    term_orders = []
    there_exists = []
    for next_FOL_exp in story_flat_arr:
        FOL_sentences = next_FOL_exp[0]
        grounded_ents = next_FOL_exp[1]
        there_exists_prob = next_FOL_exp[3]

        temp_arr = []
        temp_arr_ord = []
        temp_rev = []
        for k in range(len(FOL_sentences)):
            fol_expression = FOL_sentences[k]
            tree = parse_text_FOL_to_tree(fol_expression)
            if tree is not None:
                isFOL, lvars, consts, preds = symbol_resolution(tree)
                rule = Rule(isFOL, lvars, consts, preds, tree, grounded_ents)  # Assuming the Rule constructor
                rule.replace_logical_operations()
                rule.generate_enumerations()
                rule.calculate_term_orders(unique_predicates, unique_grounded_entities)
            variables, truth_table = compute_truth_table(rule)
            cnf, bin_reps = truth_table_to_cnf(truth_table, variables)
            temp_arr.append([fol_expression, bin_reps, cnf, truth_table, rule])
            temp_arr_ord.append(rule.term_orders)
        df_c.append(temp_arr)
        term_orders.append(temp_arr_ord)
        there_exists.append(there_exists_prob)

    return df_c, term_orders, there_exists

def script_for_ubuntu(story_id, permn):
    directory = 'dimac_cnfs_deduc'
    file_name = 'script.txt'
    full_path = os.path.join(directory, file_name)
    write_a_file_deduc(story_id, permn, full_path)

def get_tokens(story_id, permn, last_tokens, var_len, enum, thereex, fols):
    file_path = f"WCNC/dimac_cnfs_deduc_res\\output_{story_id}_{permn}.txt"
    # Open the file and read it line by line
    with open(file_path, 'r') as file:
        tokens = []
        for line in file:
            # Strip any leading/trailing whitespace and split the line into tokens
            tokens = line.strip().split()
            # If the line is not empty, take the last token and add it to the list
        if tokens:
            if len(thereex) > 0 and reduce(lambda x, y: x ^ y, thereex):  # check if thereexists_flag is True.
                # Formula for selection: ind.prob. = x[3] / (2 ** x[4])
                last_tokens.append([story_id, permn, index, int(tokens[-1]), var_len, enum, fols])
            else:
                last_tokens.append([story_id, permn, index, int(tokens[-1]), var_len, enum, fols])

    return last_tokens

def move_txt():
    #Move .txt files to another directory.

    # Define the source and destination directories
    source_dir = "WCNC/dimac_cnfs_deduc"
    destination_dir = "WCNC/dimac_cnfs_deduc_res"

    # Ensure the destination directory exists
    if not os.path.exists(destination_dir):
        os.makedirs(destination_dir)

    # Iterate over all files in the source directory
    for filename in os.listdir(source_dir):
        # Check if the file has a .txt extension
        if filename.endswith(".txt"):
            # Construct full file paths
            source_file = os.path.join(source_dir, filename)
            destination_file = os.path.join(destination_dir, filename)

            # Move the file
            shutil.move(source_file, destination_file)
            print(f"Moved: {filename}")

    print("All .txt files have been moved.")

def calc_inductive_probs(last_tokens):
    last_tokens = sorted(last_tokens, key=lambda x: x[3])

    for element in last_tokens:
        print([element[-1]])



if __name__ == '__main__':

    file_path = '/WCNC/Dataset\\story10.jsonl'  #'deduc_dataset_v2.jsonl'
    df_f = pd.read_json(file_path, lines=True)

    lst = df_f.values.tolist()
    stories = []
    story_ids = []
    id_cnt = 0
    for i in lst:
        stories.append([i[0]])
        story_ids.append(id_cnt)
        id_cnt += 1


    # As FOLIO dataset is a logical reasoning dataset, there exists multiple examples with the same story (i.e.,
    # same premises) but with different conclusions. Check story_id & skip if a particular story is already included,
    # append all others to a separate list.

    #stories, story_ids = read_stories(dataframe=df_f)

    # Extract all FOL sentences from the stories list into a flat list. Then, eliminate all with multiple quantifiers
    # as the code needs to be implemented before their inclusion.
    story_flat = flatten_stories(story_arr=stories)

    unique_predicates, unique_grounded_entities, unique_variable_entities, num_enum, enums_per_story = unique_elements(stories)

    # Below, first the FOL expressions are parsed into NLTK trees via func.'s in fol_parser_old.py (Yuan's custom code that
    # I modified). Then, replace logical operations of bijunction, implication, and xor operations with operators
    # from minimal set of {and, or, not}. Also, a few corrections in predicate names are done. Third, # of quantifiers
    # are computed with a utility function. Finally, enumerations are generated, and for each term in the trees, the
    # enumeration order is calculated.

    df_c, term_orders, there_exists = get_term_orders(story_flat_arr=story_flat)

    story_id = 0
    last_tokens = []
    for ikj in range(len(term_orders)):

        selected_elements = []
        selected_bools = []
        selected_quant_qual = []
        selected_truth_t = []
        selected_fol = []
        selected_there_exists = there_exists[ikj]

        for dictionary in term_orders[ikj]:
            selected_elements.append(list(dictionary.values()))

        for element in df_c[ikj]:
            selected_bools.append(element[1])
            selected_quant_qual.append(element[2])
            selected_truth_t.append(element[3])
            selected_fol.append(element[0])
        item_count = {}


        if selected_elements is not None:
            permn = 0
            tmp_exists = 0
            for iteration in range(1, len(selected_elements)+1):
                comb = combinations(range(len(selected_elements)), iteration)
                for index in list(comb):
                    combin = []
                    combin_t = []
                    rev_p_t = []
                    fols = []
                    for indexy in list(index):
                        combin.append(selected_elements[indexy])
                        combin_t.append(selected_truth_t[indexy])
                        rev_p_t.append(selected_there_exists[indexy])
                        fols.append(selected_fol[indexy])

                    variables = list(set(sum(combin, [])))
                    selected_dimacs = []
                    selected_clauses = []

                    for im in range(len(combin_t)):
                        dimacs, clauses = truth_table_to_cnf_dimacs(combin_t[im], combin[im], variables, reduce(lambda x, y: x ^ y, rev_p_t))
                        selected_dimacs.append(dimacs)
                        selected_clauses.append(clauses)

                    for jj in range(len(selected_clauses)):
                        if selected_clauses[jj] is None:
                            selected_clauses[jj] = []

                    #print(len(variables))
                    #num_elem = len(list(sum(selected_clauses, [])))
                    #write_dimacs_to_file_deduc(selected_clauses, story_id, permn, num_elem, 3005)#len(variables))
                    #script_for_ubuntu(story_id=story_id, permn=permn)

                    last_tokens = get_tokens(story_id=story_id, permn=permn, last_tokens=last_tokens, var_len=len(variables), enum=enums_per_story[story_id], thereex=rev_p_t, fols =fols)
                    permn += 1
        story_id += 1

    #move_txt()
    calc_inductive_probs(last_tokens)
