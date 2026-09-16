import sys
from utilities_SPAWC import *
from bin_tree import *
from itertools import combinations

# Press the green button in the gutter to run the script.
if __name__ == '__main__':

    file_path = 'folio-train.jsonl'
    df_f = pd.read_json(file_path, lines=True)

    story_ids = []
    stories = []
    for i in range(len(df_f)):
        if df_f['story_id'][i] in story_ids:
            continue
        else:
            stories.append(df_f['premises-FOL'][i])
        story_ids.append(df_f['story_id'][i])

    df_f = stories
    df_temp = []

    for i in range(len(df_f)):
        story_arr = df_f[i]
        curr_FOL = []
        gr_en, var_en = get_all_entities(story_arr)
        for j in range(len(story_arr)):
            fol_expression = story_arr[j]
            if contains_quantifiers(fol_expression):
                if not contains_both_quantifiers(fol_expression):
                    curr_FOL.append(fol_expression)
            else:
                curr_FOL.append(fol_expression)
        df_temp.append([curr_FOL, gr_en, var_en])

    # Extract predicates from each FOL expression
    unique_predicates = set()
    unique_grounded_entities = set()
    unique_variable_entities = set()
    for index in range(len(df_f)):
        arr = df_f[index]
        for j in range(len(arr)):
            fol_expression = arr[j]
            tree = parse_text_FOL_to_tree(fol_expression)
            if tree is not None:
                predicates = extract_predicates_from_tree(tree)
                unique_predicates.update(predicates)
                gronded_entities = extract_grounded_entities_from_tree(tree)
                unique_grounded_entities.update(gronded_entities)
                variable_entities = extract_variable_entities_from_tree(tree)
                unique_variable_entities.update(variable_entities)

    # Convert the set to a list
    unique_predicates = sorted(list(unique_predicates))
    unique_grounded_entities = sorted(list(unique_grounded_entities))
    unique_variable_entities = sorted(list(unique_variable_entities))

    # Print or return the list of predicates
    print("Unique Predicates: ", unique_predicates)
    print("Unique Grounded Entities: ", unique_grounded_entities)
    print("Unique Variable Entities: ", unique_variable_entities)
    print("Number of Unique Predicates: ", len(unique_predicates))
    print("Number of Unique Grounded Entities: ", len(unique_grounded_entities))
    print("Number of Unique Variable Entities: ", len(unique_variable_entities))
    print("Number of Enumerations: ", (len(unique_grounded_entities)**2) * len(unique_predicates))

    num_enum = (len(unique_grounded_entities) ** 2) * len(unique_predicates)

    df_c = []
    term_orders = []
    for subarray in df_temp:
        sub_expr = subarray[0]
        sub_gr = subarray[1]
        temp_arr = []
        temp_arr_ord = []
        for k in range(len(sub_expr)):
            fol_expression = sub_expr[k]
            tree = parse_text_FOL_to_tree(fol_expression)
            if tree is not None:
                isFOL, lvars, consts, preds = symbol_resolution(tree)
                rule = Rule(isFOL, lvars, consts, preds, tree, sub_gr)  # Assuming the Rule constructor
                rule.replace_logical_operations()
                num_q = num_quantifiers(rule.rule_str())
                rule.generate_enumerations()
                rule.calculate_term_orders(unique_predicates, unique_grounded_entities)
            variables, truth_table = compute_truth_table(rule)
            cnf, bin_reps = truth_table_to_cnf(truth_table, variables)
            temp_arr.append([fol_expression, bin_reps, cnf, truth_table])
            temp_arr_ord.append(rule.term_orders)
        df_c.append(temp_arr)
        term_orders.append(temp_arr_ord)

    story_id = 0
    lemn = 1000
    for ikj in range(len(term_orders)):
        root = None
        repeated = []

        selected_elements = []
        selected_bools = []
        selected_quant_qual = []
        selected_truth_t = []
        selected_fol = []

        for dictionary in term_orders[ikj]:
            selected_elements.append(list(dictionary.values()))
        for element in df_c[ikj]:
            selected_bools.append(element[1])
            selected_quant_qual.append(element[2])
            selected_truth_t.append(element[3])
            selected_fol.append(element[0])
        item_count = {}

        if len(selected_elements) < lemn:
            lemn = len(selected_elements)
        if selected_elements is not None:
            print(selected_elements)
            permn = 0
            for itt in range(len(selected_elements)):
                comb = combinations(range(len(selected_elements)), itt)#len(selected_elements))
                #for index in range(len(selected_elements[:3])):
                for index in list(comb):
                    arr = selected_elements
                    combin = []
                    combin_t = []
                    for indexy in list(index):
                        combin.append(selected_elements[indexy])
                        combin_t.append(selected_truth_t[indexy])

                    variables = list(set(sum(combin, [])))
                    selected_dimacs = []
                    selected_clauses = []
                    for im in range(len(combin_t)):
                        dimacs, clauses = truth_table_to_cnf_dimacs(combin_t[im], combin[im], variables)
                        selected_dimacs.append(dimacs)
                        selected_clauses.append(clauses)
                    for jj in range(len(selected_clauses)):
                        if selected_clauses[jj] is None:
                            selected_clauses[jj] = []
                    num_elem = len(list(sum(selected_clauses, [])))

                    print(index)
                    write_dimacs_to_file(selected_clauses, story_id, permn, num_elem, len(variables))
                    permn += 1
        story_id += 1