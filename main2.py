import sys
import os
from collections import Counter
import huffman
from scipy.stats import entropy
import numpy as np
from matplotlib import pyplot as plt
from decimal import Decimal, getcontext

def norm_cont_entropy_decimal(num_s, num_r, num_o, length):
    # Set the precision (you can adjust this as needed)
    getcontext().prec = 1000

    num_e = (num_s + num_o)
    compatible = Decimal('2')**(Decimal(num_r) * Decimal(num_e) - Decimal(length))
    prior = Decimal('0.5')**(Decimal(num_r) * Decimal(num_e))

    return ((Decimal('1') / compatible) - prior) / (compatible * prior)
def norm_cont_entropy_alt(num_s, num_r, num_o, length):
    # Set the precision (you can adjust this as needed)
    getcontext().prec = 1000
    return Decimal('2')**(Decimal('2') * Decimal(length)) - Decimal('2')**(Decimal(length))

def norm_cont_entropy_alt2(num_s, num_r, num_o, length):
    # Set the precision (you can adjust this as needed)
    getcontext().prec = 1000
    num_e = Decimal(num_s) + Decimal(num_o)
    num_t = Decimal('0.5')*(Decimal(num_r) * (Decimal(num_e) * (Decimal(num_e) - Decimal('1'))))
    return Decimal('2')**(Decimal(length) - Decimal(num_t)) * (Decimal('2') ** Decimal(length) - Decimal('1'))
# Define the lambda function
def lambda_w(w):
    # Placeholder for the actual implementation of lambda(w)
    # This should be replaced with the actual function definition.
    return w  # This is just a placeholder, replace with the actual function

# Define the main function that uses lambda_w
def calculate_probability(nj, n, w1, w2):
    return (nj + 2 * lambda_w(w1) / w2) / (n + lambda_w(w1))

def modify_file(file_path):
    # Read the file
    with open(file_path, 'r') as file:
        content = file.read()

    # Replace commas with comma followed by a space
    modified_content = content.replace(', ', ',')

    # Write the modified content back to the file
    with open(file_path, 'w') as file:
        file.write(modified_content)

def norm_cont_entropy(num_s, num_r, num_o, length):
    num_e = num_s + num_o
    compatible = 1/2**((num_r * num_e) - length)
    prior = 1/2**(num_r * num_e)
    return ((1 / compatible) - prior) / (compatible * prior)

# Press the green button in the gutter to run the script.
if __name__ == '__main__':

    file_paths1 = ['dataset_exp1/facts_0.txt', 'dataset_exp1/facts_1.txt', 'dataset_exp1/facts_2.txt', 'dataset_exp1/facts_3.txt', 'dataset_exp1/facts_4.txt', 'dataset_exp1/facts_5.txt', 'dataset_exp1/facts_6.txt']
    file_paths2 = ['dataset_exp1/story_0.txt', 'dataset_exp1/story_1.txt', 'dataset_exp1/story_2.txt', 'dataset_exp1/story_3.txt', 'dataset_exp1/story_4.txt', 'dataset_exp1/story_5.txt', 'dataset_exp1/story_6.txt']
    r_costs = []
    s_cost = []
    r_cost =[]
    H_cont = []
    for ijk in range(7):
        file_path1 = file_paths1[ijk]
        file_path2 = file_paths2[ijk]
        with open(file_path1) as file1:
            data1 = file1.readlines()

        with open(file_path2) as file2:
            data2 = file2.read()

        # Print first 10 lines of YAGO3
        '''
        count = 0
        for line in data:
            s, r, o = line.split(',')
            #print(s, ' ', r, ' ', o)
            count += 1
            if count == 10:
                break
        '''


        # Initialize sets to store unique subjects, relations, and objects.
        unique_subjects = set()
        unique_relations = set()
        unique_objects = set()

        FOL_parts = []
        # Read the file and process each line. Append relations in a separate file.
        with open(file_path1, 'r') as file:
            for line in file:
                # Splitting each line into subject, relation, object
                parts = line.strip().split(',')
                if len(parts) == 3:
                    FOL_parts.append(parts)
                    subject, relation, object = parts
                    unique_subjects.add(subject)
                    unique_relations.add(relation)
                    unique_objects.add(object)

        # Counting the number of unique elements in each category
        num_unique_subjects = len(unique_subjects)
        num_unique_relations = len(unique_relations)
        num_unique_objects = len(unique_objects)

        print('Num Subjects: ', num_unique_subjects, '  ', 'Num Relations: ',  num_unique_relations, '  ', 'Num Objects: ', num_unique_objects)


        # Initialize counters for subjects, relations, and objects.
        subject_counter = Counter()
        relation_counter = Counter()
        object_counter = Counter()

        num_samples_YAGO = 0
        # Read the file and count occurrences of each subject, relation, and object.
        with open(file_path1, 'r') as file:
            for line in file:
                parts = line.strip().split(',')
                if len(parts) == 3:
                    num_samples_YAGO += 1
                    subject, relation, object = parts
                    subject_counter[subject] += 1
                    relation_counter[relation] += 1
                    object_counter[object] += 1

        print(subject_counter)
        print(relation_counter)
        print(object_counter)

        # Example usage:
        # This is just an example with placeholder values since the actual lambda(w) is not defined.
        result_prob_our_rel = []
        result_prob_our_sbj = []
        result_prob_our_obj = []

        counter_items_sbj = sorted(list(subject_counter.items()))
        counter_items_rel = sorted(list(relation_counter.items()))
        counter_items_obj = sorted(list(object_counter.items()))
        for i in range(len(counter_items_sbj)):
            result_prob_our_sbj.append(calculate_probability(counter_items_sbj[i][1], num_samples_YAGO, 1, 1))
        for i in range(len(counter_items_rel)):
            result_prob_our_rel.append(calculate_probability(counter_items_rel[i][1], num_samples_YAGO, 1, 1))
        for i in range(len(counter_items_obj)):
            result_prob_our_obj.append(calculate_probability(counter_items_obj[i][1], num_samples_YAGO, 1, 1))


        print('Our Probabilities Subjects: ', result_prob_our_sbj)
        print('Our Probabilities Relations: ', result_prob_our_rel)
        print('Our Probabilities Objects: ', result_prob_our_obj)

        sorted_counter_sbj = sorted(subject_counter.items())
        print('Sorted Counter Our Subj: ', sorted_counter_sbj)
        codebook_sbj = huffman.codebook(sorted_counter_sbj)
        print('Huffman Codebook Our Subj: ',codebook_sbj)

        sorted_counter_rel = sorted(relation_counter.items())
        print('Sorted Counter Our Rel: ', sorted_counter_rel)
        codebook_rel = huffman.codebook(sorted_counter_rel)
        print('Huffman Codebook Our Rel: ', codebook_rel)

        sorted_counter_obj = sorted(object_counter.items())
        print('Sorted Counter Our Obj: ', sorted_counter_obj)
        codebook_obj = huffman.codebook(sorted_counter_obj)
        print('Huffman Codebook Our Obj: ', codebook_obj)

        avg_our_sbj = 0
        num_bit_sbj = 0
        codb_our_sbj= []
        for item in codebook_sbj.items():
            codb_our_sbj.append(len(item[1]))
        for i in range(len(codb_our_sbj)):
            avg_our_sbj += codb_our_sbj[i]*result_prob_our_sbj[i]
            num_bit_sbj += codb_our_sbj[i] * (sorted_counter_sbj[i][1])
        print('AVG CW LENGTH OUR SBJ', avg_our_sbj)
        print('TOTAL BITS SBJ', num_bit_sbj)
        print('ENTROPY OUR SBJ', entropy(result_prob_our_sbj, base=2))

        avg_our_rel = 0
        num_bit_rel = 0
        codb_our_rel = []
        for item in codebook_rel.items():
            codb_our_rel.append(len(item[1]))
        for i in range(len(codb_our_rel)):
            avg_our_rel += codb_our_rel[i] * result_prob_our_rel[i]
            num_bit_rel += codb_our_rel[i] * (sorted_counter_rel[i][1])
        print('AVG CW LENGTH OUR REL', avg_our_rel)
        print('TOTAL BITS REL', num_bit_rel)
        print('ENTROPY OUR REL', entropy(result_prob_our_rel, base=2))

        avg_our_obj = 0
        num_bit_obj = 0
        codb_our_obj = []
        for item in codebook_obj.items():
            codb_our_obj.append(len(item[1]))
        for i in range(len(codb_our_obj)):
            avg_our_obj += codb_our_obj[i] * result_prob_our_obj[i]
            num_bit_obj += codb_our_obj[i] * (sorted_counter_obj[i][1])
        print('AVG CW LENGTH OUR OBJ', avg_our_obj)
        print('TOTAL BITS OBJ', num_bit_obj)
        print('ENTROPY OUR OBJ', entropy(result_prob_our_obj, base=2))

        tot_bit_our = num_bit_sbj + num_bit_rel + num_bit_obj
        print('TOTAL BITS OURS', tot_bit_our)

        ranking = []
        for sro in FOL_parts:
            s, r, o = sro[0], sro[1], sro[2]
            len_s = len(codebook_sbj[s])
            pr_s = result_prob_our_sbj[list(dict(counter_items_sbj).keys()).index(s)]
            len_r = len(codebook_rel[r])
            pr_r = result_prob_our_rel[list(dict(counter_items_rel).keys()).index(r)]
            len_o = len(codebook_obj[o])
            pr_o = result_prob_our_obj[list(dict(counter_items_obj).keys()).index(o)]
            cost_sro = len_s * 1 + len_r * 1 + len_o * 1
            ranking.append([cost_sro, sro])

        ranking = sorted(ranking)
        running_cost = [ranking[0][0]]
        for i in range(1, len(ranking)):
            running_cost.append(running_cost[i-1] + ranking[i][0])

        RUNNING_COST = np.array(running_cost)
        r_costs.append(RUNNING_COST)
        print('XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX')



        ############################################################################################################
        ############################################################################################################
        ############################################################################################################
        # Compute for Shannon
        sorted_shannon = sorted(Counter(data2).items())
        codebook2 = huffman.codebook(sorted_shannon)
        print('Sorted Counter Shannon: ', sorted_shannon)
        print('Huffman Codebook Shannon: ', codebook2)
        print('Number of Elements Shannon: ', len(data2))

        avg_shn = 0
        num_bit_shn = 0
        codb_shn = []
        for item in codebook2.items():
            codb_shn.append(len(item[1]))
        probs_shn = []
        for i in range(len(codb_shn)):
            avg_shn += codb_shn[i] * (sorted_shannon[i][1]/len(data2))
            num_bit_shn += codb_shn[i] * (sorted_shannon[i][1])
            probs_shn.append(sorted_shannon[i][1]/len(data2))
        print('AVG CW LENGTH SHN', avg_shn)
        print('TOTAL BITS SHN', num_bit_shn)
        print('ENTROPY SHN', entropy(probs_shn, base=2))

        #Experiment with various values of lambda

        lambdas = np.logspace(0.0, 30.0, num=31, base=2.0)
        #print('Lambdas:', lambdas)

        for j in range(len(lambdas)):
            result_prob_lamb = []
            counter_items = sorted(list(subject_counter.items()))
            for i in range(len(counter_items)):
                result_prob_lamb.append(calculate_probability(counter_items[i][1], num_samples_YAGO, lambdas[j], 1))
            print('LambdaS = ', lambdas[j], ' ENTROPYS: ', entropy(result_prob_lamb, base=2))

        for j in range(len(lambdas)):
            result_prob_lamb = []
            counter_items = sorted(list(relation_counter.items()))
            for i in range(len(counter_items)):
                result_prob_lamb.append(calculate_probability(counter_items[i][1], num_samples_YAGO, lambdas[j], 1))
            print('LambdaR = ', lambdas[j], ' ENTROPYR: ', entropy(result_prob_lamb, base=2))

        for j in range(len(lambdas)):
            result_prob_lamb = []
            counter_items = sorted(list(object_counter.items()))
            for i in range(len(counter_items)):
                result_prob_lamb.append(calculate_probability(counter_items[i][1], num_samples_YAGO, lambdas[j], 1))
            print('LambdaO = ', lambdas[j], ' ENTROPYO: ', entropy(result_prob_lamb, base=2))

        print('AVG CW LENGTH OUR SBJ', avg_our_sbj)
        print('TOTAL BITS SBJ', num_bit_sbj)
        print('ENTROPY OUR SBJ', entropy(result_prob_our_sbj, base=2))

        print('AVG CW LENGTH OUR REL', avg_our_rel)
        print('TOTAL BITS REL', num_bit_rel)
        print('ENTROPY OUR REL', entropy(result_prob_our_rel, base=2))

        print('AVG CW LENGTH OUR OBJ', avg_our_obj)
        print('TOTAL BITS OBJ', num_bit_obj)
        print('ENTROPY OUR OBJ', entropy(result_prob_our_obj, base=2))

        print('AVG CW LENGTH SHN', avg_shn)
        print('ENTROPY SHN', entropy(probs_shn, base=2))

        print('TOTAL BITS OURS', tot_bit_our)
        print('TOTAL BITS SHN', num_bit_shn)
        s_cost.append(num_bit_shn)
        r_cost.append(tot_bit_our)

        ns = num_unique_subjects
        nr = num_unique_relations
        no = num_unique_objects
        nt = num_samples_YAGO
        H_cont.append(norm_cont_entropy_alt2(ns, nr, no, nt))

    print(r_costs)
    print(r_cost)
    print(s_cost)
    x = np.linspace(0, 1, 100)

    colors = ['b', 'g', 'r', 'c', 'm', 'y', 'k']  # blue, green, red, cyan, magenta, yellow, black
    labels = ['Story 1', 'Story 2', 'Story 3', 'Story 4', 'Story 5', 'Story 6', 'Story 7']

    # Plotting each pair of data lines
    plt.plot(x, r_costs[0], color=colors[0], label=labels[0])
    #plt.plot(x, np.array([s_cost[0]] * 100), color=colors[0],
    #         linestyle='dashed')  # dashed line for the second line in each pair

    # Plotting each pair of data lines
    plt.plot(x, r_costs[1], color=colors[1], label=labels[1])
    #plt.plot(x, np.array([s_cost[1]] * 100), color=colors[1],
    #         linestyle='dashed')  # dashed line for the second line in each pair

    # Plotting each pair of data lines
    plt.plot(np.linspace(0, 1, 90), r_costs[2], color=colors[2], label=labels[2])
    #plt.plot(np.linspace(0, 1, 90), np.array([s_cost[2]] * 90), color=colors[2],
    #         linestyle='dashed')  # dashed line for the second line in each pair

    # Plotting each pair of data lines
    plt.plot(x, r_costs[3], color=colors[3], label=labels[3])
    #plt.plot(x, np.array([s_cost[3]] * 100), color=colors[3],
    #         linestyle='dashed')  # dashed line for the second line in each pair

    # Plotting each pair of data lines
    plt.plot(np.linspace(0, 1, 96), r_costs[4], color=colors[4], label=labels[4])
    #plt.plot(np.linspace(0, 1, 96), np.array([s_cost[4]] * 96), color=colors[4],
    #         linestyle='dashed')  # dashed line for the second line in each pair

    # Plotting each pair of data lines
    plt.plot(x, r_costs[5], color=colors[5], label=labels[5])
    #plt.plot(x, np.array([s_cost[5]] * 100), color=colors[5],
    #         linestyle='dashed')  # dashed line for the second line in each pair

    # Plotting each pair of data lines
    plt.plot(np.linspace(0, 1, 99), r_costs[6], color=colors[6], label=labels[6])
    #plt.plot(np.linspace(0, 1, 99), np.array([s_cost[6]] * 99), color=colors[6],
    #         linestyle='dashed')  # dashed line for the second line in each pair

    #plt.title('Random Data Plot')
    plt.xlabel('Relativized Cont-Information')
    plt.ylabel('Number of Bits')
    plt.legend()  # Display the legend
    plt.savefig('plot.eps', format='eps', dpi=1000)  # Adjust dpi for higher or lower quality

    plt.show()
    max_H = max(H_cont)
    rel_H = []
    for i in range(len(H_cont)):
        rel_H.append(H_cont[i] / Decimal(max_H))
    print(rel_H)