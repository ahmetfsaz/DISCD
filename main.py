import sys
import os
from collections import Counter
import huffman
from scipy.stats import entropy
import numpy as np

# Define the lambda function
def lambda_w(w):
    # Placeholder for the actual implementation of lambda(w)
    # This should be replaced with the actual function definition.
    return w  # This is just a placeholder, replace with the actual function

# Define the main function that uses lambda_w
def calculate_probability(nj, n, w1, w2):
    return (nj + 2 * lambda_w(w1) / w2) / (n + lambda_w(w1))


# Press the green button in the gutter to run the script.
if __name__ == '__main__':
    with open('dataset_exp1/facts_0.txt') as file:
        data = file.readlines()

    # Print first 10 lines of YAGO3

    count = 0
    for line in data:
        s, r, o = line.split('\t')
        print(s, ' ', r, ' ', o)
        count += 1
        if count == 10:
            break


    file_path = 'YAGO3-10.txt'

    # Initialize sets to store unique subjects, relations, and objects.
    unique_subjects = set()
    unique_relations = set()
    unique_objects = set()

    rels = []
    # Read the file and process each line. Append relations in a separate file.
    with open(file_path, 'r') as file:
        for line in file:
            # Splitting each line into subject, relation, object
            parts = line.strip().split()
            if len(parts) == 3:
                subject, relation, object = parts
                rels.append(relation)
                rels.append(' ')
                unique_subjects.add(subject)
                unique_relations.add(relation)
                unique_objects.add(object)
    rels = ''.join(rels)

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
    with open(file_path, 'r') as file:
        for line in file:
            parts = line.strip().split()
            if len(parts) == 3:
                num_samples_YAGO += 1
                subject, relation, object = parts
                subject_counter[subject] += 1
                relation_counter[relation] += 1
                object_counter[object] += 1


    print(relation_counter)

    # Example usage:
    # This is just an example with placeholder values since the actual lambda(w) is not defined.
    result_prob_our = []

    counter_items = sorted(list(relation_counter.items()))
    for i in range(len(counter_items)):
        result_prob_our.append(calculate_probability(counter_items[i][1], num_samples_YAGO, 1, 1))


    print('Our Probabilities: ', result_prob_our)

    sorted_counter = sorted(relation_counter.items())
    print('Sorted Counter Our: ', sorted_counter)
    codebook = huffman.codebook(sorted_counter)
    print('Huffman Codebook Our: ',codebook)

    avg_our = 0
    codb_our= []
    for item in codebook.items():
        codb_our.append(len(item[1]))
    for i in range(len(codb_our)):
        avg_our += codb_our[i]*result_prob_our[i]
    print('AVG CW LENGTH OUR', avg_our)
    print('ENTROPY OUR', entropy(result_prob_our, base=2))

    # Compute for Shannon
    sorted_shannon = sorted(Counter(rels).items())
    codebook2 = huffman.codebook(sorted_shannon)
    print('Sorted Counter Shannon: ', sorted_shannon)
    print('Huffman Codebook Shannon: ', codebook2)
    print('Number of Elements Shannon: ', len(rels))

    avg_shn = 0
    codb_shn = []
    for item in codebook2.items():
        codb_shn.append(len(item[1]))
    probs_shn = []
    for i in range(len(codb_shn)):
        avg_shn += codb_shn[i] * (sorted_shannon[i][1]/len(rels))
        probs_shn.append(sorted_shannon[i][1]/len(rels))
    print('AVG CW LENGTH SHN', avg_shn)
    print('ENTROPY SHN', entropy(probs_shn, base=2))

    #Experiment with various values of lambda

    lambdas = np.logspace(0.0, 30.0, num=31, base=2.0)
    print('Lambdas:', lambdas)

    for j in range(len(lambdas)):
        result_prob_lamb = []
        counter_items = sorted(list(relation_counter.items()))
        for i in range(len(counter_items)):
            result_prob_lamb.append(calculate_probability(counter_items[i][1], num_samples_YAGO, lambdas[j], 37))
        print('Lambda = ', lambdas[j], ' ENTROPY: ', entropy(result_prob_lamb, base=2))
