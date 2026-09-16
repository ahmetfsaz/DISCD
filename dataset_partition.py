import numpy as np
import random

def merge_list(ls_ls):
    output = []
    for ls in ls_ls:
        output += ls
    return output

def split_list_into_pieces(all_indices, num_pieces):
    indices_per_piece = len(all_indices) // num_pieces
    index_pieces = [all_indices[i:i + indices_per_piece] for i in range(0, len(all_indices), indices_per_piece)]
    if len(index_pieces)>num_pieces:
        output = index_pieces[:num_pieces-1] + [merge_list(index_pieces[num_pieces-1:])]
    else:
        output = index_pieces
    return output


def dataset_repetition(edges, num_partitions):
    np.random.shuffle(edges)
    all_indices = list(range(len(edges)))
    idx_ls = split_list_into_pieces(all_indices, num_partitions)
    output = []
    for c in range(num_partitions):
        # add repetition
        c1 = random.randint(0, num_partitions-1)
        x = edges[idx_ls[c1]].copy()
        np.random.shuffle(x)

        output.append(np.vstack((edges[idx_ls[c]], x[:int(len(x) * 0.1)])))

    return output


with open('/Users/asaz/PycharmProjects/pythonProject2/YAGO3-10.txt') as file:
    data = file.readlines()

count = 0

triples = []
for line in data:
    s, r, o = line.strip().split('\t')
    print(s, ' ', r, ' ', o)
    triples.append([s, r, o])
    count += 1
    if count == 10:
        break

triples = np.array(triples)

output = dataset_repetition(triples, 5)
for c in range(5):
    print(output[c])