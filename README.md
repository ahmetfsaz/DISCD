# DISCD: Distributed Lossy Semantic Communication for Logical Deduction of Hypothesis

Code and dataset for:

> **DISCD: Distributed Lossy Semantic Communication for Logical Deduction of Hypothesis**
> Ahmet Faruk Saz, Siheng Xiong, Faramarz Fekri — *IEEE ICMLCN 2025*
> [arXiv:2502.05744](https://arxiv.org/abs/2502.05744)

## Overview

A distributed network of nodes each holds a partial, possibly overlapping view of the State of
the World, and each must decide which of several hypotheses that state best supports. No node
can decide reliably alone, and bandwidth is limited, so nodes exchange first-order logic
sentences through a central server across iterative rounds.

DISCD selects what to send by semantic content rather than at random. Each node transmits the
sentence that leaves least uncertainty about the world state, given what it has already sent
and received; the server aggregates, updates its own view, and broadcasts back the most
informative sentence it can. As rounds accumulate, node posteriors converge toward the true
distribution over the state space, and the paper derives a PAC bound on the sample size needed
to identify the minimal constituent.

The obstacle is scale. With 15 predicates over 40 entities, the state space is far too large to
enumerate, so inductive logical probabilities are computed by counting satisfying models of a
Boolean encoding rather than by direct enumeration.

## Repository structure

```
DISCD/
├── ICMLCN.py          # Main experiment script
├── utilities.py       # FOL parsing, CNF conversion, file I/O helpers
├── bin_tree.py        # Binary tree structures for model counting
└── Dataset/
    ├── User1.jsonl    # Node 1's evidence — 40 FOL sentences
    ├── ...
    └── User10.jsonl   # Node 10's evidence
```

## Dataset

Ten nodes, each holding 40 sentences of a shared story. Roughly 30% of a node's sentences are
shared with at least one other node; the remaining 70% are unique to it, so no node sees the
whole story. The task at each node is to determine which of 8 disjoint hypotheses holds for the
entities it can see.

Each line is one sentence, in first-order logic with a natural language gloss:

```json
{"FOL": "∀x ∀y (IsMarriedTo(x, y) → IsFriendOf(x, y))", "NL": "Married couples are friends."}
{"FOL": "WorksAs(Emma, Doctor) ∧ LivesIn(Emma, London)", "NL": "Emma works as a doctor and lives in London."}
```

The vocabulary is 15 predicates over 40 entities, declared at the top of `ICMLCN.py`.

## Requirements

```bash
pip install pandas nltk
```

Model counting is performed by [sharpSAT-td](https://github.com/Laakeri/sharpsat-td), an
exact model counter for Boolean formulas. Build it separately and make the binary available on
your path.

## Running

```bash
python3 ICMLCN.py
```

The script iterates over all ten nodes. Intermediate DIMACS CNF files are written to
`dimac_cnfs/` and moved to `dimac_cnfs_res/` once counted, so create both directories first:

```bash
mkdir -p dimac_cnfs dimac_cnfs_res
```

Parameters are set inside the script rather than on the command line. The message budget `B`
and the number of communication rounds are the two worth changing first; the paper reports
`B = 1` and `B = 2` over 40 rounds.

## How it works

1. **Parse.** FOL sentences are parsed into NLTK trees, and implication, biconditional, and
   XOR are rewritten using only conjunction, disjunction, and negation.
2. **Ground.** Quantifiers are expanded into grounded expressions over the entity set, and term
   enumeration orders are computed for each tree.
3. **Encode.** Each sentence is converted to conjunctive normal form and written as DIMACS CNF.
4. **Count.** A model counter returns the number of world states satisfying each sentence,
   which yields its inductive logical probability.
5. **Select.** The node transmits the sentence with the highest degree of confirmation given
   what has already been exchanged. Probabilities are recomputed each round to account for
   prior transmissions.

Random message selection is implemented alongside the content-based rule for comparison.

## Citation

```bibtex
@inproceedings{saz2025discd,
  title     = {{DISCD}: Distributed Lossy Semantic Communication for Logical Deduction of Hypothesis},
  author    = {Saz, Ahmet Faruk and Xiong, Siheng and Fekri, Faramarz},
  booktitle = {IEEE International Conference on Machine Learning for Communication and Networking (ICMLCN)},
  year      = {2025}
}
```
