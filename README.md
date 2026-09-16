# DISCD: Distributed Lossy Semantic Communication for Logical Deduction of Hypothesis

First-order logic semantic communication for hypothesis deduction. This repository holds the
code for two papers, which share a common pipeline and are separated below:

> **[WCNC] Lossy Semantic Communication for the Logical Deduction of the State of the World**
> Ahmet Faruk Saz, Siheng Xiong, Faramarz Fekri — *IEEE WCNC 2025*
> [arXiv:2410.01676](https://arxiv.org/abs/2410.01676)
>
> **[ICMLCN] DISCD: Distributed Lossy Semantic Communication for Logical Deduction of Hypothesis**
> Ahmet Faruk Saz, Siheng Xiong, Faramarz Fekri — *IEEE ICMLCN 2025*
> [arXiv:2502.05744](https://arxiv.org/abs/2502.05744)

The WCNC paper develops the point-to-point case: a transmitter with partial evidence and no
knowledge of the receiver's task sends the messages that most reduce the receiver's uncertainty
about the state of the world. The ICMLCN paper extends this to a distributed network, where
nodes hold partial, overlapping views and exchange first-order logic sentences through a central
server across iterative rounds.

## Method

The state of the world is represented in first-order logic, and the informativeness of a message
is measured by how much it narrows the set of world states consistent with the evidence. Under
Carnap and Hintikka's inductive logic, that requires the inductive probability of each candidate
message, which in turn requires counting how many world states satisfy it.

Direct enumeration is impossible: with `|P|` predicates over `|E|` entities the state space has
`2^(|P|×|E|²)` members. The pipeline instead converts each FOL sentence to conjunctive normal
form and hands the counting to an exact model counter, which prunes unsatisfiable branches
rather than enumerating assignments. The counts yield inductive probabilities, and the message
with the highest degree of confirmation is transmitted.

## Repository structure

```
DISCD/
├── fol_parser.py              # Shared: FOL parsing, grounding, CNF and DIMACS output
├── bin_tree.py                # Shared: binary tree structures for model counting
├── utilities.py               # Shared: dataset loading and helpers
│
├── WCNC.py                    # [WCNC] Compression and uncertainty reduction on FOLIO
├── WCNC_deduc.py              # [WCNC] Hypothesis deduction on the custom corpus
├── VAE.py                     # [WCNC] Baseline: GPT-2 autoencoder
├── Huffman.py                 # [WCNC] Baseline: Huffman coding
│
├── ICMLCN.py                  # [ICMLCN] Distributed communication across nodes
├── ICMLCN_deduc.py            # [ICMLCN] Distributed hypothesis deduction
│
├── folio-train.jsonl          # [WCNC] FOLIO, 1004 records
├── deduc_dataset_v2.jsonl     # [WCNC] Custom deduction corpus, 30 stories
└── Dataset/User1–10.jsonl     # [ICMLCN] Ten nodes, 40 FOL sentences each
```

The three shared modules are used by both papers. `fol_parser.py` carries the parsing and
encoding pipeline: it converts FOL text to NLTK trees, rewrites implication, biconditional and
XOR into conjunction, disjunction and negation, grounds quantifiers over the entity set, builds
truth tables, and writes DIMACS CNF for the model counter.

## Data

**FOLIO** (`folio-train.jsonl`) supplies natural language premises with their first-order logic
translations. The WCNC experiments deduplicate by `story_id`, treating each story as an
independent world, and drop premises mixing universal and existential quantifiers.

**The custom deduction corpus** (`deduc_dataset_v2.jsonl`) holds stories describing a population
of entities through their attributes and relations. The receiver must decide which of eight
disjoint hypotheses holds for that population, given only what the transmitter sends.

**The distributed dataset** (`Dataset/User1–10.jsonl`) splits one story across ten nodes at 40
sentences each. Around 30% of a node's sentences are shared with at least one other node and the
rest are unique to it, so no node sees the whole story. Each line pairs a first-order logic
sentence with its natural language gloss:

```json
{"FOL": "∀x ∀y (IsMarriedTo(x, y) → IsFriendOf(x, y))", "NL": "Married couples are friends."}
```

## Requirements

```bash
pip install pandas numpy nltk huffman dahuffman torch transformers
```

`torch` and `transformers` are needed only by `VAE.py`; `dahuffman` only by `Huffman.py`.

Model counting is performed by [sharpSAT-td](https://github.com/Laakeri/sharpsat-td), an exact
model counter using tree decompositions. Build it separately and note the path to the binary.

## Running

The experiments run in two stages, because model counting happens outside Python.

**Stage 1 — generate the CNF instances.** Create the working directories, then run the script
for the experiment you want:

```bash
mkdir -p dimac_cnfs dimac_cnfs_res dimac_cnfs_deduc dimac_cnfs_deduc_res

python3 WCNC.py           # [WCNC] FOLIO compression
python3 WCNC_deduc.py     # [WCNC] hypothesis deduction
python3 ICMLCN.py         # [ICMLCN] distributed communication
python3 ICMLCN_deduc.py   # [ICMLCN] distributed deduction
```

This writes one DIMACS file per candidate message subset into `dimac_cnfs/` (or
`dimac_cnfs_deduc/` for the deduction variants), and accumulates the matching model-counter
invocations in `script.txt`.

**Stage 2 — count the models.** Run the accumulated commands with sharpSAT-td available on your
path. Each writes its count to `dimac_cnfs_res/output_{story}_{permutation}.txt`, which the
Python side reads back to compute inductive probabilities and select messages.

Paths inside `script.txt` are absolute and will need adjusting for your machine.

**Baselines** run standalone and need neither stage:

```bash
python3 Huffman.py        # Huffman coding over FOLIO premises
python3 VAE.py            # GPT-2 autoencoder compression
```

Parameters are set inside each script rather than passed on the command line.

## Which script produces what

### `WCNC.py`

The point-to-point experiment. For each FOLIO story it enumerates candidate message subsets,
scores each by content-informativeness under inductive probability, and transmits the most
informative subset within a bit budget. Reports the reduction in receiver uncertainty against
communication cost, compared with Huffman coding, GPT-2 autoencoding, and random selection.

### `WCNC_deduc.py`

The downstream task. The receiver chooses among eight disjoint hypotheses about a population
using only the transmitted sentences, and accuracy is measured as the share of the population
for which the selected hypothesis predicts the correct properties.

### `ICMLCN.py`

The distributed case. Each node selects the sentence leaving least uncertainty about the state
of the world given what it has already sent and received; the server aggregates all incoming
messages, updates its own view, and broadcasts back the most informative sentence it can. Node
posteriors converge toward the true distribution as rounds accumulate.

### `ICMLCN_deduc.py`

Hypothesis deduction in the distributed setting, measuring success rate against communication
rounds under fixed per-round message budgets.

### `VAE.py` and `Huffman.py`

Learned and classical compression baselines over the same FOLIO premises, standing in for
approaches that compress effectively but give no account of which logical content survives.

## Citation

```bibtex
@inproceedings{saz2025lossy,
  title     = {Lossy Semantic Communication for the Logical Deduction of the State of the World},
  author    = {Saz, Ahmet Faruk and Xiong, Siheng and Fekri, Faramarz},
  booktitle = {IEEE Wireless Communications and Networking Conference (WCNC)},
  year      = {2025}
}

@inproceedings{saz2025discd,
  title     = {{DISCD}: Distributed Lossy Semantic Communication for Logical Deduction of Hypothesis},
  author    = {Saz, Ahmet Faruk and Xiong, Siheng and Fekri, Faramarz},
  booktitle = {IEEE International Conference on Machine Learning for Communication and Networking (ICMLCN)},
  year      = {2025}
}
```
