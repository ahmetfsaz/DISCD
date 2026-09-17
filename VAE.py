"""
GPT-2 baseline for the WCNC experiments.

Tokenizes the natural-language premises of each FOLIO story with GPT-2 and
reports the cost of transmitting the token sequence, then reconstructs the text
by greedy decoding to confirm the tokens carry it. This is the learned
compression baseline the semantic scheme is measured against: a language model
compresses text efficiently, but its token sequence says nothing about which
logical content survives, so it cannot trade bits against meaning.

Emits one [story_index, bits] pair per story, for the encoded tokens and for the
original text.
"""

import argparse

import pandas as pd
from transformers import GPT2LMHeadModel, GPT2Tokenizer

# ── Configuration ────────────────────────────────────────────────────────────
DATA_PATH = "folio-train.jsonl"
MODEL_NAME = "gpt2"

MIN_PREMISES = 7      # stories shorter than this are skipped
BITS_PER_CHAR = 8     # original text, one byte per character
BITS_PER_TOKEN = 32   # one machine word per GPT-2 token id
LENGTH_BUFFER = 5     # decoding headroom beyond the prompt


def load_stories(path, min_premises=MIN_PREMISES):
    """Return the premises of each sufficiently long FOLIO story.

    FOLIO pairs one set of premises with several conclusions, so the same story
    appears in multiple records. Records are deduplicated by `story_id`, and
    stories with fewer than `min_premises` premises are dropped.
    """
    frame = pd.read_json(path, lines=True)
    stories, seen = [], set()

    for index in range(len(frame)):
        story_id = frame["story_id"][index]
        if story_id in seen:
            continue
        seen.add(story_id)

        premises = frame["premises"][index]
        if len(premises) >= min_premises:
            stories.append(premises)

    return stories


def reconstruct(text, tokenizer, model, max_length=None):
    """Tokenize `text` and decode it back, returning the reconstruction and ids.

    Decoding is greedy, so the output is deterministic. The result is trimmed to
    the length of the input, since generation runs slightly past the prompt.
    """
    input_ids = tokenizer.encode(text, return_tensors="pt")

    if max_length is None:
        max_length = len(input_ids[0]) + LENGTH_BUFFER

    generated_ids = model.generate(
        input_ids,
        max_length=max_length,
        num_return_sequences=1,
        pad_token_id=tokenizer.eos_token_id,
        do_sample=False,
    )

    decoded = tokenizer.decode(generated_ids[0], skip_special_tokens=True)
    return decoded[: len(text)], input_ids


def compression_stats(text, input_ids):
    """Return the encoded size, original size, and their ratio, all in bits."""
    original_bits = len(text) * BITS_PER_CHAR
    encoded_bits = len(input_ids[0]) * BITS_PER_TOKEN
    return encoded_bits, original_bits, original_bits / encoded_bits


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[1])
    parser.add_argument("--data", default=DATA_PATH)
    parser.add_argument("--model", default=MODEL_NAME)
    parser.add_argument(
        "--skip-reconstruction",
        action="store_true",
        help="report bit costs only, without running the model",
    )
    args = parser.parse_args()

    tokenizer = GPT2Tokenizer.from_pretrained(args.model)
    model = None if args.skip_reconstruction else GPT2LMHeadModel.from_pretrained(
        args.model
    )

    stories = load_stories(args.data)
    print(f"{len(stories)} stories with at least {MIN_PREMISES} premises\n")

    encoded_bits, original_bits = [], []
    for index, premises in enumerate(stories):
        text = " ".join(premises)

        if args.skip_reconstruction:
            input_ids = tokenizer.encode(text, return_tensors="pt")
        else:
            _, input_ids = reconstruct(text, tokenizer, model)

        encoded, original, ratio = compression_stats(text, input_ids)
        print(
            f"Story {index:>2}: {original:>6} -> {encoded:>5} bits "
            f"(ratio {ratio:.2f})"
        )

        encoded_bits.append([index, encoded])
        original_bits.append([index, original])

    print("\nEncoded bits per story:")
    print(encoded_bits)
    print("\nOriginal bits per story:")
    print(original_bits)


if __name__ == "__main__":
    main()
