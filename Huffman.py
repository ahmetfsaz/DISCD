"""
Huffman coding baseline for the WCNC experiments.

Compresses the natural-language premises of each FOLIO story with a per-story
Huffman code and reports the resulting bit cost. This is the classical
compression baseline the semantic scheme is measured against: it exploits
character redundancy but has no notion of which logical content a message
carries, so it cannot trade bits against meaning.

Emits one [story_index, compressed_bits] pair per story.
"""

import pandas as pd
from dahuffman import HuffmanCodec

# ── Configuration ────────────────────────────────────────────────────────────
DATA_PATH = "folio-train.jsonl"
MIN_PREMISES = 7      # stories shorter than this are skipped
BITS_PER_BYTE = 8


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


def compressed_bits(text):
    """Huffman-code `text` and return its size in bits.

    The codebook itself is not counted, only the encoded payload, so this is a
    lower bound on what an actual transmission would cost.
    """
    codec = HuffmanCodec.from_data(text)
    encoded = codec.encode(text)

    if codec.decode(encoded) != text:
        raise ValueError("Huffman round-trip did not reproduce the input")

    return len(encoded) * BITS_PER_BYTE


def main():
    stories = load_stories(DATA_PATH)
    print(f"{len(stories)} stories with at least {MIN_PREMISES} premises\n")

    bit_costs = []
    for index, premises in enumerate(stories):
        text = " ".join(premises)
        original = len(text) * BITS_PER_BYTE
        compressed = compressed_bits(text)

        print(
            f"Story {index:>2}: {original:>6} -> {compressed:>5} bits "
            f"(ratio {original / compressed:.2f})"
        )
        bit_costs.append([index, compressed])

    print("\nCompressed bits per story:")
    print(bit_costs)


if __name__ == "__main__":
    main()
