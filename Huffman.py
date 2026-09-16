import pandas as pd
from dahuffman import HuffmanCodec

def read_stories(dataframe):
    ids, story_arr = [], []
    for ix in range(len(dataframe)):
        if dataframe['story_id'][ix] in ids:
            continue
        else:
            story_arr.append(dataframe['premises'][ix])
        ids.append(dataframe['story_id'][ix])

    return story_arr, ids

if __name__ == '__main__':

    file_path = 'folio-train.jsonl'
    df_f = pd.read_json(file_path, lines=True)

    # As FOLIO dataset is a logical reasoning dataset, there exists multiple examples with the same story (i.e.,
    # same premises) but with different conclusions. Check story_id & skip if a particular story is already included,
    # append all others to a separate list.
    stories, story_ids = read_stories(dataframe=df_f)

    stories_new = []

    for element in stories:
        if len(element) > 6:
            stories_new.append(element)

    stories = stories_new

    ids = 0
    bit_array = []
    for story in stories:

        text = " ".join(story)

        codec = HuffmanCodec.from_data(text)

        # Step 1: Encode the text using Huffman encoding
        encoded_text = codec.encode(text)
        print(f"Encoded Text: {encoded_text}")

        # Step 2: Calculate the original bit size
        # Assume each character in the original text is represented using 8 bits (ASCII encoding)
        original_bit_size = len(text) * 8
        print(f"Original Bit Size: {original_bit_size} bits")

        # Step 3: Calculate the compressed bit size
        # The compressed bit size is simply the length of the encoded text (binary string)
        compressed_bit_size = len(encoded_text) * 8
        print(f"Compressed Bit Size: {compressed_bit_size} bits")

        # Step 4: Calculate the compression ratio
        compression_ratio = original_bit_size / compressed_bit_size
        print(f"Compression Ratio: {compression_ratio:.2f}")

        # Step 5: Decode the text (to verify correctness)
        decoded_text = codec.decode(encoded_text)
        print(f"Decoded Text: {decoded_text}")

        bit_array.append([ids, compressed_bit_size])
        ids = ids + 1

    print(bit_array)
