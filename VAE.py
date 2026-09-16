import sys

from transformers import GPT2Tokenizer, GPT2LMHeadModel
import pandas as pd

# Load pre-trained GPT-2 small model and tokenizer
model_name = "gpt2"
tokenizer = GPT2Tokenizer.from_pretrained(model_name)
model = GPT2LMHeadModel.from_pretrained(model_name)


# Function to generate text based on the prompt (controlled decoding)
def generate_text(prompt, max_length=None):
    # Tokenize the input prompt
    input_ids = tokenizer.encode(prompt, return_tensors="pt")
    print(input_ids)
    sys.exit()

    # Ensure the max length is just slightly more than the input to avoid too much extra text
    if max_length is None:
        max_length = len(input_ids[0]) + 5  # Add a small buffer for max length

    # Generate text using GPT-2 with greedy decoding (no randomness, aiming for exact match)
    generated_ids = model.generate(
        input_ids,
        max_length=max_length,
        num_return_sequences=1,
        pad_token_id=tokenizer.eos_token_id,
        temperature=0.1,  # Low temperature to make it more deterministic
        top_p=0.9,  # Conservative nucleus sampling
        do_sample=False  # No sampling, greedy approach
    )

    # Decode the generated text
    decoded_text = tokenizer.decode(generated_ids[0], skip_special_tokens=True)

    # Strip the extra generated text (optional, but keeps things tidy)
    decoded_text = decoded_text[:len(prompt)]

    return decoded_text, input_ids

def read_stories(dataframe):
    ids, story_arr = [], []
    for ix in range(len(dataframe)):
        if dataframe['story_id'][ix] in ids:
            continue
        else:
            story_arr.append(dataframe['premises'][ix])
        ids.append(dataframe['story_id'][ix])

    return story_arr, ids

def calculate_compression_ratio(input_text, input_ids):
    # Calculate original size in bits (assuming 1 byte = 8 bits for ASCII characters)
    original_size_bits = len(input_text) * 8

    # Calculate the size of the encoded tokens in bits (each token is 32 bits)
    encoded_size_bits = len(input_ids[0]) * 32

    # Compute the compression ratio
    compression_ratio = original_size_bits / encoded_size_bits

    return compression_ratio, encoded_size_bits, original_size_bits

if __name__ == '__main__':
    file_path = 'folio-train.jsonl'
    df_f = pd.read_json(file_path, lines=True)

    story_arr, ids = read_stories(df_f)

    stories_new = []

    for element in story_arr:
        if len(element) > 6:
            stories_new.append(element)

    story_arr = stories_new

    sentences = []
    for story in story_arr:
        combined_string = " ".join(story)
        sentences.append(combined_string)

    ids = 0
    bit_arr = []
    orig = []
    # Process each sentence and compute the compression ratio
    for inputt in sentences:
        print("Original Text: ", inputt)

        # Generate reconstructed text and get the tokenized input
        reconstructed_text, input_ids = generate_text(inputt)

        # Calculate compression ratio
        compression_ratio, encoded, origin = calculate_compression_ratio(inputt, input_ids)

        # Display results
        print("Reconstructed Text: ", reconstructed_text)
        print("Compression Ratio: ", compression_ratio)
        print("--------------------------------------------")

        bit_arr.append([ids, encoded])
        orig.append([ids, origin])
        ids = ids + 1

    print(bit_arr)
    print(orig)