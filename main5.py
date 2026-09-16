import sys

import pandas as pd
import torch
from torch.utils.data import DataLoader, TensorDataset
from transformers import AutoTokenizer, BartForConditionalGeneration, BartTokenizer
import numpy as np

# Read the JSONL file into a DataFrame
file_path = 'folio-train.jsonl'
df = pd.read_json(file_path, lines=True)

# Extract the desired columns into different variables
conclusions = df['conclusion'].tolist()
premises = df['premises'].tolist()
premises_FOL = df['premises-FOL'].tolist()
labels = df['label'].tolist()

# Check if a GPU is available and set the device accordingly
device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
print(f"Using device: {device}")

class BartAutoencoder(torch.nn.Module):
    def __init__(self, model_name="facebook/bart-large", bottleneck_size=32):
        super(BartAutoencoder, self).__init__()
        self.encoder = BartForConditionalGeneration.from_pretrained(model_name).to(device)
        self.bottleneck1 = torch.nn.Linear(self.encoder.config.d_model, bottleneck_size).to(device)
        self.bottleneck2 = torch.nn.Linear(bottleneck_size, self.encoder.config.d_model).to(device)
        self.decoder = BartForConditionalGeneration.from_pretrained(model_name).to(device)

    def forward(self, input_ids, attention_mask=None, decoder_input_ids=None):
        encoder_outputs = self.encoder.model.encoder(input_ids=input_ids.to(device), attention_mask=attention_mask.to(device))
        compressed = self.bottleneck1(encoder_outputs.last_hidden_state)
        decompressed = self.bottleneck2(compressed)
        decoder_outputs = self.decoder(inputs_embeds=decompressed, decoder_input_ids=decoder_input_ids.to(device))
        return decoder_outputs.logits


# Example usage
model_name = "facebook/bart-large"
autoencoder = BartAutoencoder(model_name=model_name, bottleneck_size=32)

# Concatenate the FOL sentences into a single string for each example
premises_FOL_concatenated = [', '.join(sentences) for sentences in premises_FOL]


# Tokenize input sentences
tokenizer = BartTokenizer.from_pretrained(model_name)
inputs = tokenizer(premises_FOL_concatenated, return_tensors="pt", padding="max_length", truncation=True, max_length=613)
decoder_input_ids = inputs.input_ids.clone()

# Move tensors to the same device as the model
inputs = inputs.to(device)
decoder_input_ids = decoder_input_ids.to(device)

# Forward pass
outputs = autoencoder(inputs.input_ids[:1], attention_mask=inputs.attention_mask[:1], decoder_input_ids=decoder_input_ids[:1])

# Create a TensorDataset and DataLoader
dataset = TensorDataset(inputs.input_ids, inputs.attention_mask, decoder_input_ids)
#dataloader = DataLoader(dataset, batch_size=2, shuffle=True)
dataloader = DataLoader(dataset, batch_size=3, shuffle=True)
#dataloader = DataLoader(dataset, batch_size=4, shuffle=True)
#dataloader = DataLoader(dataset, batch_size=8, shuffle=True)
#dataloader = DataLoader(dataset, batch_size=16, shuffle=True) # OUT OF MEMORY

# Define the model, loss function, and optimizer
loss_fn = torch.nn.CrossEntropyLoss()

#optimizer = torch.optim.Adam(autoencoder.parameters(), lr=5e-2)
#optimizer = torch.optim.Adam(autoencoder.parameters(), lr=1e-3)
#optimizer = torch.optim.Adam(autoencoder.parameters(), lr=5e-3)
#ptimizer = torch.optim.Adam(autoencoder.parameters(), lr=5e-4)
optimizer = torch.optim.Adam(autoencoder.parameters(), lr=5e-5)

# Training loop
#num_epochs = 3
#num_epochs = 6
num_epochs = 10
autoencoder.train()
sentences = []

for epoch in range(num_epochs):
    sentences = []
    count = 0
    for batch in dataloader:
        input_ids, attention_mask, labels = [tensor.to(device) for tensor in batch]

        # Forward pass
        outputs = autoencoder(input_ids, attention_mask=attention_mask, decoder_input_ids=labels)
        logits = outputs[:, :-1].contiguous().view(-1, outputs.size(-1))
        labels = labels[:, 1:].contiguous().view(-1)

        # Compute loss and backpropagate
        loss = loss_fn(logits, labels)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()

        #print(outputs.shape)
        #print(logits.shape)
        #print(labels.shape)
        predictions = torch.argmax(outputs, dim=-1)  # Get the predicted token IDs
        #print(predictions)
        #print(predictions.shape)
        decoded_predictions = [tokenizer.decode(pred, skip_special_tokens=True) for pred in predictions]
        sentences.append(decoded_predictions)

        print("Epoch: ", epoch, " Count: ", count)
        count = count + 1

    print(f"Epoch {epoch + 1}/{num_epochs}, Loss: {loss.item()}")
    print(sentences[0])