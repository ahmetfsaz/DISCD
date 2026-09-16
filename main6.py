import pandas as pd
import torch
from torch.utils.data import DataLoader, TensorDataset
from transformers import BartForConditionalGeneration, BartTokenizer

# Read the JSONL file into a DataFrame
file_path = 'folio-train.jsonl'
df = pd.read_json(file_path, lines=True)

# Extract the desired columns into different variables
premises_FOL = df['premises-FOL'].tolist()

# Check if a GPU is available and set the device accordingly
device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
print(f"Using device: {device}")

class BartAutoencoder(torch.nn.Module):
    def __init__(self, model_name="facebook/bart-large", bottleneck_size=32):
        super(BartAutoencoder, self).__init__()
        self.encoder = BartForConditionalGeneration.from_pretrained(model_name).to(device)
        self.bottleneck = torch.nn.Linear(self.encoder.config.d_model, bottleneck_size).to(device)
        self.bottleneck = torch.nn.Linear(self.encoder.config.d_model, 1024).to(device)
        self.decoder = BartForConditionalGeneration.from_pretrained(model_name).to(device)

    def forward(self, input_ids, attention_mask=None, decoder_input_ids=None):
        encoder_outputs = self.encoder.model.encoder(input_ids=input_ids.to(device), attention_mask=attention_mask.to(device))
        compressed = self.bottleneck(encoder_outputs.last_hidden_state)
        decoder_outputs = self.decoder(inputs_embeds=compressed, decoder_input_ids=decoder_input_ids.to(device))
        return decoder_outputs.logits

# Example usage
model_name = "facebook/bart-large"
autoencoder = BartAutoencoder(model_name=model_name, bottleneck_size=32)

# Concatenate the FOL sentences into a single string for each example
premises_FOL_concatenated = [', '.join(sentences) for sentences in premises_FOL]

# Tokenize input sentences
tokenizer = BartTokenizer.from_pretrained(model_name)
inputs = tokenizer(premises_FOL_concatenated, return_tensors="pt", padding=True, truncation=True, max_length=512)
decoder_input_ids = inputs.input_ids.clone() #tokenizer(["<pad>"] * len(premises_FOL_concatenated), return_tensors="pt", padding=True, truncation=True, max_length=512).input_ids

# Move tensors to the same device as the model
inputs = inputs.to(device)
decoder_input_ids = decoder_input_ids.to(device)

# Create a TensorDataset and DataLoader
dataset = TensorDataset(inputs.input_ids, inputs.attention_mask, decoder_input_ids)  # Using input_ids as both input and target
dataloader = DataLoader(dataset, batch_size=4, shuffle=True)

# Define the model, loss function, and optimizer
loss_fn = torch.nn.CrossEntropyLoss(ignore_index=tokenizer.pad_token_id)
optimizer = torch.optim.Adam(autoencoder.parameters(), lr=5e-5)

# Training loop
num_epochs = 3
autoencoder.train()
for epoch in range(num_epochs):
    for batch in dataloader:
        input_ids, attention_mask, labels = [tensor.to(device) for tensor in batch]

        # Forward pass
        outputs = autoencoder(input_ids, attention_mask=attention_mask, decoder_input_ids=labels)#input_ids)
        logits = outputs[:, :-1, :].contiguous()  # Shape: (batch_size, seq_len - 1, vocab_size)
        labels = labels[:, 1:].contiguous()  # Shape: (batch_size, seq_len - 1)

        # Reshape logits and labels to match
        logits = logits.view(-1, logits.size(-1))  # Shape: (batch_size * (seq_len - 1), vocab_size)
        labels = labels.view(-1)  # Shape: (batch_size * (seq_len - 1))

        # Compute loss and backpropagate
        loss = loss_fn(logits, labels)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
        print('heyo')

    print(f"Epoch {epoch + 1}/{num_epochs}, Loss: {loss.item()}")
