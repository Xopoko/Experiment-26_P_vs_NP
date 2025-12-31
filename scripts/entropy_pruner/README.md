# Entropy pruner (toy)

Self-contained toy SAT sandbox for checking entropy-style features and pruning.
It generates labeled search-tree nodes, trains a simple stopper, and compares
baseline vs pruned search in one run.

Quick run (outputs go to agent/logs):

1) Dataset
   python3 -m scripts.entropy_pruner.generate_dataset --out agent/logs/entropy_dataset.csv --instances 30 --vars 12 --clauses 50

2) Train
   python3 -m scripts.entropy_pruner.train_stopper --data agent/logs/entropy_dataset.csv --model agent/logs/entropy_model.json

3) Compare baseline vs pruning
   python3 -m scripts.entropy_pruner.run_with_stopper --model agent/logs/entropy_model.json --instances 30 --vars 12 --clauses 50 --threshold 0.90
