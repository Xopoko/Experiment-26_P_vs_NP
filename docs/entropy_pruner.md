# Entropy pruner toy

This is a self-contained toy sandbox for entropy-style pruning on toy SAT.
It generates labeled nodes from a DPLL search tree, trains a simple stopper,
and compares baseline vs pruned search inside one run.

Commands:
1) python3 -m scripts.entropy_pruner.generate_dataset --out agent/logs/entropy_dataset.csv --instances 30 --vars 12 --clauses 50
2) python3 -m scripts.entropy_pruner.train_stopper --data agent/logs/entropy_dataset.csv --model agent/logs/entropy_model.json
3) python3 -m scripts.entropy_pruner.run_with_stopper --model agent/logs/entropy_model.json --instances 30 --vars 12 --clauses 50 --threshold 0.90

Metrics to watch: test_auc/test_accuracy, node reduction, solved rate.
Note: does not affect formal/Lean layer.
