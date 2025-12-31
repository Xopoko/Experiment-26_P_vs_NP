from __future__ import annotations

import argparse
import csv
from pathlib import Path

from .model import LogisticModel, accuracy_score, roc_auc_score, save_model, train_logreg
from .utils import seeded_rng


def load_dataset(path: Path) -> tuple[list[list[float]], list[int], list[str]]:
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        headers = list(reader.fieldnames or [])
        if "label_unsat" in headers:
            label_col = "label_unsat"
            feature_names = [h for h in headers if h != label_col]
            invert = False
        elif "label_sat" in headers:
            label_col = "label_sat"
            feature_names = [h for h in headers if h != label_col]
            invert = True
        else:
            raise ValueError("missing label column (label_unsat or label_sat)")

        X: list[list[float]] = []
        y: list[int] = []
        for row in reader:
            features = [float(row[name]) for name in feature_names]
            label_raw = int(float(row[label_col]))
            label = 1 - label_raw if invert else label_raw
            X.append(features)
            y.append(label)
    return X, y, feature_names


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a toy stopper (logistic regression).")
    parser.add_argument("--data", default="agent/logs/entropy_dataset.csv")
    parser.add_argument("--model", default="agent/logs/entropy_model.json")
    parser.add_argument("--epochs", type=int, default=50)
    parser.add_argument("--lr", type=float, default=0.1)
    parser.add_argument("--l2", type=float, default=0.0)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--test_split", type=float, default=0.2)
    args = parser.parse_args()

    data_path = Path(args.data)
    model_path = Path(args.model)

    X, y, feature_names = load_dataset(data_path)
    if not X:
        print("Empty dataset.")
        return 1

    rng = seeded_rng(args.seed)
    indices = list(range(len(X)))
    rng.shuffle(indices)

    split = int(len(indices) * (1.0 - args.test_split))
    train_idx = indices[:split]
    test_idx = indices[split:]

    X_train = [X[i] for i in train_idx]
    y_train = [y[i] for i in train_idx]
    X_test = [X[i] for i in test_idx]
    y_test = [y[i] for i in test_idx]

    model = train_logreg(
        X_train,
        y_train,
        feature_names,
        epochs=args.epochs,
        lr=args.lr,
        l2=args.l2,
    )

    if X_test:
        scores = model.predict_proba_batch(
            [dict(zip(feature_names, row)) for row in X_test]
        )
        preds = [1 if s >= 0.5 else 0 for s in scores]
        auc = roc_auc_score(y_test, scores)
        acc = accuracy_score(y_test, preds)
    else:
        auc = float("nan")
        acc = 0.0

    meta = {
        "data": str(data_path),
        "epochs": args.epochs,
        "lr": args.lr,
        "l2": args.l2,
        "seed": args.seed,
        "test_split": args.test_split,
        "train_rows": len(X_train),
        "test_rows": len(X_test),
    }
    save_model(model_path, model, meta=meta)

    print("Training summary")
    print(f"  rows: {len(X)} (train {len(X_train)}, test {len(X_test)})")
    print(f"  features: {len(feature_names)}")
    if auc == auc:
        print(f"  test_auc: {auc:.3f}")
    else:
        print("  test_auc: N/A")
    print(f"  test_accuracy: {acc:.3f}")
    print(f"  model: {model_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
