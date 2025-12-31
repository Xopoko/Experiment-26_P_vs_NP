from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

from .utils import mean_std, sigmoid


def roc_auc_score(y_true: Sequence[int], y_score: Sequence[float]) -> float:
    if len(y_true) != len(y_score) or not y_true:
        return float("nan")
    n_pos = sum(1 for y in y_true if y == 1)
    n_neg = len(y_true) - n_pos
    if n_pos == 0 or n_neg == 0:
        return float("nan")

    pairs = list(enumerate(y_score))
    pairs.sort(key=lambda item: item[1])

    ranks = [0.0 for _ in y_score]
    i = 0
    rank = 1
    while i < len(pairs):
        j = i + 1
        while j < len(pairs) and pairs[j][1] == pairs[i][1]:
            j += 1
        avg_rank = (rank + (rank + (j - i) - 1)) / 2.0
        for k in range(i, j):
            idx = pairs[k][0]
            ranks[idx] = avg_rank
        rank += j - i
        i = j

    sum_pos_ranks = sum(ranks[i] for i, y in enumerate(y_true) if y == 1)
    auc = (sum_pos_ranks - n_pos * (n_pos + 1) / 2.0) / (n_pos * n_neg)
    return auc


def accuracy_score(y_true: Sequence[int], y_pred: Sequence[int]) -> float:
    if not y_true:
        return 0.0
    correct = sum(1 for yt, yp in zip(y_true, y_pred) if yt == yp)
    return correct / len(y_true)


@dataclass
class LogisticModel:
    feature_names: list[str]
    mean: list[float]
    std: list[float]
    weights: list[float]
    bias: float

    def predict_proba(self, features: dict[str, float]) -> float:
        x = [float(features[name]) for name in self.feature_names]
        z = self.bias
        for xi, mu, sigma, w in zip(x, self.mean, self.std, self.weights):
            z += w * ((xi - mu) / sigma)
        return sigmoid(z)

    def predict_proba_batch(self, rows: Iterable[dict[str, float]]) -> list[float]:
        return [self.predict_proba(row) for row in rows]

    def to_dict(self) -> dict[str, object]:
        return {
            "feature_names": self.feature_names,
            "mean": self.mean,
            "std": self.std,
            "weights": self.weights,
            "bias": self.bias,
        }

    @staticmethod
    def from_dict(data: dict[str, object]) -> "LogisticModel":
        return LogisticModel(
            feature_names=list(data.get("feature_names", [])),
            mean=[float(v) for v in data.get("mean", [])],
            std=[float(v) for v in data.get("std", [])],
            weights=[float(v) for v in data.get("weights", [])],
            bias=float(data.get("bias", 0.0)),
        )


def train_logreg(
    X: Sequence[Sequence[float]],
    y: Sequence[int],
    feature_names: list[str],
    *,
    epochs: int = 50,
    lr: float = 0.1,
    l2: float = 0.0,
) -> LogisticModel:
    if not X:
        raise ValueError("empty dataset")
    n_features = len(X[0])
    means: list[float] = []
    stds: list[float] = []
    for j in range(n_features):
        col = [row[j] for row in X]
        mu, sigma = mean_std(col)
        means.append(mu)
        stds.append(sigma)

    weights = [0.0 for _ in range(n_features)]
    bias = 0.0

    for _ in range(epochs):
        grad_w = [0.0 for _ in range(n_features)]
        grad_b = 0.0
        for row, yi in zip(X, y):
            z = bias
            for j, (xj, mu, sigma, wj) in enumerate(zip(row, means, stds, weights)):
                z += wj * ((xj - mu) / sigma)
            p = sigmoid(z)
            err = p - yi
            for j, (xj, mu, sigma) in enumerate(zip(row, means, stds)):
                grad_w[j] += err * ((xj - mu) / sigma)
            grad_b += err
        n = len(X)
        for j in range(n_features):
            grad_w[j] = grad_w[j] / n + l2 * weights[j]
            weights[j] -= lr * grad_w[j]
        bias -= lr * (grad_b / n)

    return LogisticModel(
        feature_names=feature_names,
        mean=means,
        std=stds,
        weights=weights,
        bias=bias,
    )


def save_model(path: Path, model: LogisticModel, *, meta: dict[str, object] | None = None) -> None:
    payload = {"model": model.to_dict()}
    if meta:
        payload["meta"] = meta
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def load_model(path: Path) -> LogisticModel:
    raw = json.loads(path.read_text(encoding="utf-8"))
    model_data = raw.get("model", raw)
    if not isinstance(model_data, dict):
        raise ValueError("invalid model JSON")
    return LogisticModel.from_dict(model_data)
