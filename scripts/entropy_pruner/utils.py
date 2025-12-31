from __future__ import annotations

import math
import random
import zlib
from typing import Iterable, Sequence


def seeded_rng(seed: int | None) -> random.Random:
    return random.Random(seed)


def entropy_from_counts(counts: Iterable[int], *, base: float = 2.0) -> float:
    total = 0.0
    for count in counts:
        if count > 0:
            total += count
    if total <= 0:
        return 0.0
    ent = 0.0
    for count in counts:
        if count <= 0:
            continue
        p = count / total
        ent -= p * math.log(p, base)
    return ent


def compress_ratio(text: str) -> float:
    if not text:
        return 1.0
    raw = text.encode("utf-8")
    compressed = zlib.compress(raw)
    return len(compressed) / max(1, len(raw))


def mean_std(values: Sequence[float]) -> tuple[float, float]:
    if not values:
        return 0.0, 1.0
    mean = sum(values) / len(values)
    var = sum((v - mean) ** 2 for v in values) / len(values)
    std = math.sqrt(var)
    if std == 0.0:
        std = 1.0
    return mean, std


def sigmoid(x: float) -> float:
    if x >= 0:
        z = math.exp(-x)
        return 1.0 / (1.0 + z)
    z = math.exp(x)
    return z / (1.0 + z)
