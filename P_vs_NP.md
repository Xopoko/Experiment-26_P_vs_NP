# P vs NP — главный ноутбук

**Статус (2025):** проблема $\mathrm{P}$ vs $\mathrm{NP}$ остаётся открытой.
Этот ноутбук — проверяемый журнал: постановка, леммы, барьеры, точки для нерелятивизирующих/ненатуральных идей.

**Цель:** доказать $\mathrm{P}\neq\mathrm{NP}$ или $\mathrm{P}=\mathrm{NP}$.
Пока доказательства нет; новые идеи — леммы с явными зависимостями
и проверкой на контрпримеры.
## Навигация
- [0. Договор о «формальной проверяемости»](docs/00_formal_verifiability.md)
- [1. Формальная постановка](docs/01_formal_statement.md)
- [2. Эквивалентная «сертификатная» формулировка NP](docs/02_np_certificates.md)
- [3. Базовые включения](docs/03_basic_inclusions.md)
- [4. Редукции и NP‑полнота](docs/04_reductions_np_complete.md)
- [5. SAT ≤p 3SAT](docs/05_sat_to_3sat.md)
- [6. 3SAT ≤p CLIQUE](docs/06_3sat_to_clique.md)
- [6.6. INDEPENDENT SET и VERTEX COVER](docs/06_6_is_vc.md)
- [7. Три барьера](docs/07_barriers.md)
- [8. Линии атаки](docs/08_attack_lines.md)
- [Roadmap](docs/roadmap.md)
- [Agent brief (не разрастаться)](docs/agent_brief.md)
- [Открытые вопросы (очередь)](docs/open_questions.md)
- [9. Схемная сложность](docs/09_circuit_complexity.md)
- [10. PARITY (глубина 2)](docs/10_parity_depth2.md)
- [11. Switching lemma → PARITY ∉ AC⁰](docs/11_switching_lemma_ac0.md)
- [12. Иерархия по времени](docs/12_time_hierarchy.md)
- [13. Теорема Сэвича](docs/13_savitch.md)
- [14. Полиномиальная иерархия](docs/14_ph.md)
- [15. Proof complexity: резолюция и PHP](docs/15_proof_complexity.md)
- [16. IP = PSPACE и PCP](docs/16_ip_pcp.md)
- [Исследовательские шаги (16.x, индекс)](docs/research/index.md)
- [17. Источники и опорные ссылки](docs/sources.md)
- [Формальный слой (Lean 4)](formal/README.md)

## Проверка
- Запуск проверок (markdown + формализация): `scripts/verify_all.sh`
