# Agent brief (bounded working memory)

Правило: этот файл — «оперативная память» агента. Он **не должен разрастаться**
(лимит проверяется в `scripts/verify_all.sh`). Обновляй его **заменой/сжатием**,
а не дописыванием бесконечных списков.

## Anti-loop (обновлять, не раздувать)

- `LastStepID:` Q39.S43-2k-two-strip-chain-dyadic-carry-microsteps
- `Do-not-repeat (next 2 runs):` Q39.S42-2k-two-strip-chain-dyadic-prefix-stepwise, Q39.S43-2k-two-strip-chain-dyadic-carry-microsteps
- `Last InfoGain:` 1

## Текущее направление (держать 1–2 строки)

Q43: явный $A_0$ получен; следующий шаг — выписать явные $c_1,c_2$ в Thm. 4.1.
Q39: dyadic-carry микрошаги всё равно дают ранг 2; следующий шаг — требовать distinct support на микрошаге.

## Что уже сделано (не повторять)

- ROABP‑канонизация multilinearization для CNF даёт $\mathrm{P}=\mathrm{NP}$ (барьер‑леммы 15.7.4* в `docs/15_proof_complexity.md`).
- PIT‑аксиомы ⇒ EF p‑симулирует IPS; базовые кодирования (CNF→3‑CNF + $g$, Tseitin‑Eval, счётчики) уже в 16.x.
- Tseitin: Frege poly (16.91); bounded‑depth lower bounds (Håstad’20, 16.92) + all‑graphs extension (GIRS’19, 16.97); missing Gauss‑step отмечен у Håstad–Risse §1.2 (16.122). Cor. 34: bounded‑depth Frege ⇒ tree‑like Res quasi‑poly (16.98); EF poly (16.88); PC: $\\mathbb F_2$ easy (16.89), char$\\ne2$ hard (16.90).

## Активные “неповторимые” задачи (выбрать одну за прогон)

- Q39 из `docs/open_questions.md` (найти/убить poly‑size bounded‑depth симуляцию одного XOR‑шага).
- Q43 из `docs/open_questions.md` (пересчитать Chernoff‑шаг или зафиксировать $A_0$ как параметр).

## Реестр экспериментов (макс 12 пунктов; перезаписывать старые)

- E01: Формализация PIT‑аксиом (GP14 Def. 1.7) и связь с SoundnessIPS → EF sim IPS (см. 15.7.3).
- E02: Барьер канонизации $\mathrm{ML}(P_\varphi)$ → ROABP (см. 15.7.4*).
- E03: LogLog‑трюк для bounded‑кванторов/таблиц истинности (toy‑шаги в 16.x).
- E04: Контрпример «эквивалентность CNF→3‑CNF» и корректный режим equisatisfiable + явный $g$ + линейный счёт (15.7.3c–d; 16.78).
- E05: Tseitin‑кодирование $\mathrm{Eval}(C,x)$ даёт 3‑CNF $O(s)$ (toy‑шаги 16.x).
- E07: Planar‑3‑SAT → Planar‑3‑SAT(≤4‑occ) (16.83–16.84).
- E08: Tseitin($G,\\chi$): паритетный сертификат невыполнимости + 3‑CNF для 3‑регулярных графов (16.85).
- E09: Tseitin на bounded‑degree экспандерах: $W\\ge e(G)-1$ и $S\\ge\\exp((e(G)-k-1)^2/|E|)$ (16.86).
- E10: Явное bounded‑occ Tseitin‑семейство на 3‑регулярных экспандерах (16.87).
- E11: Tseitin‑сводка: Frege poly (16.91), depth‑vs‑size (16.92–16.99), EF через XOR (16.88), PC: $\\mathbb F_2$ easy (16.89), $\\mathrm{char}\\ne 2$ hard (16.90).

## Линзы (держать 5 последних; обновлять, не наращивать)

Последние:Трейд‑офф→Эквивалентность→Инвариант→Коммуникация/ранг→Инвариант
