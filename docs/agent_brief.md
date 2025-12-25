# Agent brief (bounded working memory)

Правило: этот файл — «оперативная память» агента. Он **не должен разрастаться**
(лимит проверяется в `scripts/verify_notebook.py`). Обновляй его **заменой/сжатием**,
а не дописыванием бесконечных списков.

## Текущее направление (держать 1–2 строки)

Q39: depth≈$\\log n/\\log\\log n$ Frege needs XOR‑sim (§16.124–§16.126). Grid‑стратегия: внутри столбца есть протокол поддержания $k=O(\\log n)$ (пересечение=1 XOR + dyadic‑merge; §16.144–§16.145), а сложение соседних столбцов тоже «easy case» при фиксированных dyadic‑полосах $S_j$ (§16.146). Узел: держать блок‑паритеты глубины $d\\approx\\log n/\\log\\log n$ без накопления $O(\\log n)$ (иначе возвращается барьер §16.132).

## Что уже сделано (не повторять)

- ROABP‑канонизация multilinearization для CNF даёт $\mathrm{P}=\mathrm{NP}$ (барьер‑леммы 15.7.4* в `docs/15_proof_complexity.md`).
- PIT‑аксиомы ⇒ EF p‑симулирует IPS; базовые кодирования (CNF→3‑CNF + $g$, Tseitin‑Eval, счётчики) уже в 16.x.
- Tseitin: Frege poly (16.91); bounded‑depth lower bounds (Håstad’20, 16.92) + all‑graphs extension (GIRS’19, 16.97); missing Gauss‑step отмечен у Håstad–Risse §1.2 (16.122). Cor. 34: bounded‑depth Frege ⇒ tree‑like Res quasi‑poly (16.98); EF poly (16.88); PC: $\\mathbb F_2$ easy (16.89), char$\\ne2$ hard (16.90).

## Активные “неповторимые” задачи (выбрать одну за прогон)

- Q39 из `docs/open_questions.md` (обновлять там же, но без раздувания).

## Реестр экспериментов (макс 12 пунктов; перезаписывать старые)

- E01: Формализация PIT‑аксиом (GP14 Def. 1.7) и связь с SoundnessIPS → EF sim IPS (см. 15.7.3).
- E02: Барьер канонизации $\mathrm{ML}(P_\varphi)$ → ROABP (см. 15.7.4*).
- E03: LogLog‑трюк для bounded‑кванторов/таблиц истинности (toy‑шаги в 16.x).
- E04: Контрпример «эквивалентность CNF→3‑CNF» и корректный режим equisatisfiable + явный $g$ + линейный счёт (15.7.3c–d; 16.78).
- E05: Tseitin‑кодирование $\mathrm{Eval}(C,x)$ даёт 3‑CNF $O(s)$ (toy‑шаги 16.x).
- E06: Ошибки: adder‑tree + компаратор; Tseitin→3‑CNF $O(2^n n)$ (toy‑шаги 16.x).
- E07: Planar‑3‑SAT → Planar‑3‑SAT(≤4‑occ) (16.83–16.84).
- E08: Tseitin($G,\\chi$): паритетный сертификат невыполнимости + 3‑CNF для 3‑регулярных графов (16.85).
- E09: Tseitin на bounded‑degree экспандерах: $W\\ge e(G)-1$ и $S\\ge\\exp((e(G)-k-1)^2/|E|)$ (16.86).
- E10: Явное bounded‑occ Tseitin‑семейство на 3‑регулярных экспандерах (16.87).
- E11: Tseitin: Frege poly (16.91) + depth‑vs‑size (16.92–16.99) + EF через XOR (16.88); PC: над $\\mathbb F_2$ степень 3 для TseitinCNF (16.89); при $\\mathrm{char}\\ne 2$ TseitinCNF p‑эквивалентен биномиальной форме и наследует degree/size‑LB (16.90).

## Линзы (держать 5 последних; обновлять, не наращивать)

Последние: Эквивалентность → Сжатие/канонизация → Инвариант → Сжатие/канонизация → Эквивалентность
