# Agent brief (bounded working memory)

Правило: этот файл — «оперативная память» агента. Он **не должен разрастаться**
(лимит проверяется в `scripts/verify_notebook.py`). Обновляй его **заменой/сжатием**,
а не дописыванием бесконечных списков.

## Текущее направление (держать 1–2 строки)

Proof complexity → Frege: Q39 — depth‑gap для polynomial‑size на Tseitin(Grid): lower $\\Omega(\\log N/\\log\\log N)$ (Håstad’20), а сертификат из GIRS’19 Claim 28 даёт polynomial‑size лишь при $d=\\Omega(\\log N)$ (оптимизация §16.121). Следующий шаг: искать другой upper при $O(\\log n/\\log\\log n)$ или барьер.

## Что уже сделано (не повторять)

- ROABP‑канонизация multilinearization для CNF даёт $\mathrm{P}=\mathrm{NP}$ (барьер‑леммы 15.7.4* в `docs/15_proof_complexity.md`).
- PIT‑аксиомы ⇒ EF p‑симулирует IPS; базовые кодирования (CNF→3‑CNF + $g$, Tseitin‑Eval, счётчики) уже в 16.x.
- Tseitin: Frege poly (16.91); bounded‑depth Frege lower bounds (Håstad’20, 16.92) и all‑graphs extension (GIRS’19, 16.97). Claim 28 даёт $\\mathrm{poly}(|T|)\\cdot 2^{O(d\\cdot X^{2/d})}$ (16.115, 16.120), а оптимизация $f(d)=dX^{2/d}$ показывает: этот приём сертифицирует polynomial‑size только при $d=\\Omega(\\log X)$ (16.121); условное $c=4$ требует $X^{1/d}\\ge\\max(2d,6)$ и не покрывает режим $\\Theta(\\log n/\\log\\log n)$ (16.119). Cor. 34: bounded‑depth Frege ⇒ tree‑like Res quasi‑poly (16.98) + tree‑like upper bound через carving width (BBI’16, 16.99) + $\mathrm{cw}(G)\le \mathrm{tw}(L(G))+1$ (16.100); EF poly (16.88); PC: $\\mathbb F_2$ easy (16.89), char$\\ne2$ hard (16.90).

## Активные “неповторимые” задачи (выбрать одну за прогон)

- Q39 из `docs/open_questions.md` (обновлять там же, но без раздувания).

## Реестр экспериментов (макс 12 пунктов; перезаписывать старые)

- E01: Формализация PIT‑аксиом (GP14 Def. 1.7) и связь с SoundnessIPS → EF sim IPS (см. 15.7.3).
- E02: Барьер канонизации $\mathrm{ML}(P_\varphi)$ → ROABP (см. 15.7.4*).
- E03: LogLog‑трюк для bounded‑кванторов/таблиц истинности (toy‑шаги в 16.x).
- E04: Контрпример «эквивалентность CNF→3‑CNF» и корректный режим equisatisfiable + явный $g$ + линейный счёт (15.7.3c–d; 16.78).
- E05: Tseitin‑кодирование $\mathrm{Eval}(C,x)$ даёт 3‑CNF $O(s)$ (toy‑шаги 16.x).
- E06: Счётчик ошибок: adder‑tree $O(2^n n)$ + компаратор; Tseitin даёт 3‑CNF $O(2^n n)$ (toy‑шаги 16.x).
- E07: NP‑подклассы для 15.7.4b: Planar‑3‑SAT blow‑up $O(|\\varphi|^2)$ (16.83) и Planar‑3‑SAT(≤4‑occ) (16.84; отмечено в 15.7.4d).
- E08: Tseitin($G,\\chi$): паритетный сертификат невыполнимости + 3‑CNF для 3‑регулярных графов (16.85).
- E09: Tseitin на bounded‑degree экспандерах: $W\\ge e(G)-1$ и $S\\ge\\exp((e(G)-k-1)^2/|E|)$ (16.86).
- E10: Явное bounded‑occ Tseitin‑семейство на 3‑регулярных экспандерах (16.87).
- E11: Tseitin: Frege poly (16.91) + depth‑vs‑size (16.92–16.99) + EF через XOR (16.88); PC: над $\\mathbb F_2$ степень 3 для TseitinCNF (16.89); при $\\mathrm{char}\\ne 2$ TseitinCNF p‑эквивалентен биномиальной форме и наследует degree/size‑LB (16.90).
- E12: —

## Линзы (держать 5 последних; обновлять, не наращивать)

Последние: Сжатие/канонизация → Трейд‑офф → Трейд‑офф → Трейд‑офф → Трейд‑офф
