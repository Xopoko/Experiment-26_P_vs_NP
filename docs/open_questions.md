# Открытые вопросы (рабочая очередь)

Правило: **каждый прогон агента выбирает ровно 1 пункт ниже** и делает измеримый прогресс:
доказательство/контрпример/уточнение формулировки/точная ссылка + барьер‑чек. Затем обновляет пункт.

## Активные

- [ ] **Q20 (согласовать использование $w(G)$ в Cor. 34 / §16.98):**
  теперь, когда первоисточник для $w(G)=\\max\\{\\Delta(G),\\mathrm{tw}(L(G))\\}-1$ зафиксирован (16.101),
  привести в §16.98 явное определение $w(G)=W(T(G,\\varphi)\\vdash\\bot)-1$ и аккуратно вывести форму
  $n^{O(w(G))}=2^{O(\\mathrm{tw}(G)\\,\\Delta(G)\\log n)}$ через оценки на $\\mathrm{tw}(L(G))$ (Harvey–Wood 2018, как в GIRS’19 Cor. 33).

## Завершённые (архив)

- [x] **Q19 (точная ссылка на $w(G)=\max\{\\Delta(G),\\mathrm{tw}(L(G))\\}-1$ для Tseitin‑width):**
  закрыто: Galesi–Talebanfard–Torán (2018, ECCC TR18‑170) дают Cor. 8:
  $W(T(G,\\varphi)\\vdash\\bot)=\\max\\{\\Delta(G),\\mathrm{ec}(G)-1\\}$ и Cor. 16:
  $\\mathrm{ec}(G)=\\mathrm{tw}(L(G))+1$, откуда $W=\\max\\{\\Delta(G),\\mathrm{tw}(L(G))\\}$ и $w(G)=W-1$.
  См. `docs/research/16_research_steps.md` §16.101 и `../resources/downloads/galesi_talebanfard_toran_2018_cops_robber_tseitin.pdf`.
- [x] **Q18 (связать carving width $W$ с $w(G)$ в Cor. 34):** закрыто: доказано $\mathrm{cw}(G)\le \mathrm{tw}(L(G))+1$;
  вместе с формулой для Tseitin‑width $w(G)=\max\{\\Delta(G),\\mathrm{tw}(L(G))\\}-1$ (16.101) получаем
  $\mathrm{cw}(G)\le w(G)+2$ и можно переписывать $n^{O(\\mathrm{cw}(G))}$ как $n^{O(w(G))}$; см. `docs/research/16_research_steps.md` §16.100.
- [x] **Q17 (Cor. 34: зависимости и «где именно берётся» tree‑like Res ≤ n^{O(w)}):** закрыто:
  точная ссылка для tree‑like upper bound — Beame–Beck–Impagliazzo (2016), Lemma 61 (через carving width),
  см. `docs/research/16_research_steps.md` §16.99 и
  `../resources/downloads/beame_beck_impagliazzo_2016_time_space_tradeoffs_resolution.pdf`.
- [x] **Q16 (Tseitin: bounded‑depth Frege ↔ tree‑like Resolution):** закрыто: точная формулировка Cor. 34:
  bounded‑depth Frege‑доказательство размера $S$ ⇒ tree‑like Resolution размера $\le 2^{\mathrm{poly}(\log S)}$
  (Galesi–Itsykson–Riazanov–Sofronova 2019, Cor. 34), см. `docs/research/16_research_steps.md` §16.98 и
  `../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`.
- [x] **Q15 (сузить разрыв depth‑vs‑size для Tseitin):** закрыто: Galesi–Itsykson–Riazanov–Sofronova (2019, ECCC TR19‑069)
  дают tight depth‑vs‑size через treewidth: для $d\le \Theta(\log n/\log\log n)$ размер depth‑$d$ Frege‑рефутаций
  $\ge 2^{\mathrm{tw}(G)^{\Omega(1/d)}}$ (Thm. 18) и $\le 2^{\mathrm{tw}(G)^{O(1/d)}}\cdot\mathrm{poly}(|\mathrm{Tseitin}(G,f)|)$
  (Thm. 19), см. `docs/research/16_research_steps.md` §16.97 и
  `../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`.
  В частности, для $\mathrm{tw}(G)=\Omega(n)$ (grid/экспандеры) polynomial‑size ⇔ depth $\Theta(\log n/\log\log n)$, что
  усиливает PRST’16 (16.96) и согласуется с Håstad’20 (16.92).
- [x] **Q14 (Frege‑depth для Tseitin):** закрыто: poly‑size Frege‑рефутация (Urquhart 1987; §16.91),
  bounded‑depth lower bound на grid (Håstad 2020; §16.92), upper bound depth $O(\log n)$ для bounded‑degree
  (Håstad 2020 remark + Buss 1997/Spira‑перевод; §16.93 и §16.95), и ссылка на формульную балансировку (Bonet–Buss 2002; §16.94).
- [x] **Q13 (Frege/EF симулирует XOR/Gauss):** в `docs/research/16_research_steps.md` §16.88 добавлена точная ссылка,
  что EF «легко симулирует Gaussian elimination» (Bonet–Buss–Pitassi 2002, `../resources/downloads/bonet_buss_pitassi_2002_hard_examples_frege.pdf`, p. 7),
  что закрывает фольклорность EF‑каркаса XOR‑суммирования.
- [x] **Q12 (TseitinCNF vs PC при $\mathrm{char}(F)\ne 2$):** в `docs/research/16_research_steps.md` §16.90
  показано: TseitinCNF (3‑CNF) и биномиальная Tseitin (Fourier/±1‑база) p‑эквивалентны по степени в PC при $\mathrm{char}(F)\ne 2$,
  поэтому degree/size‑LB (Razborov 2023, Thm. 6.8; Beame–Sabharwal 2000, Thm. 2.18) переносятся на TseitinCNF.
- [x] **Q11 (TseitinCNF vs PC над $\mathbb F_2$):** в `docs/research/16_research_steps.md` §16.89
  дан явный PC‑вывод линейного уравнения вершины из 4 клауз и итоговая рефутация степени 3 и размера $O(|V|)$.
- [x] **Q10 (Tseitin vs EF/PC):** в `docs/research/16_research_steps.md` §16.88 зафиксировано: над полями нечётной/нулевой характеристики любая PC‑рефутация $\mathrm{Tseitin}(G_n)$ для bounded‑degree экспандеров имеет степень $\Omega(|V_n|)$ и, по связи degree→size, экспоненциальный размер (Razborov 2023, Thm. 6.8 + абзац после Thm. 6.9). Над $\mathbb F_2$ степень 1 (сумма уравнений). Там же записан EF‑каркас: из 3‑CNF по вершинам выводятся XOR‑уравнения, их XOR‑сумма даёт $0=1$.
- [x] **Q9 (bounded‑occ Tseitin‑семейство):** в `docs/research/16_research_steps.md` §16.87 зафиксировано: явная 3‑регулярная expander family (см. `../resources/downloads/arora_barak.pdf`, §16.3, Remark 16.10) ⇒ $e(G)=\Omega(|V|)$, а значит 3‑CNF Tseitin из §16.85 имеет bounded‑occ = 8 и резолюционный размер $\exp(\Omega(|V|))$ по §16.86.
- [x] **Q8 (Tseitin ⇒ резолюционные нижние оценки):** извлечено из `../resources/downloads/itsykson_oparin_2013_tseitin.pdf` (Cor. 1 + Thm. 1) и зафиксировано как формализованный шаг `docs/research/16_research_steps.md` §16.86: для $\deg(G)\le k$ имеем $W\ge e(G)-1$ и $S\ge \exp((e(G)-k-1)^2/|E|)$, значит на bounded‑degree экспандерах резолюция экспоненциальна.
- [x] **Q7 (Tseitin как кандидат):** в `docs/research/16_research_steps.md` §16.85 задано определение XOR‑системы Tseitin($G,\chi$), доказана невыполнимость при нечётной сумме зарядов (паритетный инвариант) и выписана явная 3‑CNF кодировка для 3‑регулярных графов (размер $4|V|$, bounded‑occ = 8).
- [x] **Q6 (planar+occ для 15.7.4d):** доказано Planar‑3‑SAT ≤p Planar‑3‑SAT(≤4‑occ) (локальный split, сохраняющий планарность) в `docs/research/16_research_steps.md` §16.84; факт добавлен в Лемму 15.7.4d.
- [x] **Q5 (planar 3‑SAT blow‑up для 15.7.4d):** добавлена оценка $|r(\varphi)|=O(|\varphi|^2)$ как формализованный шаг `docs/research/16_research_steps.md` §16.83 и 1‑строчная ремарка в Лемме 15.7.4d.
- [x] **Q4b (канонизация/ROABP-барьер):** в Лемме 15.7.4d теперь отмечено, что NP‑трудность 3‑SAT(≤4‑occ) следует из явной линейной редукции `docs/research/16_research_steps.md` §16.81–16.82 (barrier‑чек: r применимо; NP/alg не по делу).
- [x] **Q4a (канонизация/ROABP-барьер):** добавлены формализованные шаги `docs/research/16_research_steps.md` §16.81–16.82: Tovey‑splitting даёт (O3, $L\le 3$)-SAT с линейным blow‑up, а 2‑клаузы устраняются padding‑заменой $(x\vee\neg y)\mapsto(x\vee x\vee\neg y)$, получая 3‑SAT с ограничением «каждая переменная ≤4 вхождения».
- [x] **Q1 (Pich–Santhanam 2023):** зафиксирована формальная формула `tt(f_n,s,t)`, эквивалентность и место использования (см. `docs/15_proof_complexity.md`).
- [x] **Q2 (EF+assumptions ⇒ P≠NP):** выписаны (H1$_\Pi$)/(H2$_\Pi$) как $\forall\Pi^b_1$-формулы и отмечены скрытые усиления (a.e.-твёрдость и фиксированный $R$); см. `docs/15_proof_complexity.md`.
- [x] **Q3 (минимальный нерелятивизирующий шаг):** добавлена лемма 15.7.3 (PIT-аксиомы ⇒ EF p-симулирует IPS) с эскизом и барьер-чеком; см. `docs/15_proof_complexity.md`.
- [x] **Q3a (PIT ⇒ IPS/EF):** в Лемме 15.7.3c добавлен явный линейный подсчёт размера редукции CNF→3‑CNF (≤$L$ клауз и ≤$3L$ литералов для $L$ литералов исходной CNF); см. также `docs/research/16_research_steps.md` §16.78.
- [x] **Q4 (канонизация/ROABP-барьер):** добавлена лемма 15.7.4 (слабый барьер для CNF-класса); см. `docs/15_proof_complexity.md`.
- [x] **Q2a (EF+assumptions ⇒ P≠NP):** добавлено замечание рядом с Леммой 15.7.2b: квантор $C\le m(s)$ — это лишь bounded‑ограничение длины кода (паддинг), все содержательные ограничения идут через $\mathrm{Valid}_s(C)$; см. также `docs/research/16_research_steps.md` §16.79.
- [x] **Q1a (Pich–Santhanam 2023):** связана оценка размера счётчика из Леммы 15.7.1d с 3‑CNF‑кодированием через Tseitin: добавлена ремарка рядом с 15.7.1d и формализованный шаг `docs/research/16_research_steps.md` §16.80.
