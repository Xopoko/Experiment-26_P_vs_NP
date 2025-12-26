# Открытые вопросы (рабочая очередь)

Правило: **каждый прогон агента выбирает ровно 1 пункт ниже** и делает измеримый прогресс:
доказательство/контрпример/уточнение формулировки/точная ссылка + барьер‑чек. Затем обновляет пункт.

## Активные

- [ ] **Q39 (Tseitin(Grid): depth‑gap для polynomial‑size в bounded‑depth Frege):**
  - `Priority:` P1
  - `Status:` ACTIVE (open confirmed)
  - `LastStepID:` Q39.S6-block-carcas-or-impossibility (см. `docs/research/16_tseitin.md` §16.187)
  - `NextStepID:` Q39.S7-find-forced-base-change
  - `Success:` либо явный upper на глубине $O(\\log N/\\log\\log N)$, либо барьер/контрпример для “XOR‑step” в bounded‑depth Frege
  Известно: $d_{\\mathrm{poly}}(N)\\ge\\Omega(\\log N/\\log\\log N)$ (Håstad’20, Cor. 6.6; §16.92) и $d_{\\mathrm{poly}}(N)\\le O(\\log N)$ (unpack GIRS’19/Claim 28; §16.115–§16.121).
  Узел: синтаксически симулировать шаг Gaussian elimination в bounded‑depth Frege (HR’22 отмечают как “не умеем”; §16.122).
  Прогресс: исправлено: Thm. 6.5 сам по себе **не** запрещает polynomial‑size на критической глубине $d=\\Theta(\\log n/\\log\\log n)$ (даёт лишь $\\exp(\\Omega(\\log^{\\Theta(1)}n))=n^{o(1)}$); значит нельзя “выбить” poly XOR‑step на этом $d$ одним LB‑аргументом — нужно находить структурно вынужденный base‑change/тяжёлый шаг. См. `docs/research/16_tseitin.md` §16.187. `InfoGain:` 1.
  `Барьер‑чек:` r — применимо, NP — неприменимо, alg — неприменимо.
  Следующий шаг: в grid‑каркасе локализовать место, где неизбежен base‑change между несовместимыми block‑разбиениями (или, наоборот, явно построить последовательность разбиений, удерживающую все шаги в лёгком режиме §16.130).

- [ ] **Q43 (flat local‑EF(s): существуют ли “малые” evaluations для poly‑size доказательств?):**
  - `Priority:` P0
  - `Status:` ACTIVE
  - `LastStepID:` Q43.S55-count-a1-per-center (см. `docs/research/16_tseitin.md` §16.217)
  - `NextStepID:` Q43.S56-generalize-a1-per-center
  - `Success:` либо схема построения cost‑$t$ evaluations (с $t=\\mathrm{polylog}(n)$) для каждой строки flat local‑EF(s)‑доказательства, либо точная точка поломки (где multi‑switching/representation требует nesting или глобальной поддержки)
  Контекст: каркас переноса evaluation уже есть (аналог Cor. 2.7 — §16.161; cost‑evaluation + перенос Lemma 2.13 — §16.162). Осталось показать, что “малое” доказательство **индуцирует** такие evaluations.
  Прогресс: (i) грубо: $c_2=64$, $c_1\\le 132$ (§16.191); (ii) точная цитата: в HR’22 §7.3 только индекс $j$ даёт фактор $M^{s/\\ell}$ (§16.192); (iii) toy‑bound: “differences in values” стоят ≤ $s$ бит на ветвь глубины $s$, т.е. меняют только $A$, а не $c_1,c_2$ (§16.193); (iv) доказано: (ii) “identity of additional chosen centers” покрывается тем же $b\\log\\Delta$ из Lemma 6.9, значит $c_1$ можно взять равным $4$ (single‑switching уровень), а единственный непоглощаемый вклад — $\\log M$ через фактор $M^{s/\\ell}$ (§16.195–§16.196). `InfoGain:` 2.
  (v) явный corollary: с $c_1=4$ получаем $(\\log n)^4$ и зависимость от $M$ только через $t'=(2s+1)\\log M$ и $M^{s/\\ell}$ (§16.197). `InfoGain:` 1.
  (vi) при $M=\\mathrm{poly}(n)$, $s=(\\log n)^c$, $d=(\\kappa+o(1))\\log n/\\log\\log n$: показатель $n^{1-\\kappa(5+c)-o(1)}$, нетривиально iff $\\kappa<1/(5+c)$ (§16.198). `InfoGain:` 1.
  (vii) при $\\ell:=t'=(2s+1)\\log M$ фактор $M^{s/\\ell}=\\exp(s/(2s+1))\\le e^{1/2}$ — константа (§16.199). `InfoGain:` 1.
  (viii) точная цитата: Def. 2.10 и Lemma 4.4 не содержат ограничений на $\\ell$ кроме “depth $\\ell$”; значит $\\ell=t'$ допустимо на уровне формулировок (§16.200). `InfoGain:` 1.
  (ix) toy‑тест: в §7.2–7.3 “индекс $j$ на раунд” даёт множитель $M^{s/\\ell}$; при $s=2$, $\\ell=5$ остаётся 1 раунд, но $s/\\ell<1$, т.е. нужна явная оговорка $\\ell\\le s$ или $\\lceil s/\\ell\\rceil$ (§16.201). `InfoGain:` 1.
  (x) доказано: из §7.2 + определения дерева решений (различные переменные на ветви, запрет на локально имплицированные запросы) следует, что каждый раунд даёт ≥$\\ell$ новых запросов, поэтому префикс длины $s$ включает ≤$\\lceil s/\\ell\\rceil$ раундов и фактор $M^{\\lceil s/\\ell\\rceil}$ корректен (§16.202). `InfoGain:` 1.
  (xi) контрпример: “$\\ge\\ell/4$ центров за раунд” в §7.2 относится ко всем exposed centers, поэтому bound $\\#\\text{rounds}\\le\\lceil 4a/\\ell\\rceil$ не следует; из Lemma 6.5–6.8 получается лишь $\\lceil 64a/\\ell\\rceil$ (§16.203). `InfoGain:` 1.
  (xii) точная цитата: в §7.2 “centers” — это exposed centers $S(\\lambda^j,\\sigma)$, а exposed centers определены как подмножество alive centers (§16.204). `InfoGain:` 1.
  (xiii) доказано: в Lemma 4.4 параметр $\\ell$ свободен и при $\\ell\\ge t'$ получаем $t'$‑common tree; выбор $\\ell:=64t'$ поглощает фактор 64 в $M^{\\lceil 64a/\\ell\\rceil}$ и не ухудшает $M^{s/\\ell}$ (§16.205). `InfoGain:` 1.
  (xiv) контрпример: non-chosen associated centers могут входить в $a_j$, но не дают запросов на $\\tau$,
  поэтому инъекция “$a$ → queries” не работает (§16.206). `InfoGain:` 1.
  (xv) доказано: разделение $a=a_{\\mathrm{ch}}+a_{\\mathrm{nch}}$ даёт $s\\le 64a_{\\mathrm{ch}}$,
  поэтому раунд‑фактор можно писать как $M^{\\lceil 64a_{\\mathrm{ch}}/\\ell\\rceil}$; $a_{\\mathrm{nch}}$
  определяется через $\\pi$ и не создаёт запросов (§16.207). `InfoGain:` 1.
  (xvi) доказано: в доказательстве Lemma 6.9 log t-биты используются только для chosen associated centers,
  а non-chosen восстанавливаются из pairing $\\pi$ с константным числом бит и $O(\\log \\Delta)$ на узел,
  значит $t^a$ можно заменить на $t^{a_{\\mathrm{ch}}}$ с переносом $a_{\\mathrm{nch}}$ в $\\Delta$‑часть (§16.208). `InfoGain:` 1.
  (xvii) доказано: после замены $t^a\\rightsquigarrow t^{a_{\\mathrm{ch}}}$ сумма Eq. (18) факторизуется
  в два геометрических ряда с отношениями $r_{\\mathrm{ch}}=(4t'\\log n'/\\Delta)\\cdot M^{1/t'}$ и
  $r_{\\mathrm{nch}}=4\\log n'/\\Delta$; при HR‑параметрах оба $<1$ (§16.209). `InfoGain:` 1.
  (xviii) доказано: после $t^a\\to t^{a_{\\mathrm{ch}}}$ зависимость от $a_{\\mathrm{nch}}$ остаётся
  только в $(4\\log n'/\\Delta)^{a_{\\mathrm{nch}}}$; $A_2^s$ и $M^{\\lceil 64a_{\\mathrm{ch}}/\\ell\\rceil}$
  от $a_{\\mathrm{nch}}$ не зависят (§16.210). `InfoGain:` 1.
  (xix) доказано: из HR‑оценки $\\Delta\\ge 2C\\log n'$ (при $n\\ge 20Cn'\\log n'$) следует
  $r_{\\mathrm{nch}}=4\\log n'/\\Delta\\le 2/C<1$ (для $C\\ge 3$); сумма по $a_{\\mathrm{nch}}$ — константа (§16.211).
  `InfoGain:` 1.
  (xx) доказано: из условий Lemma 4.2 $n/n'\\ge A t'\\log^4 n$ и $\\Delta\\ge n/(6n')$ вместе с
  $M^{1/t'}\\le e^{1/2}$ получаем $r_{\\mathrm{ch}}\\le 24e^{1/2}/(A\\log^3 n)<1$ при $n\\ge n_0(A)$ (§16.212).
  `InfoGain:` 1.
  (xxi) доказано: геометрические ряды дают сумму $\\le A_2^s/((1-r_{\\mathrm{ch}})(1-r_{\\mathrm{nch}}))$;
  при $r_{\\mathrm{ch}}\\le 1/2$ и $r_{\\mathrm{nch}}\\le 2/3$ получаем явную константу $6\\,A_2^s$ (§16.213).
  `InfoGain:` 1.
  (xxii) доказано: из $r_{\\mathrm{ch}}\\le 24e^{1/2}/(A\\log^3 n)$ следует
  $n_0(A)=\\lceil\\exp((48e^{1/2}/A)^{1/3})\\rceil$, при котором $r_{\\mathrm{ch}}\\le 1/2$ для всех $n\\ge n_0(A)$ (§16.214).
  `InfoGain:` 1.
  (xxiii) точная цитата: в HR'22 константа $A$ в Lemma 6.9/4.2 задается как "some constant",
  а в доказательстве появляются $A_1,A_2,A_3,A_4$ без численных оценок; поэтому явный $A_{\\min}$
  в тексте не извлекается (§16.215). `InfoGain:` 1.
  (xxiv) toy‑подсчёт: в Algorithms 2–4 при $|S^{*}_g|=1$, $s=2$, $\\ell=5$ число константных
  бит (кроме $a\\log t$, $b\\log\\Delta$ и $9|S^{*}_g|$) ≤ 18, т.е. $A_1^{\\mathrm{toy}}\\le 18$;
  общий bound на $A_1$ ещё не выведен (§16.216). `InfoGain:` 1.
  (xxv) toy‑подсчёт: при $|S^{*}_g|=2$ (один chosen + один non‑chosen), $s=2$, $\\ell=5$
  константных бит ≤ 32, что согласуется с $A_1=18$ на центр (§16.217). `InfoGain:` 1.
  `Барьер‑чек:` r — применимо, NP — неприменимо, alg — неприменимо.
  Следующий шаг: обобщить toy‑подсчёт константных бит для произвольного $|S^{*}_g|$ и
  выписать явный $A_1$ (Q43.S55-generalize-a1-bits).

## Завершённые (архив)

- [x] **Q42 (flat local‑EF(s): перенос HR t‑evaluation → Lemma 2.13):**
  закрыто: введено cost‑$t$ evaluation для flat local‑EF(s) и показано, что HR Lemma 2.13 переносится с заменой параметра глубины на стоимость (порог $t\\le\\Theta(n/s)$); см. `docs/research/16_tseitin.md` §16.162. `StepID:` Q42.S1-define-evaluation-flat. `InfoGain:` 2.
- [x] **Q41 (если Q39 открыт: локальные расширения):**
  закрыто: (i) контрпример показывает, что “nested extension” без разворачивания поддержки делает local‑EF(s) тривиальной (§16.160);
  (ii) в flat‑модели доказан аналог HR Cor. 2.7 при $\\mathrm{supp}_s/\\mathrm{cost}_s$ (§16.161). `StepID:` Q41.S3-proof-cor27-analogue-flat. `InfoGain:` 2.
- [x] **Q40 (литературный статус Q39):**
  закрыто: в Håstad–Risse’22 §1.2 зафиксирована точная цитата “We do not know how to syntactically translate a Gaussian elimination step …”, со страницей (p. 4; PDF p. 6); см. `docs/research/16_tseitin.md` §16.122. `StepID:` Q40.S1-quote-hr22-1.2. `InfoGain:` 1.
- [x] **Q38 (константы в depth‑threshold для Tseitin(Grid): сравнить Håstad’20 и GIRS’19):**
  закрыто: после пересчёта (§16.117+§16.120) сравнение «59 vs верхняя константа» оказалось некорректной целью: известный polynomial‑size upper на grid имеет масштаб $O(\\log n)$, а не $\\Theta(\\log n/\\log\\log n)$.
- [x] **Q37 (вынести в основной текст краткий итог по Tseitin(Grid) — текущие границы):**
  закрыто: в `docs/15_proof_complexity.md` теперь стоит корректная формулировка
  $\\Omega(\\log N/\\log\\log N)\\le d_{\\mathrm{poly}}(N)\\le O(\\log N)$; детали: §16.92+§16.115+§16.116+§16.120.
- [x] **Q36 (свести глубину $d$ из GIRS’19 Thm. 19 к глубине в 16.92/16.97 и переписать в терминах $N$):**
  закрыто: перезапись в терминах $N$ сделана в `docs/research/16_tseitin.md` §16.116 (и поправлена: tight‑утверждение снято).
- [x] **Q35 (квантифицировать верхнюю оценку Thm. 19 (GIRS’19) и сравнить с 16.92):**
  закрыто: в `docs/research/16_tseitin.md` §16.115+§16.120 выписан явный upper $\\mathrm{poly}(|T|)\\cdot 2^{O(d\\cdot X^{2/d})}$ из Claim 28,
  и показано, что он гарантирует polynomial‑size лишь при $d=\\Theta(\\log n)$ (а при $\\Theta(\\log n/\\log\\log n)$ — только quasi‑poly).
- [x] **Q34 (явная конструкция $O(\\log n)$‑depth Frege‑рефутации Tseitin в стандартном языке):**
  закрыто: в `docs/research/16_tseitin.md` §16.93 выписан самодостаточный вывод через Urquhart’87 (16.91) + Spira‑балансировку (16.94)
  + line‑replacement (16.113) + p‑доказательства эквивалентности балансировки (16.114).
- [x] **Q33 (Spira‑балансировка: где взять p‑размерный Frege‑вывод $A\\leftrightarrow A'$?):**
  закрыто: Buss’97, Proof (Sketch) к Thm. 3 (p. 8) прямо отмечает наличие polynomial‑size Frege‑доказательств,
  верифицирующих корректность Spira‑перевода (в частности, эквивалентности вида $A\\leftrightarrow A'$);
  это зафиксировано в `docs/research/16_tseitin.md` §16.114, и 16.94 теперь строгая через §16.113.
- [x] **Q32 (закрыть «техническую» часть 16.94: балансировка линий в Frege):**
  закрыто: схема «из $A$ и $A\\leftrightarrow A'$ выводить $A'$» и оценка blow‑up записаны в `docs/research/16_tseitin.md` §16.113;
  статус шага 16.94 обновлён на «доказано».
- [x] **Q31 (перепривязать §16.110 к §16.112 и убрать неформальность):**
  закрыто: в §16.110 заменено $\\log n\\le\\log S$ на ссылку «см. §16.112» и проверено, что других мест использования $n\\le S$ нет
  (дальше используется только $\\log n\\le\\log S$ через §16.112).
- [x] **Q30 (обосновать шаг $\\log n\\le\\log S$ для Tseitin: $S\\ge |V(G)|$):**
  закрыто: для связного $G$ удаление любого блока $\\mathrm{PARITY}_{v,\\sigma(v)}$ делает $T(G,\\sigma)$ выполнимой (явная конструкция по остовному дереву),
  значит любая резолюционная рефутация использует хотя бы одну исходную клаузу из каждого блока и $S\\ge |V(G)|$; см. `docs/research/16_tseitin.md` §16.112.
- [x] **Q29 (свести AR’11 (2.15/2.17/2.18) в одну «употребимую» ремарку):**
  закрыто: сводка с явными ссылками и константами записана в `docs/research/16_tseitin.md` §16.111.
- [x] **Q28 (AR’11 Thm. 2.17: явная зависимость в $\\bigl(\\tilde\\ell(G)\\log S\\bigr)^{O(\\tilde\\ell(G)^2)}$):**
  закрыто: из доказательства Thm. 2.17 можно извлечь явную грубую константу $c=6$ в
  $W\\le (C\\,\\tilde\\ell(G)\\log S)^{c\\tilde\\ell(G)^2}$; см. `docs/research/16_tseitin.md` §16.110.
- [x] **Q27 (AR’11 Thm. 2.15: явная степень в $\\ell(G)^{O(1)}$):**
  закрыто: из (5.4) и (5.6) в доказательстве AR’11 Thm. 2.15 следует $W\\le O(\\ell(G)^7\\log S)$; см. `docs/research/16_tseitin.md` §16.109.
- [x] **Q26 (AR’11: планарные графы с ограниченной степенью граней ⇒ ограниченная cyclicity $\\ell(G)$):**
  закрыто: если $G$ 2‑реберно‑связен и допускает плоское вложение, где каждая грань имеет степень $\\le d$,
  то границы граней дают покрытие рёбер циклами длины $\\le d$ и кратности $\\le 2$, значит $\\ell(G)\\le\\max\\{d,2\\}$; см. `docs/research/16_tseitin.md` §16.108.
- [x] **Q25 (Tseitin: $W(T(G,\\sigma)\\vdash\\bot)$ через $\\mathrm{cw}(G)$):**
  закрыто: из $\\tfrac18\\,\\mathrm{wb}(H_T)\\le W\\le 2\\,\\mathrm{wb}(H_T)$ (AR’11, Thm. 2.12 + §4) и
  $\\mathrm{wb}(H_T)=\\mathrm{wb}(G^*)=\\mathrm{cw}(G)$ (Remark 2.11 + §16.105–16.106) получаем
  $\\mathrm{cw}(G)/8\\le W(T(G,\\sigma)\\vdash\\bot)\\le 2\\,\\mathrm{cw}(G)$; см. `docs/research/16_tseitin.md` §16.107.
- [x] **Q24 (повторы гиперрёбер vs $\\mathrm{wb}$ в AR’11 Remark 2.11):**
  закрыто: в AR’11 гиперграф $H_{T(G,\\sigma)}$ — это мульти‑$G^*$ (Def. 2.1 допускает multiset), где $E(v)$ повторяется $2^{\\deg(v)-1}$ раз (Remark 2.11),
  и для $G^*$ такие повторы не меняют $\\mathrm{wb}$; см. `docs/research/16_tseitin.md` §16.106.
- [x] **Q23 (branch‑width $G^*$ vs carving width $\\mathrm{cw}(G)$):**
  закрыто: для двойственного гиперграфа $G^*$ (гиперрёбра — звёзды $E(v)$) branch‑decomposition по гиперрёбрам эквивалентна carving‑декомпозиции $G$ по вершинам,
  и $\\mathrm{wb}(G^*)=\\mathrm{cw}(G)$; см. `docs/research/16_tseitin.md` §16.105.
- [x] **Q22 (константы в $\\Theta(\\cdot)$ из AR’11 Thm. 2.12):**
  закрыто: из AR’11 Prop. 4.3 и доказательства Lemma 4.4 (через Figure 3.1 / Lemma 3.1) получаем явные оценки
  $\\tfrac18\\,\\mathrm{wb}(T(G,\\sigma))\\le W(T(G,\\sigma)\\vdash\\bot)\\le 2\\,\\mathrm{wb}(T(G,\\sigma))$;
  см. `docs/research/16_tseitin.md` §16.104 и
  `../resources/downloads/alekhnovich_razborov_2011_satisfiability_branchwidth_tseitin.pdf`.
- [x] **Q21 (Tseitin‑width через branch‑width):**
  закрыто: Alekhnovich–Razborov (2011, Thm. 2.12) утверждают
  $\\mathrm{wb}(T(G,\\sigma))=\\Theta(W(T(G,\\sigma)\\vdash\\bot))$, а Remark 2.11 уточняет, что подлежащий гиперграф — это $G^*$ (с повторениями);
  см. `docs/research/16_tseitin.md` §16.103 и `../resources/downloads/alekhnovich_razborov_2011_satisfiability_branchwidth_tseitin.pdf`.
- [x] **Q20 (согласовать использование $w(G)$ в Cor. 34 / §16.98):**
  закрыто: в §16.98 добавлено явное определение $w(G):=W(T(G,\\varphi)\\vdash\\bot)-1$ и цепочка
  $n^{O(w(G))}=2^{O(\\mathrm{tw}(G)\\,\\Delta(G)\\log n)}$ через Harvey–Wood (2014, (2));
  см. `docs/research/16_tseitin.md` §16.102 и
  `../resources/downloads/harvey_wood_2014_treewidth_line_graphs.pdf`.
- [x] **Q19 (точная ссылка на $w(G)=\max\{\\Delta(G),\\mathrm{tw}(L(G))\\}-1$ для Tseitin‑width):**
  закрыто: Galesi–Talebanfard–Torán (2018, ECCC TR18‑170) дают Cor. 8:
  $W(T(G,\\varphi)\\vdash\\bot)=\\max\\{\\Delta(G),\\mathrm{ec}(G)-1\\}$ и Cor. 16:
  $\\mathrm{ec}(G)=\\mathrm{tw}(L(G))+1$, откуда $W=\\max\\{\\Delta(G),\\mathrm{tw}(L(G))\\}$ и $w(G)=W-1$.
  См. `docs/research/16_tseitin.md` §16.101 и `../resources/downloads/galesi_talebanfard_toran_2018_cops_robber_tseitin.pdf`.
- [x] **Q18 (связать carving width $W$ с $w(G)$ в Cor. 34):** закрыто: доказано $\\mathrm{cw}(G)\\le \\mathrm{tw}(L(G))+1$;
  вместе с формулой для Tseitin‑width $w(G)=\\max\\{\\Delta(G),\\mathrm{tw}(L(G))\\}-1$ (16.101) получаем
  $\\mathrm{cw}(G)\\le w(G)+2$ и можно переписывать $n^{O(\\mathrm{cw}(G))}$ как $n^{O(w(G))}$; см. `docs/research/16_tseitin.md` §16.100.
- [x] **Q17 (Cor. 34: зависимости и «где именно берётся» tree‑like Res ≤ n^{O(w)}):** закрыто:
  точная ссылка для tree‑like upper bound — Beame–Beck–Impagliazzo (2016), Lemma 61 (через carving width),
  см. `docs/research/16_tseitin.md` §16.99 и
  `../resources/downloads/beame_beck_impagliazzo_2016_time_space_tradeoffs_resolution.pdf`.
- [x] **Q16 (Tseitin: bounded‑depth Frege ↔ tree‑like Resolution):** закрыто: точная формулировка Cor. 34:
  bounded‑depth Frege‑доказательство размера $S$ ⇒ tree‑like Resolution размера $\\le 2^{\\mathrm{poly}(\\log S)}$
  (Galesi–Itsykson–Riazanov–Sofronova 2019, Cor. 34), см. `docs/research/16_tseitin.md` §16.98 и
  `../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`.
- [x] **Q15 (сузить разрыв depth‑vs‑size для Tseitin):**
  закрыто: зафиксированы Thm. 18/19 из GIRS’19 (2019, ECCC TR19‑069) как family bounds $2^{\\mathrm{tw}(G)^{\\Omega(1/d)}}$ и $2^{\\mathrm{tw}(G)^{O(1/d)}}\\cdot\\mathrm{poly}(|\\mathrm{Tseitin}(G,f)|)$
  (в исходной статье $d$ трактуется как фиксированная глубина; для растущего $d$ важна явная зависимость от $d$, см. §16.115–§16.121 и Q39).
  См. `docs/research/16_tseitin.md` §16.97 и `../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`.
- [x] **Q14 (Frege‑depth для Tseitin):** закрыто: poly‑size Frege‑рефутация (Urquhart 1987; §16.91),
  bounded‑depth lower bound на grid (Håstad 2020; §16.92), upper bound depth $O(\\log n)$ для bounded‑degree
  (Håstad 2020 remark + Buss 1997/Spira‑перевод; §16.93 и §16.95), и ссылка на формульную балансировку (Bonet–Buss 2002; §16.94).
- [x] **Q13 (Frege/EF симулирует XOR/Gauss):** в `docs/research/16_tseitin.md` §16.88 добавлена точная ссылка,
  что EF «легко симулирует Gaussian elimination» (Bonet–Buss–Pitassi 2002, `../resources/downloads/bonet_buss_pitassi_2002_hard_examples_frege.pdf`, p. 7),
  что закрывает фольклорность EF‑каркаса XOR‑суммирования.
- [x] **Q12 (TseitinCNF vs PC при $\\mathrm{char}(F)\\ne 2$):** в `docs/research/16_tseitin.md` §16.90
  показано: TseitinCNF (3‑CNF) и биномиальная Tseitin (Fourier/±1‑база) p‑эквивалентны по степени в PC при $\\mathrm{char}(F)\\ne 2$,
  поэтому degree/size‑LB (Razborov 2023, Thm. 6.8; Beame–Sabharwal 2000, Thm. 2.18) переносятся на TseitinCNF.
- [x] **Q11 (TseitinCNF vs PC над $\\mathbb F_2$):** в `docs/research/16_tseitin.md` §16.89
  дан явный PC‑вывод линейного уравнения вершины из 4 клауз и итоговая рефутация степени 3 и размера $O(|V|)$.
- [x] **Q10 (Tseitin vs EF/PC):** в `docs/research/16_tseitin.md` §16.88 зафиксировано: над полями нечётной/нулевой характеристики любая PC‑рефутация $\\mathrm{Tseitin}(G_n)$ для bounded‑degree экспандеров имеет степень $\\Omega(|V_n|)$ и, по связи degree→size, экспоненциальный размер (Razborov 2023, Thm. 6.8 + абзац после Thm. 6.9). Над $\\mathbb F_2$ степень 1 (сумма уравнений). Там же записан EF‑каркас: из 3‑CNF по вершинам выводятся XOR‑уравнения, их XOR‑сумма даёт $0=1$.
- [x] **Q9 (bounded‑occ Tseitin‑семейство):** в `docs/research/16_tseitin.md` §16.87 зафиксировано: явная 3‑регулярная expander family (см. `../resources/downloads/arora_barak.pdf`, §16.3, Remark 16.10) ⇒ $e(G)=\\Omega(|V|)$, а значит 3‑CNF Tseitin из §16.85 имеет bounded‑occ = 8 и резолюционный размер $\\exp(\\Omega(|V|))$ по §16.86.
- [x] **Q8 (Tseitin ⇒ резолюционные нижние оценки):** извлечено из `../resources/downloads/itsykson_oparin_2013_tseitin.pdf` (Cor. 1 + Thm. 1) и зафиксировано как формализованный шаг `docs/research/16_tseitin.md` §16.86: для $\\deg(G)\\le k$ имеем $W\\ge e(G)-1$ и $S\\ge \\exp((e(G)-k-1)^2/|E|)$, значит на bounded‑degree экспандерах резолюция экспоненциальна.
- [x] **Q7 (Tseitin как кандидат):** в `docs/research/16_tseitin.md` §16.85 задано определение XOR‑системы Tseitin($G,\\chi$), доказана невыполнимость при нечётной сумме зарядов (паритетный инвариант) и выписана явная 3‑CNF кодировка для 3‑регулярных графов (размер $4|V|$, bounded‑occ = 8).
- [x] **Q6 (planar+occ для 15.7.4d):** доказано Planar‑3‑SAT ≤p Planar‑3‑SAT(≤4‑occ) (локальный split, сохраняющий планарность) в `docs/research/16_encodings.md` §16.84; факт добавлен в Лемму 15.7.4d.
- [x] **Q5 (planar 3‑SAT blow‑up для 15.7.4d):** добавлена оценка $|r(\\varphi)|=O(|\\varphi|^2)$ как формализованный шаг `docs/research/16_encodings.md` §16.83 и 1‑строчная ремарка в Лемме 15.7.4d.
- [x] **Q4b (канонизация/ROABP-барьер):** в Лемме 15.7.4d теперь отмечено, что NP‑трудность 3‑SAT(≤4‑occ) следует из явной линейной редукции `docs/research/16_encodings.md` §16.81–16.82 (barrier‑чек: r применимо; NP/alg не по делу).
- [x] **Q4a (канонизация/ROABP-барьер):** добавлены формализованные шаги `docs/research/16_encodings.md` §16.81–16.82: Tovey‑splitting даёт (O3, $L\\le 3$)-SAT с линейным blow‑up, а 2‑клаузы устраняются padding‑заменой $(x\\vee\\neg y)\\mapsto(x\\vee x\\vee\\neg y)$, получая 3‑SAT с ограничением «каждая переменная ≤4 вхождения».
- [x] **Q1 (Pich–Santhanam 2023):** зафиксирована формальная формула `tt(f_n,s,t)`, эквивалентность и место использования (см. `docs/15_proof_complexity.md`).
- [x] **Q2 (EF+assumptions ⇒ P≠NP):** выписаны (H1$_\\Pi$)/(H2$_\\Pi$) как $\\forall\\Pi^b_1$-формулы и отмечены скрытые усиления (a.e.-твёрдость и фиксированный $R$); см. `docs/15_proof_complexity.md`.
- [x] **Q3 (минимальный нерелятивизирующий шаг):** добавлена лемма 15.7.3 (PIT-аксиомы ⇒ EF p-симулирует IPS) с эскизом и барьер-чеком; см. `docs/15_proof_complexity.md`.
- [x] **Q3a (PIT ⇒ IPS/EF):** в Лемме 15.7.3c добавлен явный линейный подсчёт размера редукции CNF→3‑CNF (≤$L$ клауз и ≤$3L$ литералов для $L$ литералов исходной CNF); см. также `docs/research/16_encodings.md` §16.78.
- [x] **Q4 (канонизация/ROABP-барьер):** добавлена лемма 15.7.4 (слабый барьер для CNF-класса); см. `docs/15_proof_complexity.md`.
- [x] **Q2a (EF+assumptions ⇒ P≠NP):** добавлено замечание рядом с Леммой 15.7.2b: квантор $C\\le m(s)$ — это лишь bounded‑ограничение длины кода (паддинг), все содержательные ограничения идут через $\\mathrm{Valid}_s(C)$; см. также `docs/research/16_encodings.md` §16.79.
- [x] **Q1a (Pich–Santhanam 2023):** связана оценка размера счётчика из Леммы 15.7.1d с 3‑CNF‑кодированием через Tseitin: добавлена ремарка рядом с 15.7.1d и формализованный шаг `docs/research/16_encodings.md` §16.80.
