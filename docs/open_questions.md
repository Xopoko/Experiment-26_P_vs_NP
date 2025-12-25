# Открытые вопросы (рабочая очередь)

Правило: **каждый прогон агента выбирает ровно 1 пункт ниже** и делает измеримый прогресс:
доказательство/контрпример/уточнение формулировки/точная ссылка + барьер‑чек. Затем обновляет пункт.

## Активные

- [ ] **Q39 (Tseitin(Grid): закрыть разрыв по глубине для polynomial‑size):**
  Нижняя оценка: Håstad’20, Cor. 6.6 даёт необходимость depth $=\\Omega(\\log N/\\log\\log N)$ для polynomial‑size (где $N=\\Theta(n^2)$).
  Верхняя оценка: из GIRS’19 (Claim 28 → Thm. 27 → Thm. 26) следует гарантированный polynomial‑size лишь при depth $=O(\\log N)$;
  при depth $=\\Theta(\\log N/\\log\\log N)$ этот upper даёт только quasi‑poly (см. §16.120).
  Прогресс: §16.119 фиксирует условную явную константу в экспоненте ($c=4$ при $X^{1/d}\\ge\\max(2d,6)$), но это условие не покрывает
  режим, где хотелось бы получить polynomial‑size; §16.115+§16.120 дают явный unconditional upper вида $\\mathrm{poly}(|T|)\\cdot 2^{O(d\\cdot X^{2/d})}$, а §16.121 показывает,
  что даже оптимизация этого bound внутри Claim 28 даёт сертификат polynomial‑size только при $d=\\Omega(\\log X)$ (и минимум при $d=2\\ln X$).
		  Доп.: Håstad–Risse (FOCS’22 full-length) §1.2 прямо формулируют «нехватающий» upper‑шаг: они умеют представлять промежуточные XOR‑уравнения
		  небольшими depth‑$d$ формулами, но не знают, как синтаксически симулировать шаг Gaussian elimination в bounded‑depth Frege (см. §16.122).
		  Representation‑часть: в HR §1.2 (см. §16.123) заявлено, что можно выписать depth‑$d$ формулы размера $M$, представляющие $\\mathrm{PARITY}$ и $\\neg\\mathrm{PARITY}$ на блоке размера $(\\log M)^{d-1}$.
			  Но §16.147–§16.153 показывают, что для **формул** (tree‑size) это несовместимо с известным tight bound: Rossman’16 даёт $\\log\\mathrm{size}=\\Theta((d-1)\\,n^{1/(d-1)})$, т.е. при size $\\le M$ максимум
			  $$n\\le\\bigl(\\Theta((\\log M)/(d-1))\\bigr)^{d-1}.$$
		  Поэтому при пороговой глубине $d\\approx\\log n/\\log\\log n$ и $M=\\mathrm{poly}(n)$ такие PARITY‑формулы покрывают лишь $n^{o(1)}$ переменных, и сведение Q39 к «одному XOR‑шагу» (как в §16.124–§16.126) требует пересмотра модели representability.
  §16.127 фиксирует «локальный барьер»: в EF XOR‑сложение тривиально (Gaussian elimination), но универсальная балансировка даёт для Frege лишь глубину $O(\\log n)$, не $O(\\log n/\\log\\log n)$.
  §16.128 фиксирует ещё один «барьер техники»: tree‑partition upper из GIRS’19 (Claim 28) требует $d=\\Omega(\\log n)$ даже для этой 3‑вершинной Tseitin‑семьи (и потому не сертифицирует пороговую глубину).
  §16.129 уточняет источник «лишнего множителя $d$»: в GIRS’19, §4.1 (Lemma 21) их выводимое в bounded‑depth Frege представление $\\mathrm{PARITY}$ имеет размер $\\prod_i(2^{t_i+1}t_i)=\\exp(\\Theta(\\sum_i t_i))$, и при $\\prod_i t_i\\ge n$ оптимум даёт лишь $\\exp(\\Theta(d\\,n^{1/d}))$ (quasi‑poly при $d\\approx\\log n/\\log\\log n$).
  §16.130 даёт «условно лёгкий» случай XOR‑шага: если все уравнения записаны как паритет по $k$ блок‑паритетам одного фиксированного разбиения, то один XOR‑шаг доказывается за $2^{O(k)}$ и после подстановки имеет polynomial‑size при $k=O(\\log n)$; значит реальный узел — уметь держать/выводить такие block‑representations для нужных промежуточных уравнений.
  §16.131 показывает, что один фиксированный block‑basis не покрывает column‑summing на grid при $k=\\mathrm{polylog}(n)$: промежуточные «границы колонок» дают $n-1$ непересекающихся множеств рёбер и имеют ранг $n-1$, значит нужен $k=\\Omega(n)$.
  §16.132 фиксирует «барьер метода»: универсальный base‑change между двумя block‑representations через общее уточнение разбиений раздувает число блоков $k\\mapsto k^2$, что при $k=\\Theta(\\log n)$ уже даёт quasi‑poly ($2^{\\Theta(\\log^2 n)}$).
  §16.133 уточняет, что этот blow‑up не универсален: для interval‑partition на одном порядке общее уточнение имеет лишь $\\le k_1+k_2-1$ блоков.
  §16.134 уточняет, что в самой column‑summing стратегии промежуточные множества рёбер — это границы прямоугольников и они раскладываются на $O(1)$ row‑interval сегментов; значит $k^2$‑барьер §16.132 локально не срабатывает.
  §16.135 фиксирует доп. барьер: даже для 1D‑префиксов $L_t=[1..t]$ любая попытка держать один фиксированный малый базис «segment blocks», покрывающий все $t$, требует $k\\ge n$ (ранг $n$).
  §16.136 даёт каноническую dyadic‑разбивку префикса $[t]$ на $O(\\log n)$ дизъюнктных интервалов длины степени двойки и показывает, что обновление $t\\mapsto t+1$ сводится к $O(\\log n)$ merge‑операциям на соседних равных интервалах.
  §16.137 уточняет, что сам merge для дизъюнктных блоков становится «easy case» §16.130, **если** принять формулы паритета блоков как атомы; значит узел — не tautология merge, а умение поддерживать/переиспользовать такие блок‑паритеты в ходе всей стратегии.
  §16.138 уточняет синтаксическую тонкость: в Schoenfield‑Frege отрицание жёстко подставляется как $\\sigma(\\neg p)=\\neg\\sigma(p)$, поэтому HR‑пара «PARITY и $\\neg$PARITY» как две OR‑формулы не даёт автоматически пару литералов для Cut без дополнительных эквивалентностей $N\\leftrightarrow\\neg P$.
  §16.139 фиксирует редукцию: если для блоков доказуемы polynomial‑size «consistency axioms» $N_i\\leftrightarrow\\neg P_i$, то dual‑rail интерпретация превращает HR‑representation в реальный подстановочный Frege‑шаг (и «easy case» merge становится применим).
  §16.140 показывает, что при константном запасе по глубине можно вообще не вводить отдельную формулу $N$: достаточно иметь $P$ глубины $\\le d-O(1)$ и использовать синтаксическое $\\neg P$ (при необходимости — OR‑обёртку $\\neg P\\vee\\bot$).
    §16.141 подтверждает арифметику параметров: константная потеря глубины совместима с порогом $d\\approx\\log n/\\log\\log n$ при $M=\\mathrm{poly}(n)$, так что переход к $\\neg P$ не ломает representability.
    §16.142 фиксирует точную формулировку HR’25 §1.2 “representing parity” (база $\\{\\vee,\\neg\\}$, глубина как чередования) и увязывает блок‑размер $(\\log M)^{d-1}$ с классическим upper bound для PARITY (Håstad’86, Remark 6).
    §16.143 показывает, что toy‑случай $S_1\\cap S_2=\\{x\\}$ не требует $k^2$‑взрыва: если обе строки уже в block‑форме (§16.130), то общий блок‑базис строится с $k\\le k_1+k_2+1$, и XOR‑шаг сводится к §16.130.
    §16.144 фиксирует, что в column‑summing переход $t\\to t+1$ всегда имеет пересечение ровно в одном ребре: $\\delta(R_{j,t+1})=\\delta(R_{j,t})\\triangle E((t+1,j))$ и $|\\delta(R_{j,t})\\cap E((t+1,j))|=1$.
	    §16.145 выписывает такой «протокол» для одного столбца: поддержание $k=O(\\log n)$ сводится к XOR‑шагу с пересечением 1 и $O(\\log n)$ dyadic‑merge (без $k^2$‑base‑change).
	    §16.146 показывает, что сложение соседних столбцов действительно попадает в «easy case» §16.130 при фиксированном dyadic‑разбиении полос $S_j$: большое пересечение $|S_j|=n$ отменяется на уровне общих блок‑атомов.
	    §16.147 фиксирует caveat: Håstad’86, Remark 6 — про схемы, а наивная развёртка схемы в формулу даёт $M^{\\Theta(d)}$ (quasi‑poly на пороге), так что representability‑часть требует отдельного формульного обоснования.
		    §16.148 формализует «слабый» формульный upper bound через DNF‑композицию: он даёт лишь $m\\le (\\Theta((\\log M)/(d-1)))^{d-1}$, что при $d\\approx\\log n/\\log\\log n$ и $M=\\mathrm{poly}(n)$ означает $m=n^{o(1)}\\ll n$.
		    §16.149 закрывает узел: Rossman’16 даёт matching lower bound для PARITY‑формул, так что множитель $(d-1)$ в показателе неустраним и блок $(\\log M)^{d-1}$ при size $M$ невозможен для формул при растущем $d$.
		    §16.150 формализует, что HR‑глубина (чередования $\\vee/\\neg$) сводится к De Morgan‑глубине без blow‑up размера, поэтому Rossman’16 применим непосредственно к bounded‑depth Frege‑строкам.
		    §16.151 уточняет чтение HR §1.2: по их же определению формул как деревьев “$(\\log M)^{d-1}$ при size $M$” можно понимать лишь как константно‑глубинную эвристику/подавление полиномиального фактора (иначе нужно $M^{\\Omega(d)}$), т.е. в Q39 при растущем $d$ эту representability использовать нельзя.
		    §16.152 показывает, что блок $(\\log M)^{d-1}$ как раз естественен для **схем** за счёт sharing (fan‑out), и именно этим объясняется HR‑зависимость.
		    §16.153 фиксирует формально: sharing внутри строки = extension variables, т.е. “circuit‑Frege” p‑эквивалентно EF.
		    Следующий шаг: в Håstad’20/HR’22 найти место, где аргумент требует fan‑out 1 (дерево) и решить, распространяется ли LB на circuit‑Frege/EF‑вариант.

## Завершённые (архив)

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
- [x] **Q18 (связать carving width $W$ с $w(G)$ в Cor. 34):** закрыто: доказано $\mathrm{cw}(G)\le \mathrm{tw}(L(G))+1$;
  вместе с формулой для Tseitin‑width $w(G)=\max\{\\Delta(G),\\mathrm{tw}(L(G))\\}-1$ (16.101) получаем
  $\mathrm{cw}(G)\le w(G)+2$ и можно переписывать $n^{O(\\mathrm{cw}(G))}$ как $n^{O(w(G))}$; см. `docs/research/16_tseitin.md` §16.100.
- [x] **Q17 (Cor. 34: зависимости и «где именно берётся» tree‑like Res ≤ n^{O(w)}):** закрыто:
  точная ссылка для tree‑like upper bound — Beame–Beck–Impagliazzo (2016), Lemma 61 (через carving width),
  см. `docs/research/16_tseitin.md` §16.99 и
  `../resources/downloads/beame_beck_impagliazzo_2016_time_space_tradeoffs_resolution.pdf`.
- [x] **Q16 (Tseitin: bounded‑depth Frege ↔ tree‑like Resolution):** закрыто: точная формулировка Cor. 34:
  bounded‑depth Frege‑доказательство размера $S$ ⇒ tree‑like Resolution размера $\le 2^{\mathrm{poly}(\log S)}$
  (Galesi–Itsykson–Riazanov–Sofronova 2019, Cor. 34), см. `docs/research/16_tseitin.md` §16.98 и
  `../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`.
- [x] **Q15 (сузить разрыв depth‑vs‑size для Tseitin):** закрыто: Galesi–Itsykson–Riazanov–Sofronova (2019, ECCC TR19‑069)
  дают tight depth‑vs‑size через treewidth: для $d\le \Theta(\log n/\log\log n)$ размер depth‑$d$ Frege‑рефутаций
  $\ge 2^{\mathrm{tw}(G)^{\Omega(1/d)}}$ (Thm. 18) и $\le 2^{\mathrm{tw}(G)^{O(1/d)}}\cdot\mathrm{poly}(|\mathrm{Tseitin}(G,f)|)$
  (Thm. 19), см. `docs/research/16_tseitin.md` §16.97 и
  `../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`.
  В частности, для $\mathrm{tw}(G)=\Omega(n)$ (grid/экспандеры) polynomial‑size ⇔ depth $\Theta(\log n/\log\log n)$, что
  усиливает PRST’16 (16.96) и согласуется с Håstad’20 (16.92).
- [x] **Q14 (Frege‑depth для Tseitin):** закрыто: poly‑size Frege‑рефутация (Urquhart 1987; §16.91),
  bounded‑depth lower bound на grid (Håstad 2020; §16.92), upper bound depth $O(\log n)$ для bounded‑degree
  (Håstad 2020 remark + Buss 1997/Spira‑перевод; §16.93 и §16.95), и ссылка на формульную балансировку (Bonet–Buss 2002; §16.94).
- [x] **Q13 (Frege/EF симулирует XOR/Gauss):** в `docs/research/16_tseitin.md` §16.88 добавлена точная ссылка,
  что EF «легко симулирует Gaussian elimination» (Bonet–Buss–Pitassi 2002, `../resources/downloads/bonet_buss_pitassi_2002_hard_examples_frege.pdf`, p. 7),
  что закрывает фольклорность EF‑каркаса XOR‑суммирования.
- [x] **Q12 (TseitinCNF vs PC при $\mathrm{char}(F)\ne 2$):** в `docs/research/16_tseitin.md` §16.90
  показано: TseitinCNF (3‑CNF) и биномиальная Tseitin (Fourier/±1‑база) p‑эквивалентны по степени в PC при $\mathrm{char}(F)\ne 2$,
  поэтому degree/size‑LB (Razborov 2023, Thm. 6.8; Beame–Sabharwal 2000, Thm. 2.18) переносятся на TseitinCNF.
- [x] **Q11 (TseitinCNF vs PC над $\mathbb F_2$):** в `docs/research/16_tseitin.md` §16.89
  дан явный PC‑вывод линейного уравнения вершины из 4 клауз и итоговая рефутация степени 3 и размера $O(|V|)$.
- [x] **Q10 (Tseitin vs EF/PC):** в `docs/research/16_tseitin.md` §16.88 зафиксировано: над полями нечётной/нулевой характеристики любая PC‑рефутация $\mathrm{Tseitin}(G_n)$ для bounded‑degree экспандеров имеет степень $\Omega(|V_n|)$ и, по связи degree→size, экспоненциальный размер (Razborov 2023, Thm. 6.8 + абзац после Thm. 6.9). Над $\mathbb F_2$ степень 1 (сумма уравнений). Там же записан EF‑каркас: из 3‑CNF по вершинам выводятся XOR‑уравнения, их XOR‑сумма даёт $0=1$.
- [x] **Q9 (bounded‑occ Tseitin‑семейство):** в `docs/research/16_tseitin.md` §16.87 зафиксировано: явная 3‑регулярная expander family (см. `../resources/downloads/arora_barak.pdf`, §16.3, Remark 16.10) ⇒ $e(G)=\Omega(|V|)$, а значит 3‑CNF Tseitin из §16.85 имеет bounded‑occ = 8 и резолюционный размер $\exp(\Omega(|V|))$ по §16.86.
- [x] **Q8 (Tseitin ⇒ резолюционные нижние оценки):** извлечено из `../resources/downloads/itsykson_oparin_2013_tseitin.pdf` (Cor. 1 + Thm. 1) и зафиксировано как формализованный шаг `docs/research/16_tseitin.md` §16.86: для $\deg(G)\le k$ имеем $W\ge e(G)-1$ и $S\ge \exp((e(G)-k-1)^2/|E|)$, значит на bounded‑degree экспандерах резолюция экспоненциальна.
- [x] **Q7 (Tseitin как кандидат):** в `docs/research/16_tseitin.md` §16.85 задано определение XOR‑системы Tseitin($G,\chi$), доказана невыполнимость при нечётной сумме зарядов (паритетный инвариант) и выписана явная 3‑CNF кодировка для 3‑регулярных графов (размер $4|V|$, bounded‑occ = 8).
- [x] **Q6 (planar+occ для 15.7.4d):** доказано Planar‑3‑SAT ≤p Planar‑3‑SAT(≤4‑occ) (локальный split, сохраняющий планарность) в `docs/research/16_encodings.md` §16.84; факт добавлен в Лемму 15.7.4d.
- [x] **Q5 (planar 3‑SAT blow‑up для 15.7.4d):** добавлена оценка $|r(\varphi)|=O(|\varphi|^2)$ как формализованный шаг `docs/research/16_encodings.md` §16.83 и 1‑строчная ремарка в Лемме 15.7.4d.
- [x] **Q4b (канонизация/ROABP-барьер):** в Лемме 15.7.4d теперь отмечено, что NP‑трудность 3‑SAT(≤4‑occ) следует из явной линейной редукции `docs/research/16_encodings.md` §16.81–16.82 (barrier‑чек: r применимо; NP/alg не по делу).
- [x] **Q4a (канонизация/ROABP-барьер):** добавлены формализованные шаги `docs/research/16_encodings.md` §16.81–16.82: Tovey‑splitting даёт (O3, $L\le 3$)-SAT с линейным blow‑up, а 2‑клаузы устраняются padding‑заменой $(x\vee\neg y)\mapsto(x\vee x\vee\neg y)$, получая 3‑SAT с ограничением «каждая переменная ≤4 вхождения».
- [x] **Q1 (Pich–Santhanam 2023):** зафиксирована формальная формула `tt(f_n,s,t)`, эквивалентность и место использования (см. `docs/15_proof_complexity.md`).
- [x] **Q2 (EF+assumptions ⇒ P≠NP):** выписаны (H1$_\Pi$)/(H2$_\Pi$) как $\forall\Pi^b_1$-формулы и отмечены скрытые усиления (a.e.-твёрдость и фиксированный $R$); см. `docs/15_proof_complexity.md`.
- [x] **Q3 (минимальный нерелятивизирующий шаг):** добавлена лемма 15.7.3 (PIT-аксиомы ⇒ EF p-симулирует IPS) с эскизом и барьер-чеком; см. `docs/15_proof_complexity.md`.
- [x] **Q3a (PIT ⇒ IPS/EF):** в Лемме 15.7.3c добавлен явный линейный подсчёт размера редукции CNF→3‑CNF (≤$L$ клауз и ≤$3L$ литералов для $L$ литералов исходной CNF); см. также `docs/research/16_encodings.md` §16.78.
- [x] **Q4 (канонизация/ROABP-барьер):** добавлена лемма 15.7.4 (слабый барьер для CNF-класса); см. `docs/15_proof_complexity.md`.
- [x] **Q2a (EF+assumptions ⇒ P≠NP):** добавлено замечание рядом с Леммой 15.7.2b: квантор $C\le m(s)$ — это лишь bounded‑ограничение длины кода (паддинг), все содержательные ограничения идут через $\mathrm{Valid}_s(C)$; см. также `docs/research/16_encodings.md` §16.79.
- [x] **Q1a (Pich–Santhanam 2023):** связана оценка размера счётчика из Леммы 15.7.1d с 3‑CNF‑кодированием через Tseitin: добавлена ремарка рядом с 15.7.1d и формализованный шаг `docs/research/16_encodings.md` §16.80.
