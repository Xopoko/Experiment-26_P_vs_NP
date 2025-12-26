# Открытые вопросы (рабочая очередь)

Правило: **каждый прогон агента выбирает ровно 1 пункт ниже** и делает измеримый прогресс:
`Proof` / `Counterexample` / `Exact citation` / `Toy` / `Reduction` / `Barrier` + барьер‑чек.
Затем обновляет пункт.

## Активные

- [ ] **Q39 (Tseitin(Grid): depth‑gap для polynomial‑size в bounded‑depth Frege):**
  - `Priority:` P1
  - `Status:` ACTIVE (open confirmed)
  - `LastStepID:` Q39.S13-2k-block-cut-invariant (см. `docs/research/16_tseitin_q39.md` §16.159)
  - `NextStepID:` Q39.S14-2k-projection-rank-obstruction
  - `Success:` либо явный upper на глубине $O(\\log N/\\log\\log N)$, либо барьер/контрпример для “XOR‑step” в bounded‑depth Frege
  Известно: $d_{\\mathrm{poly}}(N)\\ge\\Omega(\\log N/\\log\\log N)$ (Håstad’20, Cor. 6.6; §16.92) и $d_{\\mathrm{poly}}(N)\\le O(\\log N)$ (unpack GIRS’19/Claim 28; §16.115–§16.121).
  Узел: синтаксически симулировать шаг Gaussian elimination в bounded‑depth Frege (HR’22 отмечают как “не умеем”; §16.122).
  Прогресс: исправлено: Thm. 6.5 сам по себе **не** запрещает polynomial‑size на критической глубине $d=\\Theta(\\log n/\\log\\log n)$ (даёт лишь $\\exp(\\Omega(\\log^{\\Theta(1)}n))=n^{o(1)}$); значит нельзя “выбить” poly XOR‑step на этом $d$ одним LB‑аргументом — нужно находить структурно вынужденный base‑change/тяжёлый шаг. См. `docs/research/16_tseitin_local_ef.md` §16.187. `InfoGain:` 1.
  Добавлено: toy‑инвариант для фиксированного 2×2 row‑разбиения на $S_2$ показывает, что шаг $t\\to t+1$ в column‑summing ломает совместимость уже на $4\\times4$ (пересечение $S_2$ имеет нечётность 1), т.е. base‑change неизбежен. См. `docs/research/16_tseitin_q39.md` §16.153. `InfoGain:` 1.
  Доказано: для любого $n$ и фиксированного 2‑строчного разбиения $S_j$ нечётный префикс $R_{j,t}$ даёт
  $|S_j\\cap\\delta(R_{j,t})|=t$ нечётно, значит уравнение несовместимо с разбиением и нужен base‑change.
  См. `docs/research/16_tseitin_q39.md` §16.154. `InfoGain:` 1.
  Контрпример: even‑batching $t\\to t+2$ не спасает фиксированное 2‑строчное разбиение —
  вывод $E(\\delta(B_{1,2}))$ из двух вершинных уравнений требует несовместимой промежуточной строки.
  См. `docs/research/16_tseitin_q39.md` §16.155. `InfoGain:` 1.
  Toy‑тест: XOR‑дерево вывода $\\delta(B_{1,2})$ на 4×4 неизбежно содержит вершину с
  $|S_2\\cap\\mathrm{supp}|=1$ (проекция на $B_{\\mathrm{top}}$ в $\\mathbb F_2^2$),
  значит несовместимая строка неизбежна. См. `docs/research/16_tseitin_q39.md` §16.156. `InfoGain:` 1.
  Доказано: для любого $n,j,t$ любой XOR‑вывод $\\delta(B_{t+1,t+2})$ из вершинных уравнений
  содержит вершину с пересечением $\\{e_{t+1},e_{t+2}\\}$ ровно в одном ребре (проекция 10/01),
  т.е. фиксированный 2‑строчный блок разрезается. См. `docs/research/16_tseitin_q39.md` §16.157.
  `InfoGain:` 1.
  Контрпример (toy, $k=2$): в 6×6 при разбиении $S_j$ на пары $\\{e_1,e_2\\},\\{e_3,e_4\\},\\{e_5,e_6\\}$
  строка $E(\\delta(B_{3..6}),\\bigoplus_{i=3}^6\\chi(i,j))$ совместима, но любое XOR‑дерево из
  вершинных уравнений содержит несовместимые листья (каждый $e_i$ требует вершину $(i,j)$).
  См. `docs/research/16_tseitin_q39.md` §16.158. `InfoGain:` 1.
  Контрпример (toy, $k=2$): существует XOR‑дерево, где все *внутренние* узлы $\\pi$‑совместимы
  (группировка листьев внутри блоков $\\{e_3,e_4\\}$ и $\\{e_5,e_6\\}$), поэтому
  блок‑cut‑инвариант для внутренних узлов неверен. См. `docs/research/16_tseitin_q39.md` §16.159.
  `InfoGain:` 1.
  `Барьер‑чек:` r — применимо, NP — неприменимо, alg — неприменимо.
  Следующий шаг: проверить ранговую/проекционную обструкцию для even‑batching по $2k$ строкам:
  может ли существовать XOR‑дерево, где все внутренние узлы $\\pi$‑совместимы при фиксированном
  2‑строчном разбиении (Q39.S13).

- [ ] **Q43 (flat local‑EF(s): существуют ли “малые” evaluations для poly‑size доказательств?):**
  - `Priority:` P0
  - `Status:` ACTIVE
  - `LastStepID:` Q43.S130-explicit-a-constant (см. `docs/research/16_tseitin_local_ef.md` §16.273)
  - `NextStepID:` Q43.S131-compare-n0-a
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
  (xxvi) локальный arXiv‑срез: нет прямых совпадений по “common partial decision tree”/“multi‑switching”;
  найден HR’22 и общий обзор по switching lemma, но не “a‑sum trick” (§16.218). `InfoGain:` 1.
  (xxvii) toy‑подсчёт: при $|S^{*}_g|=3$ (две chosen + одна non‑chosen), $s=2$, $\\ell=5$
  константных бит ≤ 49, что ≤ $18|S^{*}_g|$ (§16.219). `InfoGain:` 1.
  (xxviii) доказано: associated center, попавший в $\\mathrm{supp}(J_j)\\setminus S^{*}_{j-1}$, становится
  disappearing center ровно один раз (Lemma 6.7 + Def. 6.2), поэтому `discover=1` читается ≤1 раз на центр,
  а число таких битов ≤ $|S^{*}_g|$ (§16.220). `InfoGain:` 1.
  (xxix) доказано: в Algorithm 3 число константных бит (known/recover/cc) ≤ $13|S^{*}_g|$,
  т.к. у chosen‑центра есть соседний chosen‑центр (Lemma 6.5) и в `RecoverExposed/RecoverNonExposed`
  остаётся ≤3 направления, а Lemma 6.7 + монотонность $S$ дают отсутствие повторов (§16.221).
  `InfoGain:` 1.
  (xxx) доказано: в Algorithm 2 ровно один бит `discover=0` на стадию, а число стадий $g\\le |S^{*}_g|$,
  поэтому вклад `discover=0` ≤ $|S^{*}_g|$ (§16.222). `InfoGain:` 1.
  (xxxi) доказано: Algorithm 4 (RecoverK) не читает биты из $X$, поэтому вклад в константные биты
  равен $0$ и $\\le C|S^{*}_g|$ при $C=1$ (§16.223). `InfoGain:` 1.
  (xxxii) доказано: суммирование вкладов Algorithms 2–4 и подписей даёт явный bound
  $24|S^{*}_g|$; если подписи $9|S^{*}_g|$ учитывать отдельно, то $A_1\\le 15$ (§16.224).
  `InfoGain:` 1.
  (xxxiii) доказано: структура $J_j$ и $I^{*}_{-}$ кодируется ≤2 битами на направление,
  поэтому можно взять $A_2\\le 16$ (§16.225). `InfoGain:` 1.
  (xxxiv) контрпример: подписи фиксируют $J_j$, но не структуру $I_j$; на 2x2 блоке
  chosen‑центров существуют два закрытых $I_j$ (горизонтальный/вертикальный matching) с
  одинаковой поддержкой и подписями, значит $A_2=0$ не следует (§16.226). `InfoGain:` 1.
  (xxxv) доказано: для фиксированного support замкнутые $I_j$ отвечают нечётностепенным
  подграфам $G$; множество решений имеет размер $2^{\\beta(G)}$, а на лесу $I_j$ единственен
  (1 бит на независимый цикл) (§16.227). `InfoGain:` 1.
  (xxxvi) доказано: для каждой π‑компоненты $P$ паритет mixed‑edges инцидентных $P$
  равен $|P|$ по модулю 2; в частности, один mixed‑edge на π‑звезде невозможен, а два —
  совместимы (§16.264). `InfoGain:` 1.
  (xxxvi) доказано: для графа возможных рёбер $G$ можно канонически выбрать остов $F(G)$
  и базовый odd‑подграф $E_0\\subseteq F(G)$, так что $E(I)=E_0\\oplus\\bigoplus b_e C_e$, а биты
  хорд хранятся по направлениям с ≤4 битами на центр (§16.228). `InfoGain:` 1.
  (xxxvii) доказано: подпись можно расширить на ≤4 chord‑бита на центр, конфликт‑чек использует
  9‑битный префикс, а восстановление $I_j$ читает новые биты; логика Algorithms 2–4 не меняется
  (§16.229). `InfoGain:` 1.
  (xxxviii) контрпример: правило назначения chord‑битов через лексикографический BFS‑остов
  зависит от глобальной нумерации; на 2×2 блоке два симметричных центра получают разные
  chord‑биты при одинаковой локальной структуре (с точностью до симметрии), так что
  расширенная подпись не инвариантна (§16.230). `InfoGain:` 1.
  (xxxix) toy‑тест: локальное правило назначения chord‑битов через порядок направлений
  (South/West‑end) инвариантно при переносах 2×2 и 2×3, не меняет конфликт‑чек (зависит
  только от 9‑битного префикса подписи), но требует проверки допустимости фиксированной
  ориентации (§16.231). `InfoGain:` 1.
  (xl) доказано: фиксированная ориентация grid уже используется в Def. 6.11 (направления в
  подписи), поэтому South/West‑правило не добавляет identity‑бит; повороты/отражения не
  сохраняют direction‑биты и не являются допустимой симметрией (§16.232). `InfoGain:` 1.
  (xli) точная цитата: HR’22 явно фиксируют grid координатами (i, j) ∈ [n], используют
  направления left/right/up/down и “lowest numbered row” для выбора центров, т.е. ориентация
  и нумерация строк/столбцов — часть модели (§16.233). `InfoGain:` 1.
  (xlii) контрпример: в ориентационно‑свободной модели один 9‑битный signature центра
  не фиксирует ориентацию (крест из 5 центров, поворот 180° сохраняет подпись),
  значит канонизация из одной подписи невозможна (§16.234). `InfoGain:` 1.
  (xliii) контрпример: если глобальный chirality‑бит $\\chi$ инвариантен относительно автоморфизмов
  (identity‑free), то на «кресте» и 2×2 блоке поворот 180° сохраняет подписи и $\\chi$,
  значит одного бита недостаточно (§16.235). `InfoGain:` 1.
  (xliv) доказано: внешний non‑invariant advice‑бит ориентации $\\chi$ совместим с Remark 6.12,
  используется Algorithms 2–4 как глобальный параметр с добавкой $O(1)$ бит, и signature+$\\chi$
  фиксирует ориентацию (toy: крест/2×2) (§16.236). `InfoGain:` 1.
  (xlv) доказано: D4‑симметричный support (крест) даёт мультимножество подписей, инвариантное
  под всеми 8 симметриями, поэтому identity‑free канонизация требует ≥3 глобальных бит
  (информационный lower bound; §16.237). `InfoGain:` 1.
  (xlvi) доказано: 3‑битный global advice‑код $\\omega\\in\\{0,1\\}^3$ кодирует элемент $D_4$ и
  задаёт ориентацию; Algorithms 2–4 читают $\\omega$ один раз, подписи остаются 9‑битными,
  конфликт‑чек Definition 6.13 не меняется; toy: крест/2×2/2×3 (§16.238). `InfoGain:` 1.
  (xlvii) toy‑проверка: «крест» из §16.237 с подписью $(1;1111;1111)$ не локально согласован,
  т.к. при info=1111 число рёбер должно быть нечётным; значит эта D4‑симметричная конструкция
  не является допустимым $J_j$ (Def. 6.2) (§16.239). `InfoGain:` 1.
  (xlviii) доказано: closed‑support с D4‑симметрией и фикс‑центром невозможен, т.к. odd‑degree
  $\\Rightarrow |\\mathrm{supp}|$ чётно, а D4 с фикс‑центром даёт $|\\mathrm{supp}|$ нечётно (§16.240).
  `InfoGain:` 1.
  (xlix) контрпример: D4‑квотиент с орбитными переменными описывает только D4‑инвариантные $I$;
  на 4×4 support=центральный 2×2 блок допускает odd‑degree matching, но в D4‑квотиенте
  единственная орбита рёбер даёт чётные степени и система $\\deg\\equiv 1$ несовместна (§16.241).
  `InfoGain:` 1.
  (l) toy‑конструкция: на 6×6 орбита $D_4$ точки $(2,3)$ (8 центров вне диагоналей)
  поддерживает odd‑degree matching (4 ребра), поэтому существует closed information set
  на orbit‑8‑only support; см. §16.242. `InfoGain:` 1.
  (li) контрпример: на orbit‑8 support существует локально согласованный $J_j$
  (4 непересекающихся ребра + non‑edges), удовлетворяющий Def. 6.2(1,4) и запрету
  chosen–non‑chosen; значит локальной обструкции нет. См. §16.243. `InfoGain:` 1.
  (lii) toy‑тест: 2‑стадийный фрагмент с orbit‑8 и $J_j$ из §16.243 совместим с Def. 6.2(3)
  и Def. 6.13(2) (конфликт не возникает); см. §16.244. `InfoGain:` 1.
  (liii) toy‑подсчёт: для all‑non‑chosen и pairing $\\pi=E$ глобальный mod‑2 чек
  сводится к $A x=\\mathbf 1$ по 4 рёбрам $E$, и система совместна с единственным
  решением $x_e=1$; конфликт Definition 6.13(2) не возникает. См. §16.245. `InfoGain:` 1.
  (liv) toy‑проверка: при mixed chosen $(2,3),(5,4)$ на orbit‑8 и рёбрах $E$ из §16.242
  mod‑2 система совпадает с all‑non‑chosen и совместна ($x_e=1$); конфликт Def. 6.13(2)
  не возникает. Замечание: в таком $J$ есть chosen–non‑chosen edges, что запрещено
  Def. 6.2(4). См. §16.246. `InfoGain:` 1.
  (lv) toy‑проверка: при chosen центрах $(2,3),(5,4)$ запрет chosen–non‑chosen edges означает
  $x_{e_1}=x_{e_4}=0$, что противоречит $A x=\\mathbf 1$ из §16.245 (требует $x_{e_1}=x_{e_4}=1$);
  значит mod‑2 конфликт возникает. См. §16.247. `InfoGain:` 1.
  (lvi) toy‑проверка: при adjacent chosen центрах $(2,3),(2,4)$ и $J$ с рёбрами $E$ из §16.242
  (без chosen–non‑chosen рёбер) mod‑2 система $A x=\\mathbf 1$ даёт $x_1=x_2=x_3=x_4=1$ и
  совместна; конфликт Def. 6.13(2) не возникает. См. §16.248. `InfoGain:` 1.
  (lvii) точная цитата: Def. 5.6/6.2 допускают edges между adjacent chosen и запрещают только
  chosen–non‑chosen; Lemma 6.5 требует adjacency между chosen в $\\mathrm{supp}(J)$, а Def. 6.11
  не накладывает ограничений на adjacency. Следовательно, конфигурация §16.248 допустима
  на уровне определений. См. §16.249. `InfoGain:` 1.
  (lviii) toy‑пример: на 4×4 support из двух adjacent chosen центров можно выбрать
  $(\\rho,I,S,\\pi,\\psi)$ так, что $J$ закрыт на этих центрах, удовлетворяет Def. 6.2(1–4),
  минимален по Def. 5.9 и не содержит chosen–non‑chosen edges. См. §16.250. `InfoGain:` 1.
  (lix) контрпример: глобальные ограничения на $S/I/\\pi$ не дают min‑degree≥2 — при
  $S=I=\\pi=\\varnothing$ и $J$ из §16.250 степени 1 у chosen, а минимальность следует
  из Def. 5.9. См. §16.251. `InfoGain:` 1.
  (lx) toy‑проверка: для support из двух adjacent chosen (§16.250) mod‑2 система на единственном
  ребре $e$ даёт $x_e=1$, поэтому closed information set единственен и линейной неоднозначности
  $I/\\pi$ нет. См. §16.252. `InfoGain:` 1.
  (lxi) toy‑проверка: 2×2 chosen‑цикл на 4×4 допускает possible forcing info $J$ (Def. 6.2),
  а closed information sets на этом support ровно два (H/V matching), и оба проходят
  Def. 6.13(2); остаётся 1‑бит неоднозначности. См. §16.253. `InfoGain:` 1.
  (lxii) доказано: в каноническом режиме (Invariant 6.1(4) + запрет chosen–non‑chosen edges)
  pairing $\\pi$ фиксирует non‑chosen часть, а неоднозначность closed $I$ целиком равна
  $2^{\\beta(G_{\\mathrm{ch}})}$; стягивание $\\pi$ не меняет цикл‑пространство выбранной части.
  См. §16.254. `InfoGain:` 1.
  (lxiii) toy‑проверка: 2×2 chosen‑цикл + π‑компонента из двух non‑chosen центров (без
  chosen–non‑chosen edges) даёт совместную mod‑2 систему и два closed $I$; минимального
  контрпримера к Def. 6.2(4) нет при $\\beta(G/\\pi)=1$. См. §16.255. `InfoGain:` 1.
  (lxiv) toy‑проверка: нечётная non‑chosen π‑компонента даёт паритетный конфликт в системе
  $A x=\\mathbf 1$, поэтому closed $I$ не существует; однако по Def. 5.2 компоненты π имеют
  размер 2 или 4 и такой случай не реализуется. См. §16.256. `InfoGain:` 1.
  (l) toy‑тест: 2×2 chosen‑цикл + две disjoint π‑компоненты размера 2 дают совместную
  mod‑2 систему; две non‑chosen компоненты фиксируют $f_1=f_2=1$, а chosen‑часть имеет 2 решения,
  поэтому $\\beta(G/\\pi)=1$ не исключает closed $I$ (§16.257). `InfoGain:` 1.
  (lxv) toy‑тест: 2×2 chosen‑цикл + π‑компонента‑ребро (|P|=2) + π‑компонента‑звезда (|P|=4)
  при запрете chosen–non‑chosen edges даёт совместную $A x=\\mathbf 1$; non‑chosen часть фиксирована,
  число closed $I$ равно $2^{\\beta(G_{\\mathrm{ch}})}=2$ (§16.258). `InfoGain:` 1.
  (lxvi) toy‑тест: 2×2 chosen‑цикл + две disjoint π‑звезды размера 4 при запрете chosen–non‑chosen
  edges дают совместную $A x=\\mathbf 1$; non‑chosen часть фиксирована, число closed $I$ остаётся
  $2^{\\beta(G_{\\mathrm{ch}})}=2$, обструкция не возникает (§16.259). `InfoGain:` 1.
  (lxvii) toy‑поиск: для двух disjoint π‑звёзд размера 4 без chosen–non‑chosen рёбер
  $\\beta(G/\\pi)=0$, и во всех размещениях на 4×4/5×5 система $A x=\\mathbf 1$ совместна
  (0 контрпримеров из 68 и 564 пар); см. §16.260. `InfoGain:` 1.
  (lxviii) контрпример: две π‑звезды с общим центром (overlap) дают несовместность
  $A x=\\mathbf 1$, хотя наивный паритетный тест “каждая π‑звезда чётна” проходит;
  см. §16.262. `InfoGain:` 1.
  (lxix) доказано: в каноническом режиме система $A x=\\mathbf 1$ эквивалентна
  $B_{G/\\pi}x=\\mathbf 1$, и совместимость сводится к чётности размеров компонент $G/\\pi$
  (эквивалентно $b\\perp\\ker B_{G/\\pi}^T$); критерий согласуется со всеми toy‑случаями
  §16.252–§16.260. См. §16.261. `InfoGain:` 1.
  (lxx) контрпример: одна non‑chosen π‑звезда размера 4 и ровно один chosen–non‑chosen edge
  на 4×4 дают несовместность $A x=\\mathbf 1$, хотя $G/\\pi$ имеет чётную компоненту;
  см. §16.263. `InfoGain:` 1.
  (lxxi) контрпример: π‑звезда размера 4 с двумя mixed‑edges к одному chosen‑центру даёт
  несовместность $A x=\\mathbf 1$, хотя $\\delta_{\\mathrm{mix}}(P)$ чётно; см. §16.265.
  `InfoGain:` 1.
  (lxxii) toy‑проверка: в §16.265 после стягивания π‑компоненты и сохранения chosen‑вершины
  получаем $b_{\\mathrm{mix}}=(1,0)$ и $\\ker B_{G/\\pi}^T=\\langle(1,1)\\rangle$, поэтому
  $b_{\\mathrm{mix}}\\not\\perp\\ker B_{G/\\pi}^T$ и критерий отсекает конфигурацию; см. §16.266.
  `InfoGain:` 1.
  (lxxiii) доказано: в каноническом режиме совместимость $A x=\\mathbf 1$ эквивалентна
  существованию решения $B_{G/\\pi}x=b_{\\mathrm{mix}}$, а любое квотиент‑решение
  расширяется на внутренние рёбра π‑компонент (суммирование даёт единственное условие
  $\\delta_{\\mathrm{mix}}(P)\\equiv|P|\\pmod 2$); см. §16.267. `InfoGain:` 1.
  (lxxiv) toy‑тест: две disjoint π‑звезды размера 4 и один extra non‑chosen edge
  между компонентами дают $A x=\\mathbf 1$ только при $e=0$; ровно то же условие
  даёт $B_{G/\\pi}x=b_{\\mathrm{mix}}$ (b=0 на обеих компонентах). См. §16.268.
  `InfoGain:` 1.
  (lxxv) toy‑тест: треугольник в $G/\\pi$ (two π‑звезды + chosen‑центр + extra nn‑ребро)
  даёт $A x=\\mathbf 1$ несовместной уже на квотиентном уровне: из вершинных
  уравнений следует $m_P=m_Q=e$, а $m_P+m_Q=1$ противоречит; то же даёт
  $B_{G/\\pi}x=b_{\\mathrm{mix}}$. См. §16.269. `InfoGain:` 1.
  (lxxvi) контрпример (toy): 4‑цикл в $G/\\pi$ из non‑chosen π‑компонент размера 2
  допускает ненулевое присваивание nn‑рёбер $e_i$ (уравнения дают $e_{i-1}=e_i$),
  значит решение с $e_i=1$ существует; см. §16.270. `InfoGain:` 1.
  (lxxvii) доказано: в каноническом режиме nn‑рёбра между разными π‑компонентами запрещены
  (Invariant 6.1(4) + Def. 6.2(4)), поэтому цикл из non‑chosen компонент не реализуется на grid;
  см. §16.271. `InfoGain:` 1.
  (lxxviii) exact citation: явный $A_1$ уже получен в §16.224 (сумма вкладов Algorithms 2–4),
  поэтому $A_1^{\\mathrm{tot}}=24$, а при отдельном учёте подписей $A_1\\le 15$; см. §16.272.
  `InfoGain:` 1.
  (lxxix) доказано: при $A_1^{\\mathrm{tot}}=24$, $A_2\\le 16$, $A_3\\le 69/4$ и
  $A_4\\le 65/4$ можно взять $A\\le 668$ в Lemma 6.9/4.2; см. §16.273. `InfoGain:` 1.
  `Барьер‑чек:` r — применимо, NP — неприменимо, alg — неприменимо.
  Следующий шаг: сравнить условия $n\\ge n_0(A)$ и $n\\ge 20 C n'\\log n'$ при $A=668$
  и зафиксировать доминирующее ограничение (Q43.S131-compare-n0-a).

## Завершённые (архив)

- [x] **Q42 (flat local‑EF(s): перенос HR t‑evaluation → Lemma 2.13):**
  закрыто: введено cost‑$t$ evaluation для flat local‑EF(s) и показано, что HR Lemma 2.13 переносится с заменой параметра глубины на стоимость (порог $t\\le\\Theta(n/s)$); см. `docs/research/16_tseitin_local_ef.md` §16.162. `StepID:` Q42.S1-define-evaluation-flat. `InfoGain:` 2.
- [x] **Q41 (если Q39 открыт: локальные расширения):**
  закрыто: (i) контрпример показывает, что “nested extension” без разворачивания поддержки делает local‑EF(s) тривиальной (§16.160);
  (ii) в flat‑модели доказан аналог HR Cor. 2.7 при $\\mathrm{supp}_s/\\mathrm{cost}_s$ (§16.161). `StepID:` Q41.S3-proof-cor27-analogue-flat. `InfoGain:` 2.
- [x] **Q40 (литературный статус Q39):**
  закрыто: в Håstad–Risse’22 §1.2 зафиксирована точная цитата “We do not know how to syntactically translate a Gaussian elimination step …”, со страницей (p. 4; PDF p. 6); см. `docs/research/16_tseitin_q39.md` §16.122. `StepID:` Q40.S1-quote-hr22-1.2. `InfoGain:` 1.
- [x] **Q38 (константы в depth‑threshold для Tseitin(Grid): сравнить Håstad’20 и GIRS’19):**
  закрыто: после пересчёта (§16.117+§16.120) сравнение «59 vs верхняя константа» оказалось некорректной целью: известный polynomial‑size upper на grid имеет масштаб $O(\\log n)$, а не $\\Theta(\\log n/\\log\\log n)$.
- [x] **Q37 (вынести в основной текст краткий итог по Tseitin(Grid) — текущие границы):**
  закрыто: в `docs/15_proof_complexity.md` теперь стоит корректная формулировка
  $\\Omega(\\log N/\\log\\log N)\\le d_{\\mathrm{poly}}(N)\\le O(\\log N)$; детали: §16.92+§16.115+§16.116+§16.120.
- [x] **Q36 (свести глубину $d$ из GIRS’19 Thm. 19 к глубине в 16.92/16.97 и переписать в терминах $N$):**
  закрыто: перезапись в терминах $N$ сделана в `docs/research/16_tseitin_core.md` §16.116 (и поправлена: tight‑утверждение снято).
- [x] **Q35 (квантифицировать верхнюю оценку Thm. 19 (GIRS’19) и сравнить с 16.92):**
  закрыто: в `docs/research/16_tseitin_core.md` §16.115+§16.120 выписан явный upper $\\mathrm{poly}(|T|)\\cdot 2^{O(d\\cdot X^{2/d})}$ из Claim 28,
  и показано, что он гарантирует polynomial‑size лишь при $d=\\Theta(\\log n)$ (а при $\\Theta(\\log n/\\log\\log n)$ — только quasi‑poly).
- [x] **Q34 (явная конструкция $O(\\log n)$‑depth Frege‑рефутации Tseitin в стандартном языке):**
  закрыто: в `docs/research/16_tseitin_core.md` §16.93 выписан самодостаточный вывод через Urquhart’87 (16.91) + Spira‑балансировку (16.94)
  + line‑replacement (16.113) + p‑доказательства эквивалентности балансировки (16.114).
- [x] **Q33 (Spira‑балансировка: где взять p‑размерный Frege‑вывод $A\\leftrightarrow A'$?):**
  закрыто: Buss’97, Proof (Sketch) к Thm. 3 (p. 8) прямо отмечает наличие polynomial‑size Frege‑доказательств,
  верифицирующих корректность Spira‑перевода (в частности, эквивалентности вида $A\\leftrightarrow A'$);
  это зафиксировано в `docs/research/16_tseitin_core.md` §16.114, и 16.94 теперь строгая через §16.113.
- [x] **Q32 (закрыть «техническую» часть 16.94: балансировка линий в Frege):**
  закрыто: схема «из $A$ и $A\\leftrightarrow A'$ выводить $A'$» и оценка blow‑up записаны в `docs/research/16_tseitin_core.md` §16.113;
  статус шага 16.94 обновлён на «доказано».
- [x] **Q31 (перепривязать §16.110 к §16.112 и убрать неформальность):**
  закрыто: в §16.110 заменено $\\log n\\le\\log S$ на ссылку «см. §16.112» и проверено, что других мест использования $n\\le S$ нет
  (дальше используется только $\\log n\\le\\log S$ через §16.112).
- [x] **Q30 (обосновать шаг $\\log n\\le\\log S$ для Tseitin: $S\\ge |V(G)|$):**
  закрыто: для связного $G$ удаление любого блока $\\mathrm{PARITY}_{v,\\sigma(v)}$ делает $T(G,\\sigma)$ выполнимой (явная конструкция по остовному дереву),
  значит любая резолюционная рефутация использует хотя бы одну исходную клаузу из каждого блока и $S\\ge |V(G)|$; см. `docs/research/16_tseitin_core.md` §16.112.
- [x] **Q29 (свести AR’11 (2.15/2.17/2.18) в одну «употребимую» ремарку):**
  закрыто: сводка с явными ссылками и константами записана в `docs/research/16_tseitin_core.md` §16.111.
- [x] **Q28 (AR’11 Thm. 2.17: явная зависимость в $\\bigl(\\tilde\\ell(G)\\log S\\bigr)^{O(\\tilde\\ell(G)^2)}$):**
  закрыто: из доказательства Thm. 2.17 можно извлечь явную грубую константу $c=6$ в
  $W\\le (C\\,\\tilde\\ell(G)\\log S)^{c\\tilde\\ell(G)^2}$; см. `docs/research/16_tseitin_core.md` §16.110.
- [x] **Q27 (AR’11 Thm. 2.15: явная степень в $\\ell(G)^{O(1)}$):**
  закрыто: из (5.4) и (5.6) в доказательстве AR’11 Thm. 2.15 следует $W\\le O(\\ell(G)^7\\log S)$; см. `docs/research/16_tseitin_core.md` §16.109.
- [x] **Q26 (AR’11: планарные графы с ограниченной степенью граней ⇒ ограниченная cyclicity $\\ell(G)$):**
  закрыто: если $G$ 2‑реберно‑связен и допускает плоское вложение, где каждая грань имеет степень $\\le d$,
  то границы граней дают покрытие рёбер циклами длины $\\le d$ и кратности $\\le 2$, значит $\\ell(G)\\le\\max\\{d,2\\}$; см. `docs/research/16_tseitin_core.md` §16.108.
- [x] **Q25 (Tseitin: $W(T(G,\\sigma)\\vdash\\bot)$ через $\\mathrm{cw}(G)$):**
  закрыто: из $\\tfrac18\\,\\mathrm{wb}(H_T)\\le W\\le 2\\,\\mathrm{wb}(H_T)$ (AR’11, Thm. 2.12 + §4) и
  $\\mathrm{wb}(H_T)=\\mathrm{wb}(G^*)=\\mathrm{cw}(G)$ (Remark 2.11 + §16.105–16.106) получаем
  $\\mathrm{cw}(G)/8\\le W(T(G,\\sigma)\\vdash\\bot)\\le 2\\,\\mathrm{cw}(G)$; см. `docs/research/16_tseitin_core.md` §16.107.
- [x] **Q24 (повторы гиперрёбер vs $\\mathrm{wb}$ в AR’11 Remark 2.11):**
  закрыто: в AR’11 гиперграф $H_{T(G,\\sigma)}$ — это мульти‑$G^*$ (Def. 2.1 допускает multiset), где $E(v)$ повторяется $2^{\\deg(v)-1}$ раз (Remark 2.11),
  и для $G^*$ такие повторы не меняют $\\mathrm{wb}$; см. `docs/research/16_tseitin_core.md` §16.106.
- [x] **Q23 (branch‑width $G^*$ vs carving width $\\mathrm{cw}(G)$):**
  закрыто: для двойственного гиперграфа $G^*$ (гиперрёбра — звёзды $E(v)$) branch‑decomposition по гиперрёбрам эквивалентна carving‑декомпозиции $G$ по вершинам,
  и $\\mathrm{wb}(G^*)=\\mathrm{cw}(G)$; см. `docs/research/16_tseitin_core.md` §16.105.
- [x] **Q22 (константы в $\\Theta(\\cdot)$ из AR’11 Thm. 2.12):**
  закрыто: из AR’11 Prop. 4.3 и доказательства Lemma 4.4 (через Figure 3.1 / Lemma 3.1) получаем явные оценки
  $\\tfrac18\\,\\mathrm{wb}(T(G,\\sigma))\\le W(T(G,\\sigma)\\vdash\\bot)\\le 2\\,\\mathrm{wb}(T(G,\\sigma))$;
  см. `docs/research/16_tseitin_core.md` §16.104 и
  `../resources/downloads/alekhnovich_razborov_2011_satisfiability_branchwidth_tseitin.pdf`.
- [x] **Q21 (Tseitin‑width через branch‑width):**
  закрыто: Alekhnovich–Razborov (2011, Thm. 2.12) утверждают
  $\\mathrm{wb}(T(G,\\sigma))=\\Theta(W(T(G,\\sigma)\\vdash\\bot))$, а Remark 2.11 уточняет, что подлежащий гиперграф — это $G^*$ (с повторениями);
  см. `docs/research/16_tseitin_core.md` §16.103 и `../resources/downloads/alekhnovich_razborov_2011_satisfiability_branchwidth_tseitin.pdf`.
- [x] **Q20 (согласовать использование $w(G)$ в Cor. 34 / §16.98):**
  закрыто: в §16.98 добавлено явное определение $w(G):=W(T(G,\\varphi)\\vdash\\bot)-1$ и цепочка
  $n^{O(w(G))}=2^{O(\\mathrm{tw}(G)\\,\\Delta(G)\\log n)}$ через Harvey–Wood (2014, (2));
  см. `docs/research/16_tseitin_core.md` §16.102 и
  `../resources/downloads/harvey_wood_2014_treewidth_line_graphs.pdf`.
- [x] **Q19 (точная ссылка на $w(G)=\max\{\\Delta(G),\\mathrm{tw}(L(G))\\}-1$ для Tseitin‑width):**
  закрыто: Galesi–Talebanfard–Torán (2018, ECCC TR18‑170) дают Cor. 8:
  $W(T(G,\\varphi)\\vdash\\bot)=\\max\\{\\Delta(G),\\mathrm{ec}(G)-1\\}$ и Cor. 16:
  $\\mathrm{ec}(G)=\\mathrm{tw}(L(G))+1$, откуда $W=\\max\\{\\Delta(G),\\mathrm{tw}(L(G))\\}$ и $w(G)=W-1$.
  См. `docs/research/16_tseitin_core.md` §16.101 и `../resources/downloads/galesi_talebanfard_toran_2018_cops_robber_tseitin.pdf`.
- [x] **Q18 (связать carving width $W$ с $w(G)$ в Cor. 34):** закрыто: доказано $\\mathrm{cw}(G)\\le \\mathrm{tw}(L(G))+1$;
  вместе с формулой для Tseitin‑width $w(G)=\\max\\{\\Delta(G),\\mathrm{tw}(L(G))\\}-1$ (16.101) получаем
  $\\mathrm{cw}(G)\\le w(G)+2$ и можно переписывать $n^{O(\\mathrm{cw}(G))}$ как $n^{O(w(G))}$; см. `docs/research/16_tseitin_core.md` §16.100.
- [x] **Q17 (Cor. 34: зависимости и «где именно берётся» tree‑like Res ≤ n^{O(w)}):** закрыто:
  точная ссылка для tree‑like upper bound — Beame–Beck–Impagliazzo (2016), Lemma 61 (через carving width),
  см. `docs/research/16_tseitin_core.md` §16.99 и
  `../resources/downloads/beame_beck_impagliazzo_2016_time_space_tradeoffs_resolution.pdf`.
- [x] **Q16 (Tseitin: bounded‑depth Frege ↔ tree‑like Resolution):** закрыто: точная формулировка Cor. 34:
  bounded‑depth Frege‑доказательство размера $S$ ⇒ tree‑like Resolution размера $\\le 2^{\\mathrm{poly}(\\log S)}$
  (Galesi–Itsykson–Riazanov–Sofronova 2019, Cor. 34), см. `docs/research/16_tseitin_core.md` §16.98 и
  `../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`.
- [x] **Q15 (сузить разрыв depth‑vs‑size для Tseitin):**
  закрыто: зафиксированы Thm. 18/19 из GIRS’19 (2019, ECCC TR19‑069) как family bounds $2^{\\mathrm{tw}(G)^{\\Omega(1/d)}}$ и $2^{\\mathrm{tw}(G)^{O(1/d)}}\\cdot\\mathrm{poly}(|\\mathrm{Tseitin}(G,f)|)$
  (в исходной статье $d$ трактуется как фиксированная глубина; для растущего $d$ важна явная зависимость от $d$, см. §16.115–§16.121 и Q39).
  См. `docs/research/16_tseitin_core.md` §16.97 и `../resources/downloads/galesi_itsykson_riazanov_sofronova_2019_bounded_depth_frege_tseitin_all_graphs.pdf`.
- [x] **Q14 (Frege‑depth для Tseitin):** закрыто: poly‑size Frege‑рефутация (Urquhart 1987; §16.91),
  bounded‑depth lower bound на grid (Håstad 2020; §16.92), upper bound depth $O(\\log n)$ для bounded‑degree
  (Håstad 2020 remark + Buss 1997/Spira‑перевод; §16.93 и §16.95), и ссылка на формульную балансировку (Bonet–Buss 2002; §16.94).
- [x] **Q13 (Frege/EF симулирует XOR/Gauss):** в `docs/research/16_tseitin_core.md` §16.88 добавлена точная ссылка,
  что EF «легко симулирует Gaussian elimination» (Bonet–Buss–Pitassi 2002, `../resources/downloads/bonet_buss_pitassi_2002_hard_examples_frege.pdf`, p. 7),
  что закрывает фольклорность EF‑каркаса XOR‑суммирования.
- [x] **Q12 (TseitinCNF vs PC при $\\mathrm{char}(F)\\ne 2$):** в `docs/research/16_tseitin_core.md` §16.90
  показано: TseitinCNF (3‑CNF) и биномиальная Tseitin (Fourier/±1‑база) p‑эквивалентны по степени в PC при $\\mathrm{char}(F)\\ne 2$,
  поэтому degree/size‑LB (Razborov 2023, Thm. 6.8; Beame–Sabharwal 2000, Thm. 2.18) переносятся на TseitinCNF.
- [x] **Q11 (TseitinCNF vs PC над $\\mathbb F_2$):** в `docs/research/16_tseitin_core.md` §16.89
  дан явный PC‑вывод линейного уравнения вершины из 4 клауз и итоговая рефутация степени 3 и размера $O(|V|)$.
- [x] **Q10 (Tseitin vs EF/PC):** в `docs/research/16_tseitin_core.md` §16.88 зафиксировано: над полями нечётной/нулевой характеристики любая PC‑рефутация $\\mathrm{Tseitin}(G_n)$ для bounded‑degree экспандеров имеет степень $\\Omega(|V_n|)$ и, по связи degree→size, экспоненциальный размер (Razborov 2023, Thm. 6.8 + абзац после Thm. 6.9). Над $\\mathbb F_2$ степень 1 (сумма уравнений). Там же записан EF‑каркас: из 3‑CNF по вершинам выводятся XOR‑уравнения, их XOR‑сумма даёт $0=1$.
- [x] **Q9 (bounded‑occ Tseitin‑семейство):** в `docs/research/16_tseitin_core.md` §16.87 зафиксировано: явная 3‑регулярная expander family (см. `../resources/downloads/arora_barak.pdf`, §16.3, Remark 16.10) ⇒ $e(G)=\\Omega(|V|)$, а значит 3‑CNF Tseitin из §16.85 имеет bounded‑occ = 8 и резолюционный размер $\\exp(\\Omega(|V|))$ по §16.86.
- [x] **Q8 (Tseitin ⇒ резолюционные нижние оценки):** извлечено из `../resources/downloads/itsykson_oparin_2013_tseitin.pdf` (Cor. 1 + Thm. 1) и зафиксировано как формализованный шаг `docs/research/16_tseitin_core.md` §16.86: для $\\deg(G)\\le k$ имеем $W\\ge e(G)-1$ и $S\\ge \\exp((e(G)-k-1)^2/|E|)$, значит на bounded‑degree экспандерах резолюция экспоненциальна.
- [x] **Q7 (Tseitin как кандидат):** в `docs/research/16_tseitin_core.md` §16.85 задано определение XOR‑системы Tseitin($G,\\chi$), доказана невыполнимость при нечётной сумме зарядов (паритетный инвариант) и выписана явная 3‑CNF кодировка для 3‑регулярных графов (размер $4|V|$, bounded‑occ = 8).
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
