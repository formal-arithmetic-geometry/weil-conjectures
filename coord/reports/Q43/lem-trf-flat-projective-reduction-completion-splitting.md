# Repair report

## Repair of latest landing return 179bd4756c4 (2026-10-23)

The latest entry in coord/returns/Q43.md identifies head 179bd4756c4 and the same side-completion integration refusal. I continued the retained sandbox, preserving both statement-only jobs, their actual searches and all seven original arguments. The required initial dry run exited OK at db4e164dde9; deliver.py constructed its temporary delivery against the current server DAG. No git command was run in the shared repository. The final delivery will use this same supported rebase procedure after the changes described here.

I compared the retained parent against the current main DAG field by field: only proof, proof_deps and split_report differ. The current seven-step proof equals returned-proof.json exactly. The statement, statement dependencies, source, Lean record, blueprint ancestry, chapter, unit and maintainer metadata agree. Neither child exists in the current DAG. The released stage-1 repair order still explicitly requires at least two new statement-only jobs; the old reviewed split does not discharge it. There are no changed cited mathematical statements requiring replacement or new searches.

I re-read Stacks algebra.tex Tag 05D3 (lemma-split-completed-sequence) for the parent and both jobs, and Tag 05CG (lemma-lift-projective) for quotient projectivity. I opened the two child statements and all six existing algebra statements listed below, and re-read the saved search hits. Step 1 gets the exact quotient maps, their exactness, projective last terms and reduction squares from the first child; Step 2 uses the original surjection and those projective quotients in the second child; Step 3 uses precisely the compatibility equation asserted there; Step 4 uses the first child's injectivity, kernel-image equality and naturality. All four manifest quotations still contain the relevant claims verbatim. I expanded Step 4's first sentence into the coordinate argument that a completed kernel element has every coordinate zero. This is an actual proof-text adjustment in addition to the updated rebase report; the rest of the approved mathematical split remains intact.

The hypotheses remain arbitrary commutative R and ideal I, with no Noetherian, finite generation, completeness or separation restriction. The first child uses flatness of the last term for quotient exactness and the nilpotent image of I in R/I^n for projectivity. The second child's finite-sum correction uses surjectivity of v before applying projectivity at n+1; its compatibility statement is R-linear across the different quotient scalar rings. I checked I=0, I=R, the zero ring and zero modules, and the n=1 base case again. No statement correction or source dispute is needed. The two child workloads remain 1519 and 1627 characters of the preserved argument; the updated parent assembly has 1911 characters, with every step under 2000. The final dry run and push below verify the revised files, rather than merely re-pushing the returned head.

## Repair of current landing return 7c3f5932fbb (2026-10-22)

The current return in `coord/returns/Q43.md` identifies returned head `7c3f5932fbb` and asks for a rebase from the side completion onto the current DAG. I continued the retained delivery rather than starting over. The required initial dry run exited successfully at `1d814fbb92c`; this is an integration check, not a claim that the re-split has landed. The delivery tool fetches current `origin/sheaf-dag` and merges only the split-owned fields into its temporary delivery tree. I have run no git command in the shared read clone.

The current live parent and retained parent differ only in `proof`, `proof_deps` and `split_report`. Every live proof step is exactly the corresponding entry in `returned-proof.json`; there has been no intervening change to the statement, source, Lean record, blueprint ancestry, chapter, unit or maintainer review metadata. Neither child exists in the current DAG. The released stage-1 repair note still requires the two statement-only jobs and a short assembly. Thus the side completion is not being mistaken for a live completion or used to skip the outstanding work.

I re-read both child statements and the current six algebra input statements named in the earlier repair section. The parent's four citation uses still match the child statements verbatim, including commuting reductions in Step 4. No changed hypothesis, merged dependency or source discrepancy requires a replacement lemma. I adjusted Step 3 to display the coordinate equation proving that the assembled section preserves compatibility, instead of leaving this calculation implicit in the reference to Step 2. All other approved arguments and all real search evidence remain intact. This report and the split summary now identify the current returned head, separating this repair from the older ca5cac3fa79 attempt below.

The source review used Stacks `algebra.tex`, `lemma-split-completed-sequence` (05D3) and `lemma-lift-projective` (05CG). In the quotient job, flatness of the last term gives exactness after tensoring and quotient flatness; the image of I in R/I^n is nilpotent and its reduction is precisely M/IM. In the sections job, surjectivity of v gives the finite-sum correction inside the inverse-image submodule, and projectivity at level n+1 gives a linear section with the prescribed reduction. The parent uses neither an unproved inverse-limit exactness result nor extra finiteness assumptions. The cases I=0, I=R, the zero ring, zero modules and n=1 continue to satisfy the statements. No statement is disputed.

## Earlier repair of landing return ca5cac3fa79 (2026-10-22)

The current return is an integration refusal, after approval of the mathematics: the side completion had not been promoted to the live DAG used by the queue. I read the return in coord/returns/Q43.md and the current released stage-1 repair note. That note explicitly reopens the old reviewed split and requires two new jobs with a short assembly. It remains applicable; the historical reviewed record is not evidence that this re-split landed.

I compared every field of the retained parent with the current shared-repository parent. The only differences were the intended proof, proof_deps and split_report fields. In particular the statement, Lean record, source, unit, chapter, blueprint ancestry and historical review records agree. The current seven-step proof equals returned-proof.json exactly. Both new node ids remain absent from the current DAG. I retained the approved statements, their source citations, full historical argument, actual Mathlib search records and raw results. I read the saved search results rather than repeating unchanged questions.

The initial required dry run rebuilt this retained overlay on current origin/sheaf-dag and passed at 9337548bc49. The delivery tool fetches that branch and overlays only stage-1-owned fields, retaining current maintainer metadata; I ran no git command in the shared repository. The final delivery is rebuilt the same way after this report and split-summary repair. The two new jobs remain the substantive changes relative to current main, rather than an unchanged copy of its seven-step proof.

For the renewed citation audit I read both new statement-only node statements in full. Steps 1 and 4 use the first child's quotient exactness and commuting reductions, Steps 2 and 3 use the second child's compatible linear sections. I expanded the Step 4 manifest quote to include the commuting reduction equations, which that step uses along with injectivity and exactness. Each quotation is a literal substring of the relevant statement. I also re-read the current statements of def-weil-pbc-flat-ring-map, def-weil-pbc-projective-module, lem-weil-pbc-flat-quotient-tensor-injective, lem-weil-pbc-tensor-over-quotient-ring, lem-weil-pbc-flat-module-quotient-flat and lem-trf-local-nilpotent-projective-flat-lift. They supply exactly the flatness, projective lifting, tensor exactness, quotient identification, quotient flatness and nilpotent lift used in the preserved child workloads; none requires a new hypothesis or a change of route. No cited mathematical statement needed repair. The existing theorem still ends in sorry, so there is no attachment.

I re-read Stacks algebra.tex lemma-split-completed-sequence (05D3) and lemma-lift-projective (05CG), and the current blueprint chapter and unit text. I checked again the arbitrary-ideal and non-finite-module hypotheses, the inverse-image-submodule correction, scalar rings at adjacent levels, and the zero and unit ideal cases. The statements remain true, with no additional finiteness, Noetherian or completeness condition. The parent assembly has no step above 2000 characters and stays below 3000 characters in total.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-flat-projective-reduction-completion-splitting.json`: same statement, four-step assembly, split; inherited Mathlib searches retained.
- `dag/nodes/sec-trace-formula/lem-trf-adic-quotient-projective-short-exact.json`: statement, unsplit, no Mathlib match. Independent quotient exactness and nilpotent-projectivity argument, formerly Steps 1–2 (1519 characters).
- `dag/nodes/sec-trace-formula/lem-trf-adic-projective-compatible-sections.json`: statement, unsplit, no Mathlib match. Prescribed-section extension and induction, formerly Steps 3–5 (1627 characters).
- `citations.json`: one verbatim statement quotation per use in the four parent steps.
- `searches.jsonl` and search-result files: actual new searches, including unavailable LeanSearch answers; historical item searches remain in the item. `returned-proof.json` and `prior-report-Q25.md` preserve the current retained proof and earlier reviewed report.

Two new nodes, zero Mathlib leaves. Both new nodes have empty proof/proof_deps and null proof_origin, for separate workers to split; they do not depend on each other. The current parent proof has 1911 characters, under the 3000-character return limit. No proof step exceeds 2000 characters.

## Attachments

None. Read-only searches of `lean/WeilConjectures` and `lean/Sheaf` by the exact tag, declaration and completion/projective-reduction concepts found the item's theorem in `lean/Sheaf/SecTraceFormula/FlatProjectiveReductionCompletionSplitting.lean:44`, whose proof at line 60 is `sorry`; it is not an attachment. No project declaration states either new lemma completely with a finished proof. The other search hits concern derived complexes, sheaves or individual compatible elements.

## WANTED

None: the source and supporting algebra are available locally.

## Earlier work-spreading repair (retained history)

The return requires spreading a 4069-character proof into at least two comparable statement-only jobs while retaining the statement and a short assembly. I compared the empty retained sandbox with the live item, copied the live version, and read the earlier reviewed Q25 report. The two new jobs allocate all former Steps 1–5, without replacing the nilpotent lift or omitting the difficult surjectivity and compatibility arguments. Former Steps 6–7 remain written out in the parent as componentwise assembly. The exact old seven steps, with all their citations, are preserved below so the argument is not shortened or blurred. No statement error or source error was found. All non-split metadata, the Lean record and inherited blueprint ancestry are preserved.

## Not duplicates

lem-trf-adic-quotient-projective-short-exact vs lem-trf-flat-projective-reduction-completion-splitting: the new statement concerns finite quotient sequences and projectivity of each M_n, and has no completions or limit section; the parent assembles these with a separately proved compatible-section theorem.
lem-trf-adic-projective-compatible-sections vs lem-trf-flat-projective-reduction-completion-splitting: the new statement assumes projectivity at every positive level and extends a prescribed finite-level section, then gives a compatible family; it has no K, exactness hypothesis, flatness hypothesis or completion, and does not claim completed exactness.
lem-trf-adic-quotient-projective-short-exact vs lem-trf-completion-flat-mittag-leffler: the existing statement is flat Mittag-Leffler completion over a complete Noetherian ring, not projectivity and exactness of arbitrary finite quotients; its occurrence of 05D3 is only in the proof.
lem-trf-adic-projective-compatible-sections vs lem-trf-completion-flat-mittag-leffler: the existing statement gives properties of one completion over a complete Noetherian base, not extension of prescribed sections of an arbitrary module surjection.
lem-trf-adic-quotient-projective-short-exact vs lem-trf-local-nilpotent-projective-flat-lift: the existing lemma has one nilpotent ideal and proves projectivity of the entire flat module; the new lemma applies it over each R/I^n after establishing exactness and identifying the iterated quotients. I is not assumed nilpotent in the new lemma.
lem-trf-adic-projective-compatible-sections vs def-weil-pbc-projective-module: the definition supplies a single lift along a surjection; the new lemma must construct the inverse-image submodule, prove its surjectivity and enforce compatibility of successive lifts, so it is not an instance of the definition alone.

DAG searches covered the whole graph by tag 05D3, compatible section/splitting phrases and projective/adic quotient concepts, as well as titles to disambiguate geometric projectivity. Opened the existing nilpotent-projectivity, nilpotent-projective-module-lift, complete-base-projectivity, completion-flat-Mittag-Leffler and finite-perfect-tower nodes. None is a generalization specializing in one line to either new lemma. Whole-blueprint searches used `05D3`, `compatible sections`, `compatible splitting`, `projective reduction`, `projective quotients`, `projective modulo`, `sections modulo`, `short exact`, `adic` and `splittings`. No blueprint node states either new statement. `blueprint_refs.py ancestor` confirms lem-trf-local-term-locality; both children prepend the item to the inherited via list and identify their precise place in the supporting Tag 05D3 proof. The current main-20261015 chapter and unit texts were read; this algebraic supporting route does not replace their geometric arguments.

## Review by Q43

For the latest 179bd4756c4 return, I renewed the source and hypothesis checks against the current DAG, verified the saved old proof is identical to the current seven steps, and checked the four current citation uses literally. No cited statement changed. I made completed injectivity explicit coordinate by coordinate, updated the split summary and report to this return, and retained all approved statement-only workloads and honest searches. The latest repair section records the exact initial dry-run receipt and the comparison results.

For the current 7c3f5932fbb landing return, I repeated the field comparison and opened every cited statement. The current DAG still has the preserved seven-step proof and no child nodes. I made Step 3's compatibility calculation explicit, refreshed the returned-head identification, and retained the approved mathematical split and honest search records. The detailed hypothesis and source checks below were renewed against the current statements.

For this landing-return repair, I renewed the source and hypothesis review described above, compared the retained delivery with the current main node field by field, and checked all four citation uses against the actual child statements. The full Step 4 quotation now includes the reduction naturality equations; the approved mathematical split and all arguments are retained. The review below records the original work-spreading repair and remains valid against the statements I re-read.

I read Stacks `algebra.tex` Tag 05D3 (lemma-split-completed-sequence), including its omitted-surjectivity sentence, for the item and both new nodes, and Tag 05CG (lemma-lift-projective) for the projectivity argument allocated to the first child. I opened all five input statements of the old split, not just their titles. Tags 00HL, 00DF and 00HI are represented respectively by the existing tensor exactness, quotient-tensor and quotient-flatness nodes. The lifting-property equivalence is explicitly part of def-weil-pbc-projective-module. The preserved argument below specifies how these apply and every hypothesis required. These are intended inputs for the later workers, not proof dependencies smuggled into the new unsplit nodes.

Parent Step 1 cites lem-trf-adic-quotient-projective-short-exact. Its statement explicitly supplies injectivity of u_n, surjectivity of v_n, middle exactness, projectivity of M_n over the correct quotient ring A_n, and commutation with reductions. All hypotheses are exactly those of the unchanged parent, with no Noetherian, finiteness, separation, completeness or ideal-generation condition added. The quotient formulas ensure these are the maps defining the completion in the parent.

Parent Step 2 cites lem-trf-adic-projective-compatible-sections. The original v is surjective by hypothesis, and Step 1 supplies projectivity of every positive quotient. The child explicitly gives sections at all positive levels, with the displayed compatibility equation, not merely unrelated splittings. Its extension clause is for a given section and therefore records the actual induction workload. There is no appeal to a result about elementwise lifts to obtain a linear section.

Parent Step 3 cites the second child's compatible-family clause. It checks componentwise that s maps compatible families to compatible families, is R-linear, and has completed v as a left inverse. Step 4 cites the first child's exactness/injectivity clauses: unique levelwise kernel preimages are compatible because their two candidate reductions have the same image under injective u_n. Thus the parent writes out its image/kernel and injectivity calculation, without an uncited inverse-limit exactness theorem. The citation manifest quotes literal parts of the child statements for each of these four uses.

For the first child's underlying argument, tensor exactness uses flatness of the last module M, not flatness of the tensor factor R/I^n; quotient-flatness is applied with J=I^n. In A_n=R/I^n the image J_n of I satisfies J_n^n=0. The second-quotient identifications have kernels IM/I^nM and I/I^n, so projective reduction transports over the quotient ring isomorphism; then the nilpotent lifting node applies. For the second child, projectivity over A_{n+1} is used only after the map from the actual inverse-image submodule P/I^{n+1}P has been proved surjective by correcting a discrepancy in I^nM. The correction is not inferred to lie in I^nE without proof. Inclusion P into E induces the required quotient map even though that induced map need not be injective. Applying v_n to the representative of the lift proves the section-compatibility equation. These arguments remain explicitly preserved below.

I checked edge cases I=0 (constant quotients, projective M), I=R (all positive quotients and completions zero), R the zero ring, zero E or M, K=0, and n=1 with J_1=0. The statements impose no unneeded nonzero hypothesis, and both module and ring actions still make sense. In the second child v surjective implies all v_n surjective by taking representatives; flatness of M is not required there. The index starts at 1 throughout and the compatibility equations are R-linear, allowing their different A_n scalar rings. The statement is unchanged; no STATEMENT-DISPUTED marker is required.

I checked delivery-errors B–E individually: self-contained objects and inline ideal-multiple/reduction definitions; correct source tag and label; ordinary single TeX escapes; honest searches; no proof steps or proof-dependency lists on the new jobs; no duplicate or parent-clause restatement; exact literal citations; no unproved comparison, hidden non-elementary input or cycle introduced in the parent. This is the explicit work-spreading exception requested in the return, not a new lemma for a two-line identity: the two deferred arguments have comparable sizes and distinct hypotheses, while the elementary final assembly remains in the parent.

## Mathlib evidence

Both jobs have two independently phrased LeanFinder queries, a valid comma-separated Loogle query, a source grep and LeanSearch attempted through the prescribed msearch.py. LeanSearch returned the service's rate-limit error and is recorded as unavailable. LeanFinder and Loogle worked. The full raw returned hits are retained in the search-result files and node records. The first broad source grep also returned irrelevant occurrences of exact followed by quotient; the additional targeted projective/quotient/nilpotent grep returned seven Grassmannian or projective-dimension hits and no quotient-tower theorem. The supplementary Module/Projective source search was read as well; its single-file output has the search wrapper's filename/line parsing oddity, so no location claim rests on that output. The actual source file was read directly.

Read Module.Flat.projective_of_finitePresentation at Mathlib/RingTheory/Flat/EquationalCriterion.lean:287: it requires finite presentation, absent here. Module.Flat.of_projective proves the reverse implication. Read AdicCompletion.map_exact at Mathlib/RingTheory/AdicCompletion/Exactness.lean:184 and the Noetherian/finite-middle-module context; it is not quotient projectivity and supplies no compatible linear splitting. Read the element-correction lemmas at Functoriality.lean:379,393 and the map-surjectivity result at 410: they give individual corrected representatives or surjectivity, not a linear section compatible at all levels. Read Module.projective_lifting_property at Algebra/Module/Projective.lean:91: a single projective lifting property does not by itself assert the induction needed here. The IsAdicComplete.StrictMono hits use an already compatible family and do not construct it. Therefore neither child is an exact match or one-line specialization of a found declaration.

## Preserved argument and workload allocation

The following are the seven steps read from the returned live item, verbatim, with their original node citations; only their allocation is new. This preserves the full proof for the future workers without writing proof steps into their statement-only nodes.

### Former Step 1 → lem-trf-adic-quotient-projective-short-exact

Write $K_n=K/I^nK$, $E_n=E/I^nE$ and $M_n=M/I^nM$. For each $n\ge1$, apply [lem-weil-pbc-flat-quotient-tensor-injective] to the given short exact sequence and $N=R/I^n$, using the assumed flatness of its last term $M$. Identify each tensor product with its quotient using clause (1) of [lem-weil-pbc-tensor-over-quotient-ring]. On $\bar r\otimes x$ the identification is $rx\bmod I^nL$, so the resulting maps are precisely the maps $u_n:K_n\to E_n$, $v_n:E_n\to M_n$ induced by $u,v$. Hence $0\to K_n\xrightarrow{u_n}E_n\xrightarrow{v_n}M_n\to0$ is short exact. Evaluation on representatives shows these maps commute with reduction from level $n+1$ to level $n$.

Original cited statements: lem-weil-pbc-flat-quotient-tensor-injective, lem-weil-pbc-tensor-over-quotient-ring.

### Former Step 2 → lem-trf-adic-quotient-projective-short-exact

For every $n\ge1$ set $A_n=R/I^n$ and let $J_n$ be the image of $I$ in $A_n$. By [lem-weil-pbc-flat-module-quotient-flat], $M_n$ is flat over $A_n$. Products of $n$ elements of $J_n$ vanish, so $J_n^n=0$. The scalar action gives $J_nM_n=IM/I^nM$, and the maps $[m]\mapsto[m]$ in both directions identify $M_n/J_nM_n$ with $M/IM$, and $A_n/J_n$ with $R/I$. The maps are well-defined because their kernels before taking the second quotient are respectively $IM/I^nM$ and $I/I^n$. Under these identifications the reduction of $M_n$ is projective by hypothesis: its lifting property transports across these isomorphisms by composing the given map with the isomorphism and the resulting lift with its inverse [def-weil-pbc-projective-module]. Thus [lem-trf-local-nilpotent-projective-flat-lift] applied to $(A_n,J_n,M_n)$ makes every $M_n$ projective over $A_n$.

Original cited statements: lem-weil-pbc-flat-module-quotient-flat, def-weil-pbc-projective-module, lem-trf-local-nilpotent-projective-flat-lift.

### Former Step 3 → lem-trf-adic-projective-compatible-sections

The projective lifting property [def-weil-pbc-projective-module], applied to $\mathrm{id}_{M_1}$ and the surjection $v_1$ of Step 1, gives an $A_1$-linear section $s_1:M_1\to E_1$. We construct compatible $A_n$-linear sections $s_n$ inductively. Fix $n\ge1$ and a section $s_n$, and form the submodule $P=\{e\in E\mid e\bmod I^nE\in\operatorname{im}(s_n)\}$, the inverse image of the submodule $\operatorname{im}(s_n)$ under the quotient map.

Original cited statements: def-weil-pbc-projective-module.

### Former Step 4 → lem-trf-adic-projective-compatible-sections

The restriction $v:P\to M$ is surjective. Indeed, given $m\in M$, choose $e_0\in E$ representing $s_n(m\bmod I^nM)$. Since $v_ns_n=\mathrm{id}$, $d=m-v(e_0)$ lies in $I^nM$. Write $d=\sum_j a_jm_j$ with $a_j\in I^n$, and choose $e_j\in E$ with $v(e_j)=m_j$ using the original surjectivity of $v$. Then $p=e_0+\sum_j a_je_j$ has $v(p)=m$ and $p\bmod I^nE=s_n(m\bmod I^nM)$, so $p\in P$. Since $v(I^{n+1}P)\subseteq I^{n+1}M$, it induces an $A_{n+1}$-linear surjection $\pi:P/I^{n+1}P\to M_{n+1}$.

Original cited statements: none (elementary).

### Former Step 5 → lem-trf-adic-projective-compatible-sections

By Step 2, $M_{n+1}$ is projective over $A_{n+1}$. Apply [def-weil-pbc-projective-module] to lift $\mathrm{id}_{M_{n+1}}$ through $\pi$, obtaining a section $t:M_{n+1}\to P/I^{n+1}P$. Inclusion $P\subseteq E$ induces $j:P/I^{n+1}P\to E_{n+1}$, because $I^{n+1}P\subseteq I^{n+1}E$. Set $s_{n+1}=jt$. Since $v_{n+1}j=\pi$, this is a section. To check compatibility, for $y\in M_{n+1}$ represent $t(y)$ by $p\in P$. There is $w\in M_n$ with $p\bmod I^nE=s_n(w)$. Applying $v_n$ gives $w=v(p)\bmod I^nM=y\bmod I^nM$, using $\pi t=\mathrm{id}$. Thus reducing $s_{n+1}(y)$ to $E_n$ gives exactly $s_n(y\bmod I^nM)$. Inductively choosing these sections yields a compatible family $(s_n)_{n\ge1}$.

Original cited statements: def-weil-pbc-projective-module.

### Former Step 6 → parent Step 3

For a compatible family $(m_n)\in\widehat M$ define $s((m_n))=(s_n(m_n))$. Step 5 shows this is a compatible family in $\widehat E$. Each $s_n$ is $A_n$-linear, hence $R$-linear, so componentwise operations make $s$ $R$-linear. At every level $v_ns_n=\mathrm{id}_{M_n}$, whence $\widehat v\circ s=\mathrm{id}_{\widehat M}$ and $\widehat v$ is surjective.

Original cited statements: none (elementary).

### Former Step 7 → parent Step 4

Finally $\widehat u$ is injective because each $u_n$ is injective by Step 1. If $e=(e_n)\in\ker(\widehat v)$, Step 1 gives a unique $k_n\in K_n$ with $u_n(k_n)=e_n$. Write $a_n:K_{n+1}\to K_n$ and $b_n:E_{n+1}\to E_n$ for reduction. Then $u_n(a_n(k_{n+1}))=b_n(u_{n+1}(k_{n+1}))=b_n(e_{n+1})=e_n=u_n(k_n)$. Injectivity of $u_n$ gives $a_n(k_{n+1})=k_n$. Thus $(k_n)\in\widehat K$ maps to $e$. Conversely $v_nu_n=0$ at every level, so $\widehat v\widehat u=0$. Therefore $\operatorname{im}(\widehat u)=\ker(\widehat v)$. Together with Step 6 this gives every conclusion.

Original cited statements: none (elementary).

## Unfinished work

No unresolved issue within this one-level repair. The two new nodes are deliberately statement-only unsplit jobs for subsequent workers; no claim of a Lean proof is made. No Lean file was written and no compiler, Lake or build tool was run. Required server dry-run and final push results are recorded after verification.

## Verification

Historical verification: the earlier repair dry run passed preflight at ed4bedf0266. A reread corrected the last assembly step’s stale reference from former Step 6 to current Step 3; the preserved historical argument above remains verbatim. For this landing-return repair, the initial server dry run passed at 9337548bc49. The final dry run and push must verify the updated report, split summary and expanded Step 4 quotation.

Current repair verification: the mandatory initial dry run exited OK at `1d814fbb92c`. After the explicit compatibility and current-return updates above, the final dry run and push are performed on the exact sandbox contents; their exit results are reported by the delivery tool.

Latest repair verification (2026-10-23): mandatory initial dry run exited OK at db4e164dde9. The final dry run and push verify the changed parent proof and refreshed report; their terminal results are given by deliver.py.
