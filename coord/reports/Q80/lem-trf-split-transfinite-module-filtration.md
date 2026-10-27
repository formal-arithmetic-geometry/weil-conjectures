# Q80 stage-1 repair report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-split-transfinite-module-filtration.json: existing statement unchanged; five-step assembly, two new cited helpers.
- dag/nodes/sec-trace-formula/lem-trf-transfinite-successor-generators-surjective.json: statement-only, status unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-filtration-successor-maps-independent.json: statement-only, status unsplit; no Mathlib match.
- citations.json: verbatim statements for every node cited in every parent proof step.

## Attachments

None. The project theorem Module.nonempty_linearEquiv_directSum_of_split_transfinite_filtration in lean/Sheaf/LinearAlgebra/SplitTransfiniteModuleFiltration.lean:56 ends with sorry. No exact finished declaration was found by the blueprint tag or the filtration concepts in lean/WeilConjectures.

## WANTED

None: the source for the parent and both children is available locally.

## Repair and continuity with the returned version

The sandbox initially contained only dispatcher brief markers, with no JSON, report, citations or search log. I copied the live returned parent, retaining its statement, citations, inherited Mathlib searches, metadata and source; no prior sandbox split was available to dry-run first. The delivery tool rebases the owned fields onto the current server head. The numbered return has one substantive demand: distribute the 3960-character proof into at least two comparable independently workable statement-only nodes and leave an assembly of at most 3000 characters. This delivery creates precisely two such nodes. The parent preserves the actual section construction, finite-sum construction, and linear inverse; its old surjectivity and injectivity arguments are assigned respectively to the new generation and independence lemmas. Neither child assumes split quotients or concludes an isomorphism, and neither subsumes the other.

No statement dispute or source error was found. There is no change to the current chapter/unit route, no SGA source, no Lean edit, compiler, Lake invocation or repository git command. This helper's inherited ancestry is algebraic; I read the current ancestor's blueprint_update and the chapter/unit records and do not alter their contracting-correspondence route.

## Landing return L: rebase and promotion repair (2026-10-22)

The latest return is distinct from the original proof-length repair: the independent reader approved that split, but landing refused it because the side-project completion had not been promoted to the live DAG. I retained the delivered sandbox files, report, citations and searches, and ran the required dry run first. It exited successfully with `OK (not pushed)` at b5781f43302 after fetching the current server head. The delivery tool performs the rebase; no repository git command was run.

I compared all three retained node files with the current shared DAG. Both child ids remain absent there. For the parent, only `proof`, `proof_deps`, and `split_report` differ: the current parent still has the original five-step proof. Its statement, statement dependencies, source, inherited searches, blueprint ancestry, Lean attachment and review metadata are equal to the retained version and are preserved. Thus the substantive rebased change remains replacing the transfinite-generation and finite-support-independence arguments with the two separately stated child nodes; this is not an unchanged re-push of the original parent.

I reread every cited statement on this current base, including both existing Mathlib definition leaves. The quotient node still explicitly supplies the surjective linear quotient map and its kernel, exactly what step 1 uses. The direct-sum node still explicitly supplies finite-support families, componentwise operations, inclusions and their finite-sum expansion, exactly what steps 2 and 5 use. The two retained child statements still give respectively every-stage generation and injectivity for the actual sum map, with all hypotheses supplied in steps 1–2. Every citation quote remains a verbatim substring. No changed cited mathematical statement requires altering the proof. I also reread Stacks 058U/058V, the current chapter/unit records and the Sheaf theorem ending in `sorry`; no attachment or route change is justified. Searches by tag and transfinite-filtration concepts found no new duplicate or finished WeilConjectures declaration. The earlier logged Mathlib searches are reused because neither the statements nor their search questions changed.

For this landing repair I rechecked the zero, one-successor and limit-endpoint cases: generation needs the zero stage and limit continuity, whereas independence only uses a largest finite-support index and the modulo-predecessor hypothesis. The explicit section construction and linear inverse remain in the 2712-character parent assembly, whose longest step is 824 characters. Both extracted nodes remain statement-only and neither depends on the parent. The final dry run and push below are required to deliver this rebased split for live promotion by L; no promotion state is forged in the sandbox.

## Not duplicates

lem-trf-transfinite-successor-generators-surjective vs lem-trf-split-transfinite-module-filtration: the parent concludes an isomorphism with successive quotients under split inclusions; this child concerns arbitrary maps and only generation of stages, without injectivity.

lem-trf-transfinite-successor-generators-surjective vs lem-trf-projective-kaplansky-direct-summand: that node concerns a direct summand of a sum of countably generated modules and concludes another countable-factor decomposition; this child has neither a projective/direct-summand assumption nor any countable-generation conclusion.

lem-trf-filtration-successor-maps-independent vs lem-trf-split-transfinite-module-filtration: the parent concludes an isomorphism with successive quotients under split inclusions; this child concerns arbitrary maps and only injectivity of their sum, without continuity, exhaustion or generation.

lem-trf-filtration-successor-maps-independent vs lem-trf-projective-kaplansky-direct-summand: that node concerns a direct summand of a sum of countably generated modules and concludes another countable-factor decomposition; this child has neither a projective/direct-summand assumption nor any countable-generation conclusion.

Whole-DAG searches covered the source tag and label, transfinite and ordinal filtrations, finite-support injectivity, and triangular maps. Blueprint searches for transfinite and 058V returned no imported nodes; searches for finite support, direct sum and filtration found only different statements (finite filtered objects, graded decompositions, sheaf coproducts, and projective-dimension bounds). The well-ordered-union projective-dimension nodes conclude resolution bounds rather than images or injectivity of an explicit sum map. Lean concept searches found no match for either child. Both new ids were absent before writing.

## Review by Q80

I read algebra.tex, Definition definition-devissage (Tag 058U, conditions (0)–(3)) and the complete proof of lemma-direct-sum-devissage (Tag 058V, lines 20409–20453). They justify the source of the parent and BOTH new nodes: the paragraph identifying images of f_beta is exactly the generation argument, and the following injectivity paragraphs use the new summand's independence and finite support. The second child's maximal-support proof is the same argument without repeated induction; neither needs countable generation or projectivity. I checked the tag-to-label mapping in tags/tags. I read both existing definition nodes in full, especially the quotient map's kernel and the direct sum's finite-support operations. I also read the existing Sheaf theorem and docstring; its sorry prevents attachment.

Parent step 1 cites def-weil-pbc-quotient-module. Its statement explicitly gives the quotient map as surjective and linear with kernel the submodule; these are exactly the facts used to descend x-jr(x), prove qs=1 and obtain the complement identity. The retraction identity is a hypothesis, not an uncited splitting theorem. Set-indexed classical choice is sufficient. The calculation is elementary and stays explicit.

Parent step 2 cites def-weil-pbc-direct-sum-modules, whose statement explicitly gives finite support, componentwise operations, inclusions and the expansion as a finite sum. This supplies the domain and map formula, linearity, D_beta and compatibility with X_beta; alpha<beta implies alpha+1<=beta, so every summand lies in the stated stage. No colimit or proper-class existence result is used.

Parent step 3 cites lem-trf-transfinite-successor-generators-surjective. I opened the written child and checked that its conclusion is the full equality f(D_beta)=X_beta for all beta<=kappa, not just density or an abstract generation assertion. The parent supplies A_alpha=Q_alpha and t_alpha=s_alpha, X_0=0 and limit continuity from the original assumptions, and successor generation from step 1. X_kappa=X and D_kappa=D give surjectivity. No injectivity is taken from this child.

Parent step 4 cites lem-trf-filtration-successor-maps-independent. Its statement gives injectivity for precisely the finite-sum map in step 2. Its only substantive additional premise is that t_alpha(a) in X_alpha forces a=0, which follows explicitly from q_alpha s_alpha=1 in step 1. The codomain of t_alpha is X_(alpha+1), the filtration is increasing, and both facts match the child. No continuity or generation is taken from this child. This isolates a separate argument from step 3, with no circular dependency on the parent or on the generation child.

Parent step 5 cites def-weil-pbc-direct-sum-modules only to identify the output module. Surjectivity and injectivity have already been obtained. Unique preimages give a linear inverse by the explicit addition/scalar identities retained from the return, so no uncited isomorphism theorem is hidden here.

I checked B–E point by point: both new statements introduce every object and hypothesis, cite their sole defined construction, contain no proof steps or proof dependencies, and use single-escaped TeX. Their common sum formula defines the map, not a proof sketch. They are genuine smaller arguments, not restatements of the original isomorphism, not duplicates, and not elementary two-line observations: the generation proof needs ordinal base/successor/limit cases; the independence proof needs a maximal nonzero finite support argument. All non-elementary parent steps cite the exact helper statements. Every cited statement is copied verbatim into citations.json. The parent retains its original statement byte-for-byte, and no new step exceeds 2000 characters.

Small cases checked: kappa=0 makes D empty and X_0=0 for generation, while the independence map is the injective map 0->X even without X_0=0. At kappa=1 the children reduce respectively to X_1=image(t_0) when X_0=0 and ker(t_0)=0 from the modulo-X_0 premise. Repeated stages allow zero factors, and nonzero factors cannot satisfy the independence premise if their entire image lies in the preceding stage. At kappa=omega, continuity is essential only for generation; all kernel relations have finite support and thus a largest index. The zero ring causes no exception. Maps and ordinals are set-indexed, and all sums are finite.

Mathlib searches were run only through the required msearch.py command and read before recording. Each child has LeanSearch, Loogle, grep and two different LeanFinder phrasings. The direct-sum range, componentwise-map and independence lemmas were checked against their source: they require exactly the generation/independence work being extracted, so neither child is a one-line specialization. The full log and original parent searches are retained. No unavailable service is recorded as a negative search.

## Full argument retained for the next workers

The following is the returned five-step proof, preserved verbatim so that no argument is lost. Steps 1, 2 and 5 remain explicit in the parent. Old step 3 is now the generation child's independent task, with Q_alpha replaced by arbitrary A_alpha and successor decomposition assumed. Old step 4 is now the independence child's independent task, with the implication obtained by q_alpha s_alpha=1 replaced by its explicit hypothesis. This preserves all actual arguments while the new node files themselves remain statement-only.

### Returned step 1

For each $\alpha<\kappa$ choose a retraction $r_\alpha:X_{\alpha+1}\to X_\alpha$ of the inclusion $j_\alpha:X_\alpha\hookrightarrow X_{\alpha+1}$; this is a set-indexed choice. Put $Q_\alpha=X_{\alpha+1}/X_\alpha$, with quotient map $q_\alpha$ from [def-weil-pbc-quotient-module]. Define
$$s_\alpha:Q_\alpha\longrightarrow X_{\alpha+1},\qquad s_\alpha(q_\alpha(x))=x-j_\alpha r_\alpha(x).$$
This is independent of the representative: replacing $x$ by $x+j_\alpha(a)$ changes the right side by $j_\alpha(a)-j_\alpha r_\alpha j_\alpha(a)=0$. The formula is additive and $R$-linear. Moreover $q_\alpha s_\alpha=\mathrm{id}$, since the subtracted term belongs to $X_\alpha$. Thus every $x\in X_{\alpha+1}$ satisfies $x=j_\alpha r_\alpha(x)+s_\alpha q_\alpha(x)$, and $s_\alpha(z)\in X_\alpha$ implies $z=q_\alpha s_\alpha(z)=0$.

### Returned step 2

Using the finitely supported families of [def-weil-pbc-direct-sum-modules], set $D=\bigoplus_{\alpha<\kappa}Q_\alpha$ and define
$$f:D\longrightarrow X,\qquad f((z_\alpha))=\sum_{\alpha\in\operatorname{supp}(z)}s_\alpha(z_\alpha),$$
where each $X_{\alpha+1}$ is included in $X$. This is a finite sum. On the union of the finite supports of two families the formula gives $f(z+w)=f(z)+f(w)$, and likewise $f(az)=af(z)$, so $f$ is $R$-linear. For $\beta\leq\kappa$, let $D_\beta$ be the submodule of $D$ consisting of the families whose components vanish for $\alpha\geq\beta$. For $\alpha<\beta$ we have $\alpha+1\leq\beta$, hence $s_\alpha(z_\alpha)\in X_\beta$. It follows term by term that $f(D_\beta)\subseteq X_\beta$, and $D_\kappa=D$.

### Returned step 3

We prove $X_\beta=f(D_\beta)$ for every $\beta\leq\kappa$. If equality failed, choose the least failing ordinal $\beta$; such a least element exists because these ordinals are well-ordered. The case $\beta=0$ cannot fail: $X_0=0$ and $D_0=0$. If $\beta=\gamma+1$, take $x\in X_{\gamma+1}$. By step 1,
$$x=r_\gamma(x)+s_\gamma(q_\gamma(x)),$$
with $X_\gamma$ viewed as a submodule of $X$. By minimality, $r_\gamma(x)=f(z)$ for some $z\in D_\gamma$. Adding to $z$ the family supported only at $\gamma$ with component $q_\gamma(x)$ gives an element of $D_{\gamma+1}$ mapping to $x$, by [def-weil-pbc-direct-sum-modules] and [def-weil-pbc-quotient-module]. If $\beta$ is a nonzero limit ordinal, continuity gives, for every $x\in X_\beta$, an ordinal $\gamma<\beta$ with $x\in X_\gamma$. Minimality gives a preimage in $D_\gamma\subseteq D_\beta$. Each case contradicts failure, since step 2 already gives the reverse inclusion. At $\beta=\kappa$ we obtain $f(D)=X_\kappa=X$, so $f$ is surjective.

### Returned step 4

To prove injectivity, suppose $z\in D$ is nonzero and $f(z)=0$. By [def-weil-pbc-direct-sum-modules], its nonzero support $S$ is finite and nonempty. It has a largest ordinal $\gamma$: enumerate its finitely many elements and at each addition retain the larger one. For every $\alpha\in S$ with $\alpha<\gamma$, we have $s_\alpha(z_\alpha)\in X_{\alpha+1}\subseteq X_\gamma$. The equation
$$s_\gamma(z_\gamma)=-\sum_{\alpha\in S,\ \alpha<\gamma}s_\alpha(z_\alpha)$$
therefore puts $s_\gamma(z_\gamma)$ in $X_\gamma$. Apply the quotient map $q_\gamma:X_{\gamma+1}\to X_{\gamma+1}/X_\gamma$ of [def-weil-pbc-quotient-module]. Step 1 gives $z_\gamma=q_\gamma s_\gamma(z_\gamma)=0$, contradicting $\gamma\in S$. Thus $\ker f=0$. This finite-support argument covers a limit endpoint as well: it never assumes that an element has infinitely many nonzero components.

### Returned step 5

Steps 3–4 show that $f:D\to X$ is bijective. For each $x\in X$ let $g(x)$ be its unique preimage. If $x,y\in X$ and $a\in R$, then $f(g(x)+g(y))=x+y$ and $f(ag(x))=ax$; uniqueness gives $g(x+y)=g(x)+g(y)$ and $g(ax)=ag(x)$. Hence $g$ is an $R$-linear inverse and provides the required isomorphism $X\cong D=\bigoplus_{\alpha<\kappa}(X_{\alpha+1}/X_\alpha)$, with [def-weil-pbc-direct-sum-modules]. If $\kappa=0$, the assumptions give $X=0$, $D$ is the empty direct sum, and this same construction is the unique isomorphism between zero modules.

## Unfinished work

The two extracted lemmas are intentionally unsplit, as the re-split return requests; their proofs are separate future tasks. The landing-return repair is documented above; final validation and delivery are performed by the delivery tool. The two child proofs remain future stage-1 tasks by design.


## Current retry: retained delivery compared with current DAG

This retry began with the complete earlier delivery already in the sandbox. I retained its proof, both helper statements, full report, citation quotes and search log. The first required dry run exited with `OK (not pushed)` at `1cf58666bad`; this is the current retry's receipt, distinct from the historical receipt above. The tool fetched and rebased against the current server DAG before admitting preflight.

I independently compared every top-level field of the retained parent with the current shared parent: only `proof`, `proof_deps` and `split_report` differ. Both extracted helper ids are still absent from the current DAG. I reread all four statements cited in the assembly (the two existing definition leaves and the two retained helper statements), the full Stacks 058U/058V source, and the current chapter/unit records. No cited statement changed its mathematical content relative to the retained split, so no dependency replacement or alteration of the assembly is warranted. I checked every citation quote against the actual current statement and each new node's recorded query against searches.jsonl. The five steps still total 2712 characters and retain the quotient section, finite-sum map and linear inverse explicitly.

The source theorem in Sheaf still ends in `sorry`; fresh searches in WeilConjectures provide no finished attachment. Fresh DAG and blueprint searches found no replacement for either helper. The existing search results and candidate Mathlib sources were reread; their assumptions still require the generation or independence arguments isolated here. At the empty endpoint, the generation assumptions force X=0; independence separately handles the empty sum into arbitrary X. At a nonzero limit, continuity is used solely for generation and finite support supplies a largest index for independence. These checks confirm the approved split survives this rebase with unchanged statements. This update records the landing-return repair; live promotion is left to L as the return instructs. Final dry run and push follow this report update.


## Landing-return retry review on the newly fetched base

This invocation began with the returned, approved three-node delivery present. As required, I ran the retained files through deliver.py --no-push before editing anything; it fetched the current server base, completed preflight, exited successfully, and printed `OK (not pushed)` at `73d8b179774`. This receipt supersedes the earlier retry receipts for this attempt. No direct git command or live-repository write was used.

I compared all top-level parent fields against the present shared DAG: precisely proof, proof_deps and split_report differ. Both proposed helper ids remain absent. The current released stage-1 repair note still explicitly requires two comparable statement-only children and a parent assembly below 3000 characters, preserving its statement and route. The retained assembly has 2712 characters, with step lengths 824, 740, 337, 267 and 544. Its two separate arguments and their full old proofs are retained above; the return concerns promotion of this work from the side DAG, not a mathematical rejection. The delivery tool rebases onto the current server DAG; promotion remains L's action.

I reread the full source Definition 058U (definition-devissage) and Lemma 058V (lemma-direct-sum-devissage), and the current chapter/unit and repair records. Step 1 uses the current quotient node's explicit surjective linear quotient map and kernel, with the retraction identity from the item's hypothesis. Step 2 uses the current direct-sum node's finite support and componentwise operations. Step 3 uses the generation child's every-stage equality, supplying its zero stage, continuity and successor-generation hypotheses. Step 4 uses the independence child's sum-map injectivity under the modulo-predecessor implication proved in step 1. Step 5 uses the explicit unique-preimage linear inverse and the direct-sum definition. I verified every one of the five citation quotes against the current cited statement; none requires replacement or a mathematical adjustment.

I reread all retained helper query results in searches.jsonl and their node records, checked that the tool/query pairs coincide, and reread the direct-sum range and independent-sum Mathlib candidates. Those candidates still require generation or independence as input rather than providing the ordinal-filtration arguments. The questions and statements are unchanged, so I did not rerun recorded searches. Fresh whole-DAG searches by 058V, source label and filtration/generation/independence concepts, plus blueprint searches for transfinite and 058V, found no replacement. In particular the nearby well-ordered-union projective-dimension, triangular-relation, derived-basis increasing-union, and preaisle-closure statements concern different conclusions and hypotheses. Project-source searches found no finished WeilConjectures attachment; the recorded Sheaf theorem still ends in sorry.

The edge-case checks remain valid on this base: at kappa=0 the generation assumptions force the zero stage, while independence holds for the empty sum into any X; at kappa=1 the hypotheses supply precisely generation and injectivity of the one summand. At a limit endpoint continuity supplies generation, and a finite nonzero support still has a largest index for independence. Repeated stages and the zero ring introduce no exception. Both helpers are statement-only, self-contained, noncircular and strictly smaller than the original equivalence; no step exceeds 2000 characters. Thus B--E and C1/C4 remain satisfied after this rebase. The only changes needed in this retry were recording the current-base review and receipt, preserving the approved proof and all search/citation evidence. Final dry run and push follow.


## Rebase review of 2026-10-23 (current delivery attempt)

The retained three-node delivery was present at startup. Before any edit I ran the required dry run to completion; it passed server preflight and printed `OK (not pushed)` at `69d00d55b81`. That receipt belongs to this attempt; the earlier receipts above are retained history. The delivery tool fetches the current server DAG and rebases the owned files in its temporary worktree.

I compared the retained parent field by field against the current read clone: its statement, statement dependencies, source, blueprint ancestry and Lean/review records are identical; only proof, proof_deps and split_report differ. Both helper ids remain absent from the current DAG. I reread every cited statement, the released keep_plan repair order, the chapter/unit records and the ancestor's current blueprint_update. No cited mathematical content changed, so the approved assembly needs no mathematical alteration. The repair is the rebased extraction of the two helpers from the current parent's original proof, with this new current-base review; L remains responsible for promoting the delivery to the live DAG.

For C1/C4, step 1 uses exactly the quotient node's linear surjective map and kernel to construct its section from the assumed retraction. Step 2 uses exactly the direct-sum node's finite supports and componentwise operations. Step 3 supplies zero stage, continuity and successor generation to the generation child's every-stage image equality. Step 4 supplies the modulo-predecessor implication to the independence child's injectivity assertion. Step 5 retains the explicit unique-preimage construction of the linear inverse. I verified all five citation quotes against these actual statements. I reread Stacks algebra.tex, Definition 058U and the complete Lemma 058V proof, and checked the tag mapping. The parent still has 2712 proof characters (824, 740, 337, 267, 544 per step).

I read all 11 retained search-log results and checked each helper's recorded tool/query pairs against that log. The statements and search questions did not change, so I reused those searches. I reread the Mathlib range and independent-sum candidates: they require the generation or independence input that these helpers establish. Fresh searches of the entire DAG by tag/source label and ordinal-filtration concepts, and blueprint searches for transfinite and 058V, found no replacement. The same-tag Kaplansky node has the different countably-generated direct-summand conclusion already distinguished above; the well-ordered-union projective-dimension node supplies a resolution bound. A fresh project-source search found no finished WeilConjectures attachment; the recorded Sheaf theorem still ends in sorry.

The B--E review also checked the empty ordinal, one successor, repeated stages, zero ring and limit endpoint. In the generation helper the zero stage and continuity are essential and explicitly present. In the independence helper no exhaustion or continuity is needed, because each nonzero relation has finite support with a largest ordinal. Both helper statements are self-contained and remain unsplit with no proof dependencies; neither assumes the parent's equivalence or cites it. All original arguments are retained above. No statement dispute, route change, repository write, Lean edit, compiler invocation or direct git command occurred. Final validation and push follow this review.

For a reproducible comparison on the next base, the four cited statement SHA-256 values checked in this attempt are:

- def-weil-pbc-direct-sum-modules: `21a51fe33906e8438a002c78382873865326e8599e01ddea4845528cb4ab0e9e`

- def-weil-pbc-quotient-module: `df0145a1a52adfcb1a02c6fcdf989365a54fcb667c21e225b76cdadd5fc2bf5f`

- lem-trf-filtration-successor-maps-independent: `64311ce09922f6e6dcbca30d23a0c7ed55350444291b4ef940f881865ffddba9`

- lem-trf-transfinite-successor-generators-surjective: `5e553599545cf6d61729cc69a0da82922e5e7b1af76a9e60fce638307ce10d24`
