# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-filtered-colimit-strictly-henselian-local.json: unchanged statement, four-step assembly replacing the returned long proof.
- dag/nodes/sec-six-functors-basics/lem-sfb-local-colimit-residue-field.json: statement; status unsplit; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-separably-closed-field-colimit.json: statement; status unsplit; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-henselian-colimit-stage-root.json: statement; status unsplit; no exact Mathlib match.
- citations.json: verbatim statement quotes for every proof-step dependency.
- searches.jsonl: actual search log; repair.py: sandbox-only writing helper.

## Attachments

None. The project search under lean/WeilConjectures has no exact declaration for the item or the three new statements. The existing theorem CommRingCat.isStrictlyHenselianLocalRing_colimit_of_local_maps, lean/Sheaf/RingTheory/FilteredColimitStrictlyHenselianLocal.lean:80, has sorry, so is not an attachment. No Lean was written or compiled.

## WANTED

None. The Stacks source and blueprint unit are present locally.

## What was wrong and what was repaired

The return requires spreading the work rather than shortening the old proof. The sandbox initially had only dispatcher dotfiles, no node, report or search log; I copied the live repository's returned version, whose seven proof texts total 4678 characters. Its statement remains byte-for-byte unchanged. Three new statement-only unsplit nodes now hold the three substantial independent arguments, and the parent only assembles their conclusions. No existing node besides the item is edited. The new statements expose the maximal-ideal contraction and residue cocone, separable field permanence without algebraicity assumptions, and the monic same-degree polynomial and lifted root at a finite stage. All original arguments are retained below, not summarized away.

The source is Stacks algebra.tex, Tag 04GI, label lemma-colimit-henselian. I also read Definition 04GF, label definition-henselian; its simple-root convention is reconciled with our idempotent convention using the existing root-lifting equivalence, not silently identified. I read the fixed chapter/unit records and the master unit text. This local-ring tool remains below the existing open-direct-image input; no route is changed. blueprint_refs.py ancestor returns None for this created chain; the inherited null ancestor, precise place and via chain are preserved, with the item prepended for its new children.

## Not duplicates

lem-sfb-local-colimit-residue-field vs lem-sfb-finite-contractible-diagram-localizations: the existing node assumes finite finitely presented algebras over a w-contractible base and identifies localizations at primes with maximal contractions; it does not give the maximal ideal, contractions, or residue-field colimit for arbitrary local-ring diagrams as the new node does.

lem-sfb-separably-closed-field-colimit vs lem-sfb-finite-contractible-diagram-localizations: the existing node is about finite algebras over a w-contractible base and strictly henselian localizations; it does not assert separable closedness of an arbitrary directed ring colimit of separably closed fields, whose transition extensions need not be algebraic.

lem-sfb-henselian-colimit-stage-root vs lem-sfb-finite-contractible-diagram-localizations: the existing node gives strictly henselian localizations for finite algebra diagrams; it does not supply a same-degree monic polynomial, a simple residue root, and its henselian lift at a common finite stage for arbitrary henselian local-ring diagrams.

lem-sfb-local-colimit-residue-field vs lem-sfb-filtered-colimit-strictly-henselian-local: the new statement treats arbitrary local rings, proves contractions and the residue-colimit cocone, and assumes no henselianity; the parent asserts strict henselian permanence.

lem-sfb-separably-closed-field-colimit vs lem-sfb-filtered-colimit-strictly-henselian-local: the new statement concerns only fields and their ring colimit, with no local-ring or henselian conclusion.

lem-sfb-henselian-colimit-stage-root vs lem-sfb-filtered-colimit-strictly-henselian-local: the new statement gives a polynomial, a simple residue root and a solution at one stage, assumes locality/residue colimits already, and neither asserts locality nor separable closedness of the colimit.

lem-sfb-local-colimit-residue-field vs lem-weil-pbc-flat-local-tower-direct-limit: the existing theorem assumes flat algebras over a fixed local base, fixed maximal-ideal extension and compatible maps to a fixed field; those hypotheses are absent here, and its statement does not identify the general residue-field colimit.

lem-sfb-local-colimit-residue-field vs lem-per-noetherian-local-colimit-regular: the existing result requires regular local stages and a Noetherian colimit; it does not state the residue cocone or contractions under the general local-ring hypotheses.

Among the new nodes, locality/residue colimits assumes no henselian or separably closed input; field permanence concerns arbitrary fields and assumes no algebraicity; the stage-root statement assumes locality and a residue colimit, and proves finite-stage root data. These are different statements and independent arguments, not mutual aliases. The earlier source-field search for 04GI found only the parent; the resumed current-DAG check also finds lem-sfb-finite-contractible-diagram-localizations, whose statement has now been opened and distinguished above. Full-DAG keyword searches, blueprint_refs searches for colimit/local, residue field colimit, separably closed, direct limit, simple root, henselian and 04GI found no duplicate.

## Mathlib results read

For each new id I ran leansearch, loogle, leanfinder, grep, and a second leanfinder phrasing through the prescribed msearch.py. All services answered; the actual queries and results are recorded without invented searches. I read the returned signatures, and inspected Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean:96,116,121 (induced residue maps and their formula), Mathlib/RingTheory/Henselian.lean:108,119 (henselian class and TFAE), and Mathlib/FieldTheory/PurelyInseparable/Basic.lean:567 (Algebra.IsAlgebraic.isSepClosed). None states the new result or specializes to it in one line. In particular a directed system of separably closed fields need not be algebraic over any fixed stage; that algebraic-extension theorem is insufficient. Ring.DirectLimit constructions do not supply the local-ring residue-colimit comparison. HenselianLocalRing.TFAE requires a henselian ring or the lifting condition already, and does not descend the data to a stage. The item retains its prior searches and their results; they agree with the present searches for the extracted arguments.

## Review by Q83

On resumption for the landing refusal, I compared every field of the retained item against the current read-only DAG. Only proof, proof_deps, proof_origin and split_report differed, exactly the re-split fields; the statement, stmt_deps, blueprint provenance, Lean record and maintainer reviews were retained. I reread every parent dependency statement and all definition statements of the three new nodes. The seven citation entries remain verbatim, and each step's uses is covered exactly. In particular the current root-lifting node still gives both implications with the identical monic-polynomial/simple-residue-root hypotheses; no change of ideal or extra finiteness assumption is being imported. I opened the newly arrived lem-sfb-finite-contractible-diagram-localizations in full: its finite-module and finite-presentation hypotheses over a w-contractible base are absent from each general helper here, and its conclusions do not give the residue cocone or the finite-stage polynomial/root witnesses. This accounts for all three same-tag diagnostics of the first resumed dry run. I reread Stacks algebra.tex lines 42926–42962 (04GI) and the simple-root definition at 42075 (04GF); they support the same three argument allocations and four assembly steps. No new mathematical claim or search query is introduced by this rebase repair.

I read the statement and proof of Stacks 04GI for the parent and every new node: its omitted locality/residue paragraph belongs to lem-sfb-local-colimit-residue-field, its separably closed field sentence to lem-sfb-separably-closed-field-colimit, and its final monic simple-root argument to lem-sfb-henselian-colimit-stage-root. The new nodes have empty proof and proof_deps, and no proof sketch in their statements; the arguments below are a handoff in this report. Their sizes reflect three separate mathematical arguments.

Parent step 1 uses precisely the full statement of the local-colimit node, with the given nonempty small directed poset and exactly the given maximal-ideal contractions. Its conclusion supplies locality of R, locality of all legs and the specified residue cocone, rather than assuming any of them. Parent step 2 reads the strictly henselian clause of def-weil-pbc-henselian-terminology to obtain separable closedness of every residue field, then uses the separably closed field-colimit statement on the very same residue diagram; its field, smallness and directedness hypotheses are satisfied by step 1 and the original index. Parent step 3 uses the henselian clause of the same definition and the full stage-root statement; every local-leg and residue-colimit hypothesis comes from step 1. Evaluation commutes with alpha_i because it is a finite sum of coefficient times power terms, and the specified residue formula gives the claimed residue of alpha_i(a_i). Parent step 4 uses exactly (ii) implies (i) of lem-weil-pbc-henselian-local-root-lifting, whose statement I opened, and the strictly henselian definition; it does not use a definition as a permanence theorem. citations.json records all these citations verbatim.

I checked B: self-contained quantified objects, source tag and label, all required notion references, genuine logged searches, precise blueprint provenance, statement-only new nodes, no finished attachment. I checked C and D by reading every cited statement, preserving all arguments and keeping the new nodes strictly smaller than the parent; none cites the parent and no new cycle is introduced. I checked E by following which ideal and field each map uses. The nonempty hypothesis makes 1 outside the union and excludes a zero-ring colimit. No stage map is treated as injective: only residue-field maps are injective. The same-degree monic lift is constructed with leading coefficient exactly 1, even if ring maps kill coefficients. Nonzero derivative at the target forces the descended derivative nonzero; injectivity of the residue field map reflects the root equation. The Bezout argument uses finite equations, not a claim that separability always descends without witnesses.

Small cases: a singleton or constant diagram recovers the original local ring and its residue field. The noninjective local map k[epsilon]/(epsilon^2) to k still has the asserted contracted maximal ideal and residue cocone; no injectivity slipped in. Field diagrams may have transcendental transitions (for example nested algebraically closed fields), so no algebraicity assumption is added. A monic constant polynomial has no residue root, making the stage-root implication vacuous in degree zero; positive characteristic causes no differentiation problem because integer multiples commute with ring maps. The three new argument handoffs are comparable pieces (old steps 1–3, 4, and 5–6), with step 7 left as assembly. No assembly step approaches 2000 characters and the total stays under 3000.

## Complete retained argument and allocation to the new nodes

The following is the full returned proof verbatim, retained as working material for the new statement-only nodes. It is not a proof added to those new nodes. The existing supporting node statements used here were opened and read: elementwise representatives/equality at a common stage; unit criterion outside the unique maximal ideal; finite-data descent of elements and ring equations; Bezout definition of separability; root definition of separable closedness; henselian terminology; and the two-way monic-root criterion.

### Old step 1 → lem-sfb-local-colimit-residue-field

Write $\alpha_i:R_i\to R$ for the colimit maps and set $M=\bigcup_i\alpha_i(\mathfrak m_i)$. This is an ideal: move any two representatives, and a representative of any multiplier, to one common stage, and use the ideal axioms there. By [lem-pc-filtered-colimit-commrings-elementwise], equality of two representatives is witnessed at a common later stage. Thus, if $\alpha_i(x)=\alpha_j(y)$ with $y\in\mathfrak m_j$, some $k\ge i,j$ satisfies $\varphi_{ik}(x)=\varphi_{jk}(y)\in\mathfrak m_k$, and locality gives $x\in\mathfrak m_i$. Consequently $\alpha_i^{-1}(M)=\mathfrak m_i$. In particular $1\notin M$: choose any $i$ (the index is nonempty), and apply this equality to $1\in R_i$.

Uses: lem-pc-filtered-colimit-commrings-elementwise

### Old step 2 → lem-sfb-local-colimit-residue-field

Every $r\notin M$ has a representative $r=\alpha_i(x)$ by [lem-pc-filtered-colimit-commrings-elementwise]; necessarily $x\notin\mathfrak m_i$. By [lem-weil-pbc-local-ring-unit-criterion], choose $y\in R_i$ with $xy=1$, so $\alpha_i(y)$ inverts $r$. Therefore every nonzero element of $R/M$ is invertible, and $M$ is maximal. Every proper ideal of $R$ is contained in $M$, since an element outside $M$ is a unit. Thus $R$ is local with unique maximal ideal $M$, and the contraction equality in step 1 says that every $\alpha_i$ is local.

Uses: lem-pc-filtered-colimit-commrings-elementwise, lem-weil-pbc-local-ring-unit-criterion

### Old step 3 → lem-sfb-local-colimit-residue-field

Put $\kappa_i=R_i/\mathfrak m_i$ and $\kappa=R/M$. The local transition maps induce compatible field maps $\kappa_i\to\kappa_j$, and $\rho_i([x])=[\alpha_i(x)]$ defines a compatible map $\kappa_i\to\kappa$. Each $\rho_i$ is injective: $\rho_i([x])=0$ means $\alpha_i(x)\in M$, hence $x\in\mathfrak m_i$ by step 1. To verify the colimit universal property [def-weil-pbc-category-colimit], take any compatible ring maps $b_i:\kappa_i\to S$. Their composites with $R_i\to\kappa_i$ give a cocone on the $R_i$, hence a unique $b:R\to S$. It kills $M$, because $b(\alpha_i(x))=b_i([x])=0$ for $x\in\mathfrak m_i$, so it factors uniquely through $\kappa$. Conversely any map from $\kappa$ with the required composites must induce that same $b$ after the surjection $R\to\kappa$. This proves $\kappa=\varinjlim_i\kappa_i$ in commutative rings, with the stated $\rho_i$.

Uses: def-weil-pbc-category-colimit

### Old step 4 → lem-sfb-separably-closed-field-colimit

Let $p\in\kappa[T]$ be nonconstant and separable. By [def-pc-separable-polynomial], choose $U,V\in\kappa[T]$ with $Up+Vp'=1$. Apply [lemma-nagata-filtered-colimit-finite-data] to the directed colimit of step 3: descend the finitely many coefficients of $p,U,V$ and the finitely many coefficient equations of this identity to one $\kappa_i$. Taking zero coefficients outside their chosen finite degree bounds gives polynomials $p_i,U_i,V_i$ with $U_ip_i+V_ip_i'=1$, since differentiation has coefficients $n c_n$ and hence commutes with the coefficient maps. A nonzero positive-degree coefficient of $p$ has a nonzero lift, so $p_i$ is nonconstant; the displayed identity makes it separable. The residue field $\kappa_i$ is separably closed by strict henselianity [def-weil-pbc-henselian-terminology]. By [def-pc-separably-closed], choose $c_i\in\kappa_i$ with $p_i(c_i)=0$. Applying $\rho_i$ gives $p(\rho_i(c_i))=0$. Thus $\kappa$ is separably closed by the same definition.

Uses: def-pc-separable-polynomial, lemma-nagata-filtered-colimit-finite-data, def-weil-pbc-henselian-terminology, def-pc-separably-closed

### Old step 5 → lem-sfb-henselian-colimit-stage-root

Now let $f\in R[T]$ be monic of degree $n$, and let $a_0\in\kappa$ satisfy $\overline f(a_0)=0$ and $\overline{f'}(a_0)\ne0$. Use [lemma-nagata-filtered-colimit-finite-data] for $R$ to lift the finitely many coefficients below degree $n$ to some stage; form the lift with leading term exactly $T^n$. By [lem-pc-filtered-colimit-commrings-elementwise] for the colimit of step 3, lift $a_0$ to some $a_{0,j}\in\kappa_j$. Move both choices to a common upper bound $i$. This gives a monic $f_i\in R_i[T]$ mapping to $f$ and $a_{0,i}\in\kappa_i$ with $\rho_i(a_{0,i})=a_0$.

Uses: lemma-nagata-filtered-colimit-finite-data, lem-pc-filtered-colimit-commrings-elementwise

### Old step 6 → lem-sfb-henselian-colimit-stage-root

The coefficient formulas for evaluation and differentiation, and $\rho_i([x])=[\alpha_i(x)]$, give $\rho_i(\overline{f_i}(a_{0,i}))=\overline f(a_0)=0$ and $\rho_i(\overline{f_i'}(a_{0,i}))=\overline{f'}(a_0)\ne0$. Injectivity of $\rho_i$ from step 3 gives $\overline{f_i}(a_{0,i})=0$; the second equality gives $\overline{f_i'}(a_{0,i})\ne0$. The ring $R_i$ is henselian by [def-weil-pbc-henselian-terminology], so implication (i)$\Rightarrow$(ii) of [lem-weil-pbc-henselian-local-root-lifting] supplies $a_i\in R_i$ with $f_i(a_i)=0$ and $[a_i]=a_{0,i}$. For $a=\alpha_i(a_i)$, applying the ring map to the finite evaluation sum gives $f(a)=\alpha_i(f_i(a_i))=0$, and reduction gives $[a]=\rho_i([a_i])=a_0$.

Uses: def-weil-pbc-henselian-terminology, lem-weil-pbc-henselian-local-root-lifting

### Old step 7 → parent assembly (step 4)

We have proved the monic simple-root lifting condition for the local ring $R$. Implication (ii)$\Rightarrow$(i) of [lem-weil-pbc-henselian-local-root-lifting] makes $R$ henselian in the idempotent-lifting convention. Its residue field is separably closed by step 4. Therefore $R$ is strictly henselian by [def-weil-pbc-henselian-terminology].

Uses: lem-weil-pbc-henselian-local-root-lifting, def-weil-pbc-henselian-terminology

## Unfinished work

The three new lemmas intentionally remain unsplit for other workers. No mathematical obstruction or statement dispute was found. Required server checks and delivery are run after writing this report; their results are appended below.

## Validation

The prescribed deliver.py --no-push completed with exit 0 and printed OK (not pushed) at a24cc5143af: preflight passed. This ran the maintainer's preflight including check_dag.py and review_split.py on the server; neither checker was run locally. The final packet is rechecked after this validation note, then pushed by the same prescribed delivery tool.


## Repair of the live-DAG landing refusal

The supplied return was a landing-state refusal after mathematical approval: the side completion had not been promoted to the live queue DAG. The retained packet's last dry-run receipt records head 1cf47d91341; no interrupted deliver.py process remains. I did not discard the prior re-split or re-push it unchanged. The first resumed prescribed dry run rebased the packet against the current server state and stopped before push on three new same-04GI comparisons with lem-sfb-finite-contractible-diagram-localizations. I read that node, added each required nonduplicate explanation, and compared the retained item with the current repository. All non-stage-1 fields match the current item. Every cited current statement has been reread and its exact quote checked; no citation repair or statement change was necessary. The three new nodes remain unsplit, and the assembly totals 1546 characters (all steps below 2000), satisfying the current released repair order's at-least-two-nodes and at-most-3000-characters requirements. The prescribed delivery tool rebuilds on its current server DAG; no git command is run in the shared repository. Further dry-run results replace the earlier validation as the evidence for this repaired packet.


## Final landing-refusal retry, 2026-10-22

The retained packet and its durable receipt were present on arrival. As required, I ran the prescribed dry run before editing; it completed successfully at 488d402da4f. This is the current retry's evidence, superseding the older receipts described above. The tool builds the delivery on its current server DAG; I ran no git command and made no repository or launcher changes. The landing refusal concerned side/live completion state, not a failed mathematical review; promoting that completion remains the maintainer's landing operation.

I compared the retained item with the current read-only DAG: statement, statement dependencies, blueprint provenance, creation record, tool uses, Lean record, and both maintainer review records agree. The only differences before this retry were proof, proof dependencies, proof origin and split report. None of the three helper ids exists in the current DAG. Every current cited statement was opened again: the henselian definition still uses idempotent lifting; the root criterion still supplies exactly the equivalence required in step 4; the colimit and separable-field definitions are unchanged in meaning and all seven recorded quotations remain literal substrings. No changed cited statement forces a replacement dependency.

I reread Stacks 04GI (algebra.tex, lemma-colimit-henselian) and 04GF (definition-henselian), and the current finite-contractible-diagram-localizations statement. The three existing same-tag distinctions above still hold. I reread the logged search results and the actual residue-field map, henselian TFAE and algebraic-extension separable-closedness signatures: none adds the missing permanence or descent assertion, and no new search question arises. A full WeilConjectures source search for the item tag and the colimit/strict-henselian and separably-closed combinations found no completed attachment. The Sheaf theorem remains explicitly sorry.

For this final packet I clarified assembly step 3: it now explicitly lists the same-degree monic polynomial, residue representative and stage solution supplied by the stage-root node, and identifies the residue formula as coming from step 1. This makes the exact uses visible without introducing a new result. Steps 1, 2 and 4, all three helper statements, citations and recorded searches are retained. The previously recorded singleton, noninjective dual-number quotient, transcendental field extension and constant-monic-polynomial checks still apply. The assembly remains below 3000 characters and every step below 2000. This updated review and explicit witness assembly replace an unchanged re-push; final server validation and push follow.
