# Worker report — Q107

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-functorial-log-blowup-etale-descent.json`: item, unchanged statement; five-step assembly, 2534 characters.
- `dag/nodes/sec-trace-formula/lem-trf-finite-fan-chart-cech-cover.json`: statement-only lemma, status `unsplit`, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-log-tower-cover-synchronization.json`: statement-only lemma, status `unsplit`, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-log-tower-effective-center-descent.json`: statement-only lemma, status `unsplit`, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-log-tower-cover-rigidity.json`: statement-only lemma, status `unsplit`, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-log-tower-contraction-descent.json`: statement-only lemma, status `unsplit`, no Mathlib match.
- `citations.json`: verbatim statement excerpts for every citation in the parent proof.
- `report.md`: repair and source review, including the complete previous argument below.
- `searches.jsonl`, `*.search.txt`, `search_plan.json`: actual search log and saved results, retained for audit. `repair.py` and `write_report.py` are sandbox-only preparation scripts, not delivery files.

## Attachments

None. Searched `lean/WeilConjectures/` by the blueprint tag and logarithmic-blowup/fan-chart concepts. No matching project declaration occurs. Read `lean/Sheaf/AlgebraicGeometry/FunctorialLogBlowupEtaleDescent.lean` (theorem at line 81): the displayed theorem has `sorry` at line 92, so it is not an attachment. Its ten-paragraph docstring agrees with the old natural-language proof. No Lean file was written and no compiler, Lake, or build tool was run.

## WANTED

None. The ILO PDF and Stacks TeX sources used below are present.

## What was wrong and what changed

The 2026-10-22 return requires the 10208-character proof to be distributed across at least three comparable new statement-only nodes, with an assembly of at most 3000 characters. This repair introduces five independent lemmas; their eventual proof workloads comprise old steps (2,3), (1,4,5), (6,7), (8,10), and (9), respectively. None states extension of a rule to all inputs. The parent now constructs the extension by assembling finite-cover existence, synchronized descent data, effective center descent, rigidity, and contraction descent. Its statement, original source, existing Lean record, chapter and unit are unchanged.

The sandbox contained only dispatcher marker files, with no node, report or search log to recover. The initial required `deliver.py --no-push` exited with “no node files”. I copied the current live node, which contains exactly the ten returned proof steps (705, 1082, 969, 800, 832, 1429, 1076, 1028, 1287, 1000 characters), and retained its argument below. This is a substantive re-split, not a rebase-only delivery.

## Return repair, point by point

1. Spread the work: five new lemmas, all `unsplit`, with complete self-contained statements, sources, recorded LeanFinder, LeanSearch, Loogle and grep searches, and empty `proof`/`proof_deps`. The workloads are approximately 2051, 2337, 2505, 2028, 1287 characters of the old proof, respectively; the shorter final lemma carries the non-surjective contraction argument.
2. Short assembly: five parent steps, 2534 text characters altogether. Each invokes precise conclusions of the new lemmas rather than hiding the old arguments in shortened prose.
3. Retain every argument: the next section maps and reproduces all ten old steps, including empty input, proper principal centers, stagewise scheme base changes, actual-ideal descent formula, coherence, cover independence, consecutive deletions, identity/composition, and natural uniqueness.
4. Keep the statement: checked byte-for-byte equality with the live parent statement. No statement dispute or correction was needed.

## Promotion-return repair (2026-10-22)

The present return names approved head `7e046ef2783` and reports that its side completion was never promoted to the live queue DAG. I retained its five node files, original proof assignment, citations, report and actual search results. The first required dry run in this retry succeeded at `0943c8019a3`; the unmodified delivery tool resolves the current `origin/sheaf-dag` and overlays only stage-1-owned fields, so the new commit is based on the current DAG rather than the returned branch.

I compared every retained node with the current shared snapshot. The five proposed supporting nodes are absent there. For the parent, only `proof`, `proof_deps` and `split_report` differed: the live snapshot still carries the ten original steps, with lengths 705, 1082, 969, 800, 832, 1429, 1076, 1028, 1287 and 1000. Its statement, statement dependencies, source, blueprint ancestry, chapter, unit and Lean metadata agree. The released stage-1 repair note explicitly requires this re-split even though that old parent is marked split. I do not claim the current snapshot is an archive of the returned commit; the retained sandbox and the return entry are the returned-work record.

This retry also changes the proof, not only its base: assembly step 3 now states that the common refinement covers both chart covers, applies synchronization to detect proper centers and exclude deletions, and only then identifies the two full towers with the prescribed tower on the refinement. Its citation excerpt now quotes synchronization's precise no-deletion clause. The other four steps and all five supporting statements are retained. No search question or new-node statement changed, so I read and reused all saved searches instead of repeating them.

## Continued promotion repair (2026-10-22)

The resumed dispatch retains the same promotion-return order. Before any edit I ran the required dry run to completion: `OK (not pushed)` at `ec7a1fe543c`. Comparing the six retained files with the current shared DAG again showed that the five supporting ids are absent and only the parent's proof, proof dependencies and split report differ. The source statement, statement dependencies, original source and blueprint ancestry, and existing Lean records still agree. The released stage-1 re-split order remains in force. The earlier heads recorded above are historical retry results, not evidence that this retry has been pushed.

I reread all five supporting statements and every current statement dependency, together with all original proof dependency statements. This covers any changed cited node without relying on an old dependency hash. The only project theorem found remains sorried, and there is no attachment in `WeilConjectures/`. I reread the ILO source on printed pages 107--110 and Stacks 04TQ/04TR in sites.tex, and read the saved raw search results and their log; the five statements and search questions are unchanged, so no search was repeated or invented.

This retry makes a further substantive clarification in assembly step 4. For composable strict etale maps Z to Y to X, use W_Y = Y times_X U and W_Z = Z times_X U, both charted admissible covers by the finite-cover statement. The original procedure's composition law applies on W_Z to W_Y to U. The contraction-descent statement explicitly tests both retained index maps and actual log morphisms after W_Z to Z, so it yields the global composition law; identities are the case f = identity. This supplies an explicit diagram for the compatibility asserted by the retained proof. Every step-4 citation remains verbatim and supplies exactly these two inputs. The parent statement and the five new statements are preserved.

I also inspected current neighboring results on strict logarithmic Cartesian blowups, smooth tower synchronization, fan affine-lift descent, fan refinement comparisons and ordinary Zariski resolution descent. They concern a single blowup, fans/monoschemes, or ordinary resolution over Q; none gives this finite-tower strict etale descent for log schemes. The shared DAG is read only; only the unmodified delivery tool performs the rebase and creates the deliverable commit. The final dry run is required after this clarification and report update, before the direct push.

## Current promotion repair and review by Q107 (2026-10-23)

The current return entry identifies approved head `0def5fb3945`. No earlier push or dry-run receipt is treated as completion. I first ran the required unmodified delivery dry run with the retained sandbox; it exited successfully at `1febe940b45`. The delivery tool prepares a new commit on its current server base. The shared snapshot still has the ten-step parent and none of the five supporting ids. Comparing the retained parent to that snapshot shows only proof, proof_deps and split_report differences; the statement and all statement dependencies, source, blueprint, chapter, unit, audit and Lean metadata agree. The released stage-1 repair order remains active, so the old reviewed record does not supersede this requested split.

I read the five cited supporting statements in full, every current statement dependency, and all fifteen statements cited by the original proof. In particular the fan-chart lemma still supplies the finite chart neighborhoods, the procedure definition still includes identities/composition and actual-center comparisons, and the coherent-ideal chart-construction lemma still supplies saturated blowups and strict etale restriction. I reread ILO VIII 3.3.4 and 3.3.7–3.3.15 on printed pages 107–110, together with Stacks 04TQ/04TR at sites.tex:5638/5848. These sources agree with the retained statements and the preserved old arguments. The project theorem still ends in sorry and the search in WeilConjectures yields no attachment.

I made one mathematical clarification in assembly step 3: after comparing the full towers on W = U times_X V through T(W), I now explicitly check compatibility with the two descent data on W times_X W using the original rule's composition law. Thus cover rigidity is applied to the descended data, not merely to an unexplained identification. W is charted admissible and covers X, and its double overlap is charted admissible by the cover lemma, so every invocation of the original rule has its hypotheses. No supporting statement or search question changed. The saved searches and raw hits were read and retained, with no invented or repeated query.

I checked each parent's citation against its actual statement: step 1 gets an admissible finite cover and the synchronized center-preserving cocycle; step 2 gets effectivity, the full length and proper descended ideals; step 3 gets common refinements, no deletion and unique cover comparisons; step 4 gets charted W_Y and W_Z and the contraction theorem's testing of actual maps and retained indices; step 5 gets no further deletion on a cover and rigidity/naturality. Every citation in citations.json is still a verbatim substring of that statement and every uses occurrence has an entry. Empty inputs and zero-length towers remain allowed, proper principal centers are retained, and no non-surjective map is used to detect whole centers. The original ten arguments remain verbatim below. All five new nodes remain statement-only and none states the extension theorem. The assembly remains below 3000 characters, with each step below 2000. Final validation and direct push follow this report update.

## Source and route

Read ILO, *Travaux de Gabber*, Expose VIII, printed pp.107–110 (PDF pages 113–116), especially 3.3.4(ii), 3.3.7–3.3.13, and the entire proof of 3.3.15. The first sentence of that proof reduces by descent to globally fan-charted inputs. Its last paragraph uses a finite disjoint union to compare towers. The chart construction and compatibility with strict morphisms are in 3.3.8; saturated towers and recursive pullback in 3.3.9–3.3.11; fan chart pullback in 3.3.12–3.3.13. These are the sources for all five new statements. They make the implicit descent assertion precise; the detailed arguments remain agent expansions, not claims that ILO prints these five lemmas verbatim.

Also read Stacks `sites.tex`, Tag 04TQ, `lemma-glue-maps` (line 5638), and Tag 04TR, `lemma-glue-sheaves` (line 5848), with its preceding descent datum and sectionwise construction. The existing `lem-pe-set-sheaf-cover-descent` states both required results, with the small-site/universe hypotheses, whereas mere Yoneda or a definition of sheafification would not. Read the statements of all old proof dependencies, including `lem-weil-pbc-etale-site-localization-open`, `lem-trf-coherent-log-ideal-chart-construction`, and `lem-weil-pbc-qcqs-morphism-permanence`; the preserved argument below specifies where they belong when the new nodes are split later. These are not falsely recorded as proof dependencies on the new, unsplit nodes.

Read the current chapter and unit records (`sec-trace-formula`, `sk-i-curve-zero`) and the current main-20261015 ancestor `lem-trf-local-term-locality`. This is a historical nearby-duality/alteration branch through monoidal resolution; I preserve the recorded route and do not replace the current contracting-correspondence unit argument. `blueprint_refs.py ancestor` returns `lem-trf-local-term-locality`. Every new node carries that ancestor with the parent prepended to `via`, and gives the exact old proof steps and ILO descent passage in `from.place`.

## Search review

Before writing any new node I searched the entire DAG for logarithmic blowups, fan charts, surjective strict maps, contracted towers, synchronization, centers and descent, and for source locations. I read the relevant existing statements listed under Not duplicates. Whole-blueprint searches for `log blowup`, `coherent log ideal`, `tower descent`, `fan chart`, `logarithmic`, and `contraction` produced no matching logarithmic-tower descent theorem; further per-argument searches are recorded by their literal phrases in the review below.

For each new id, `search_plan.json` gives two distinct natural-language phrasings, a Loogle query and a grep pattern. All were run through the required unmodified `msearch.py`; the raw responses are in the corresponding `<id>.search.txt`, and each node embeds the results exactly with assessment and verdict. Both semantic services and Loogle were available. There were no matching logarithmic scheme/tower declarations.

The nearest finite-cover hits, `AlgebraicGeometry.QuasiCompactCover.of_finite` and its pullback instances in `Mathlib/AlgebraicGeometry/Cover/QuasiCompact.lean`, concern ordinary covers, not global logarithmic fan charts or torsion-free characteristic monoids. The rigidity hit `Scheme.IdealSheafData.ext_of_iSup_eq_top`, read at `Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:268`, is for ordinary ring ideal sheaves on affine Zariski covers; our ideals are subobjects of an etale monoid log sheaf. The one Loogle descent hit, `Pseudofunctor.DescentData.subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv`, read at `Mathlib/CategoryTheory/Sites/Descent/DescentData.lean:462`, identifies two descriptions of a morphism in abstract descent data. It supplies neither effectivity for centers nor existence of the log blowup tower. Effective-epimorphism and etale-ring hits likewise do not provide these logarithmic conclusions. Grep hits for logarithmic derivatives and coherent monoidal condensed sheaves were unrelated. Consequently all five nodes remain unsplit, with no claimed Mathlib leaf.

## Not duplicates

lem-trf-finite-fan-chart-cech-cover vs lem-trf-log-fan-chart-blowup: the existing lemma gives individual chart neighborhoods and pullback of fan towers; the new lemma packages a finite disjoint-union charted input and admissibility of all Cech products, common refinements and arbitrary strict etale tests.

lem-trf-finite-fan-chart-cech-cover vs lem-weil-pbc-finite-coproduct-lfp-qcqs: the existing result concerns ordinary scheme coproducts; the new result concerns global fan charts, characteristic groups and charted refinements.

lem-trf-log-tower-cover-synchronization vs def-trf-strict-etale-log-blowup-procedure: the existing node defines the data; the new lemma proves contraction detection on covers and constructs the synchronized uncontracted Cech datum.

lem-trf-log-tower-cover-synchronization vs lem-trf-coherent-log-ideal-chart-construction: the existing result constructs one saturated blowup; it does not identify retained indices or give a Cech datum for an assigned finite tower.

lem-trf-log-tower-effective-center-descent vs lem-trf-coherent-log-ideal-chart-construction: the existing result descends one chartwise blowup along an already specified global ideal; the new lemma descends actual ideal centers at each unknown intermediate level of an arbitrary ordered tower.

lem-trf-log-tower-effective-center-descent vs lem-pe-set-sheaf-cover-descent: the existing result gives gluing of set sheaves and maps; the new lemma additionally gives ideal stability, nonempty coherence, the stagewise scheme identifications and the length-preserving saturated blowup tower.

lem-trf-log-tower-effective-center-descent vs lem-trf-fine-log-structure-etale-descent: the existing node descends log structures on an already specified scheme; the new lemma constructs successive schemes from descended ideal centers.

lem-trf-log-tower-effective-center-descent vs lem-trf-polarized-fine-log-etale-descent: the existing node needs relatively ample line bundles on a general log-scheme descent datum; the new lemma uses universal blowups and actual ideal centers without a supplied polarization.

lem-trf-log-tower-cover-rigidity vs lem-trf-strict-fan-chart-local-comparison: the existing result compares fan charts by local fan isomorphisms; it does not assert uniqueness or descent of an ordered log tower isomorphism.

lem-trf-log-tower-cover-rigidity vs lem-trf-log-blowup-normalization: the existing result identifies a single blowup with a normalization under log-regular integral hypotheses; it does not prove tower rigidity for arbitrary locally Noetherian fs bases.

lem-trf-log-tower-contraction-descent vs def-trf-strict-etale-log-blowup-procedure: the definition specifies contraction comparisons but does not establish their descent, exact retained-index detection or local testing of their equations.

lem-trf-finite-fan-chart-cech-cover vs lem-trf-functorial-log-blowup-etale-descent: the new statement is only one input lemma (cover construction, synchronization, effectivity, rigidity or contraction testing) and does not extend a rule or assert the parent theorem.

lem-trf-log-tower-cover-synchronization vs lem-trf-functorial-log-blowup-etale-descent: the new statement is only one input lemma (cover construction, synchronization, effectivity, rigidity or contraction testing) and does not extend a rule or assert the parent theorem.

lem-trf-log-tower-effective-center-descent vs lem-trf-functorial-log-blowup-etale-descent: the new statement is only one input lemma (cover construction, synchronization, effectivity, rigidity or contraction testing) and does not extend a rule or assert the parent theorem.

lem-trf-log-tower-cover-rigidity vs lem-trf-functorial-log-blowup-etale-descent: the new statement is only one input lemma (cover construction, synchronization, effectivity, rigidity or contraction testing) and does not extend a rule or assert the parent theorem.

lem-trf-log-tower-contraction-descent vs lem-trf-functorial-log-blowup-etale-descent: the new statement is only one input lemma (cover construction, synchronization, effectivity, rigidity or contraction testing) and does not extend a rule or assert the parent theorem.

## Review by Q107

For this promotion repair I reread all five cited supporting statements and every current definition or notion in their statement dependencies: fs log schemes and universal saturated blowups, strict morphisms and fan charts, admissible charted procedures and their retained index maps, etale morphisms, scheme fiber products and coproducts, locally Noetherian schemes, the sheaf equalizer condition, and the universe convention. Their hypotheses remain compatible with the retained parent. I reread ILO VIII 3.3.4(ii), 3.3.7--3.3.15 and Stacks sites.tex lemma-glue-maps/lemma-glue-sheaves. The source deletes whole monoid ideals only; it does not delete proper principal centers, and strict base change identifies the induced covering schemes at each stage. In the amended step 3 the maps W to U and V are surjective, so the no-deletion clause applies; step 4 still assumes surjectivity only of W to Y, never of the arbitrary f. The parent proof remains below 3000 characters and no step reaches 2000. I verified every citations.json excerpt is a literal substring of the corresponding statement and every cited step/node pair has exactly one entry. The current report records the promotion return separately from the earlier mathematical re-split, so its accepted argument and searches are not mistaken for new work.

I checked the source with the actual node statements open, not only their ids. For finite covers, ILO 3.3.4(ii) supplies local charts and the final paragraph of 3.3.15 supplies the finite-union device. The new cover statement includes quasi-compact sources, double and triple overlaps, common refinements and strict etale test pullbacks. Local Noetherianity gives quasi-separatedness; the old permanence lemma explicitly has the source-qc/target-qs implication, base change, and qc source over qc base. Thus no intersection of arbitrary affine opens is assumed affine and no finite-type base hypothesis is introduced. Strictness identifies the pulled characteristic stalks; composing with a fan chart gives the global chart on the pullback. Empty schemes and empty fans are allowed.

For synchronization, I checked ILO's definition of contraction in 3.3.8 and the recursive pullback in 3.3.10. It deletes whole monoid ideals, not all isomorphic blowups: a proper principal monoid ideal is retained. Identity comparison forces each assigned tower to be contracted; over the empty scheme every ideal is whole. The two projections of the cover's entire Cech overlap are surjective, unlike projections of individual pairwise chart pieces. At every level strict restriction commutes with the actual chart blowup, so the map is an ordinary scheme base change of the covering map. Surjectivity of blowup maps is never used. The ideal sheaf equalizer detects a whole ideal, and the original identity/composition laws then give the same ordered index set and center-preserving cocycle on the triple overlap.

For effective descent, ILO 3.3.7 is the definition of coherence as etale-locally nonempty finite monoid generation, and 3.3.8–3.3.10 supplies the blowup universal property. Stacks 04TR/04TQ glues the sheaf and its inclusion on the localized small site. Injection and ideal stability follow after the cover, the displayed section formula fixes the descended ideal uniquely, and the same local generators establish coherence and nonemptiness. The induction starts with X_0=X and U_0=U and constructs the next universal blowup from I_i; strict restriction identifies it with the specified U_{i+1}. All n stages are retained; properness is detected by the restriction. The new statement records these exact inductive invariants, rather than only an abstract assertion that a tower descends.

For rigidity I read the uniqueness part of the ILO descent reduction alongside the original steps 8 and 10. Equality of subideals is a sheaf-local statement. Once the first ideals agree, the universal property forces the first isomorphism over X, and the same argument applies to each next center. It proves uniqueness with actual centers, even for proper principal blowups. The statement requires an uncontracted ordered isomorphism on a surjective cover, so it neither discards multiplicities of identity stages nor compares unrelated lengths. Common-refinement comparison is consequently valid, gives the cover-choice cocycle, and handles the identity cover.

For contraction descent I checked 3.3.8–3.3.11 and old step 9. Surjectivity is assumed only for W→Y; f:Y→X can be a component inclusion or an empty map. Whole-center detection occurs at each repeated, uncontracted level. Deleted transitions are canonical identities, so later centers are carried across them; this explicitly covers several successive deletions. The local surviving index set is exactly the global one. After contraction the center-preserving local isomorphism descends by rigidity, and equations of count maps and actual log morphisms can be tested on the induced covering stages. No word 'transports' stands for an unrecorded compatibility argument.

Parent citation audit (the quotes are in citations.json): step 1 uses the finite-cover lemma's existence and overlap conclusions and the synchronization lemma's contractedness/Cech datum. All quasi-compact, locally Noetherian, fs and torsion-free hypotheses are precisely the parent's. Step 2 uses the effective-descent conclusion with the cocycle just obtained, not a definition of descent. Step 3 uses the common-refinement clause, synchronization of the original comparisons, and rigidity's unique common-cover isomorphism and identity-cover assertion. Step 4 uses the cover lemma for W and the contraction-descent statement for C(f*E(X))≅E(Y), with its exact-index and equation-testing clauses; the original rule comparison is legitimate because W and U are charted admissible. Step 5 uses synchronization on the surjective cover, rigidity for uniqueness with centers, and contraction descent to check naturality. All steps are marked non-elementary because they apply these theorems. The residual assembly is choice, substitution and composition of the stated isomorphisms; no hidden geometric lemma remains in a parent step.

Small-case checks: n=0 gives the empty tower at every construction; on X empty a contracted tower must have n=0. A proper principal ideal in the standard monoid N gives an identity blowup whose stage is retained. A disconnected cover of two components must use the single tower on their coproduct; comparing individual non-surjective overlaps would be wrong. A proper open immersion Y→X can turn a proper global center into a whole center, so only W→Y, not f, is used for no-deletion. Several consecutive whole centers give repeated identity levels with exactly the stated surviving indices. Non-log-regular or non-integral bases are permitted: no normalization or log-regular theorem is used.

B–E checks: all five statements introduce their own objects and cite the definitions of the notions they use; they contain no proof sketches or proof steps. TeX is stored with one decoded backslash. None is elementary, a parent clause, or a duplicate of the existing node inspected above. The three required kinds of Mathlib searches were really run, including second semantic phrasings, with original results retained. New statement dependencies contain no reference back to the item. The parent proof is 2534 characters, and no individual step exceeds 2000 characters. The new nodes carry complete blueprint ancestry, explicit source places, and the original detailed arguments assigned below. There is no SGA citation, unit change, statement weakening, or new hollow definition. The report keeps the original generic tool inputs visible for future splits; the parent itself now cites only the five same-unit lemmas.

## Preserved original arguments, assigned to the new nodes

These are work instructions for the next workers, not proof steps attached to the new statement-only JSON nodes. The text is retained verbatim from the returned live head, together with every original citation and source, so no argument is lost by making the parent assembly short.

### lem-trf-finite-fan-chart-cech-cover

Old step 2 (1082 characters):

For nonempty $(X,M)$ choose the finite strict etale chart cover $u_a:U_a\to X$ supplied by [lem-trf-log-fan-chart-blowup](i). Put $U=\coprod_a U_a$, with log structure and chart obtained componentwise, and $u:U\to X$. The coproduct lemma supplies disjoint open-and-closed components; its finite-coproduct consequence gives quasi-compactness. A disjoint union of the target fans, with its componentwise monoid sheaf, is a fine fan by the local definition, and the componentwise characteristic isomorphisms make $U$ globally fan-charted. The log scheme is locally Noetherian because its components are, and its characteristic stalks are their stalks. The map $u$ is strict, surjective and etale: on each disjoint open component it is $u_a$, and the affine-local definition of etaleness is exactly the definition there. Thus the given rule, including its finite-union compatibility, supplies one finite contracted tower $S=\mathcal T(U)$ of length $n$, with ordered centers $J_i\subset M_{U_i}$ for $0\leq i<n$. We use this single tower, not separate orderings of the component towers.

Original uses: lem-trf-log-fan-chart-blowup, lem-weil-pbc-scheme-coproduct-family, lem-weil-pbc-finite-coproduct-lfp-qcqs, def-trf-fine-fan-blowup, def-weil-etale-morphism.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VIII, proof of Theorem 3.3.15, printed pp.109--110; descent details expanded.

Old step 3 (969 characters):

The overlap $R=U\times_XU$ and the triple overlap are legitimate inputs for the rule. Indeed $X$ is quasi-separated by the locally-Noetherian lemma. Since $U$ is quasi-compact, $u$ is quasi-compact by the permanence lemma; its base changes and their sources over a quasi-compact base are quasi-compact by that same lemma. Apply this successively for double and triple overlaps. Their projections are strict etale and surjective by etale-cover base change. They are locally Noetherian by [pqf-lem-locnoeth-lft], since etale morphisms are locally of finite type. The strict pullback assertion of the fan-chart lemma supplies global fan charts from $U$, and strictness identifies their characteristic stalks with those upstairs on $U$. Thus these overlaps are fs with torsion-free characteristic groups. The same reasoning applies to common refinements of any two such finite chart covers, and to $Y\times_XU$ when $Y\to X$ is strict etale with $Y$ in the indicated class.

Original uses: lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-etale-covering-base-change, pqf-lem-locnoeth-lft, def-weil-etale-morphism, lem-trf-log-fan-chart-blowup.

Source: literature/stacks-project/schemes.tex; Tags 03GI (lemma-quasi-compact-permanence), 01K5 (lemma-quasi-compact-preserved-base-change); properties.tex Tag 01OY; morphisms.tex Tags 01T6, 02GO, 01S1; ILO VIII 3.3.12--3.3.13.

### lem-trf-log-tower-cover-synchronization

Old step 1 (705 characters):

First note that every assigned tower is contracted. Apply the assumed comparison to the identity of a charted log scheme: a finite ordered tower is isomorphic, with its centers, to its own contraction only if no stage was deleted. Whole-monoid centers give identity morphisms, since their pullbacks are generated by the unit under every fs log morphism, so the identity has the defining blowup universal property. Only whole-monoid centers are deleted: a proper principal ideal is retained even though its blowup is an isomorphism. On the empty scheme every ideal sheaf is the whole monoid sheaf, so the assigned contracted tower has length zero. Define the extension on the empty scheme to be this tower.

Original uses: def-trf-fs-log-blowup.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VIII 3.3.8--3.3.10, contraction and universal properties; identity comparison hypothesis.

Old step 4 (800 characters):

Here is the stagewise cover check used below. Pull a finite log blowup tower back along a surjective strict etale map $A\to B$. The log-ideal construction commutes with strict etale restriction, so at each stage $A_i\to B_i$ is the scheme-theoretic base change of $A\to B$ and is again a surjective strict etale cover. For an ideal $I_i\subset M_{B_i}$, its restriction is the whole monoid sheaf if and only if $I_i=M_{B_i}$: if the restriction is whole, every local section of $M_{B_i}$ belongs to $I_i$ after the cover, and the sheaf condition for the subsheaf $I_i$ glues its local representatives. The reverse implication is immediate. Consequently a surjective strict etale pullback deletes no stages of a contracted tower. This argument needs no surjectivity of the blowup morphisms themselves.

Original uses: lem-trf-coherent-log-ideal-chart-construction, lem-weil-pbc-etale-covering-base-change, def-weil-pbc-etale-sheaf-of-sets.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VIII 3.3.8--3.3.10; sites.tex Tag 00VM (definition-sheaf-sets); morphisms.tex Tags 02GO and 01S1.

Old step 5 (832 characters):

Apply the assumed comparisons to both projections $p_1,p_2:R\to U$. By Step 4 neither pullback of $S$ loses a stage, so both are uncontracted towers of length $n$, canonically identified with $\mathcal T(R)$. Composing one identification with the inverse of the other gives an isomorphism $p_1^*S\simeq p_2^*S$ of ordered towers with centers over $R$. In particular corresponding centers, on the identified levels, are equal as subideals of the same log structure. On triple overlaps the two composite identifications equal the direct one: all three are the comparisons with $\mathcal T(U\times_XU\times_XU)$ prescribed by the composition hypothesis. The diagonal comparison is the identity by the identity hypothesis. This gives a descent datum for every stage, including its actual ideal, with one common index set $0,\ldots,n-1$.

Original uses: none (elementary comparison of the assumed functorial identifications).

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VIII, proof of Theorem 3.3.15, printed pp.109--110; descent details expanded.

### lem-trf-log-tower-effective-center-descent

Old step 6 (1429 characters):

We descend the centers inductively, retaining this index set. Suppose that $X_i$ has been constructed and that $U_i\simeq U\times_XX_i$, with the overlap identifications of Step 5 identifying $R_i$ with $U_i\times_{X_i}U_i$; initially this is $X_0=X$. Strictness identifies $M_{U_i}$ with the restriction of $M_i$ on the localized etale site. The equalities of centers on $R_i$ therefore make the sheaf $J_i$ into a sheaf descent datum on the covering $U_i\to X_i$. Use the small-site and universe convention [def-weil-size-convention], with all covering objects and the displayed finite fiber products in its chosen universe. The set-sheaf cover-descent lemma glues it to a sheaf $I_i$ and glues its inclusions into $M_i$. This map is injective: sections with the same image agree after the cover because each local inclusion is injective, and hence agree by the sheaf condition. Identify $I_i$ with its image in $M_i$. Explicitly, for etale $W\to X_i$, its sections are precisely the $m\in M_i(W)$ whose restrictions to $W\times_{X_i}U_i$ belong to $J_i$. This also proves uniqueness as a subobject. Stability under multiplication by $M_i$ is checked after this cover and follows from ideal stability for $J_i$. Nonemptiness and coherence hold because the same etale-local finite nonempty monoid generators that define $J_i$ define the restriction of $I_i$; these are local conditions in the definition of a coherent log ideal.

Original uses: lem-pe-set-sheaf-cover-descent, lem-weil-pbc-etale-site-localization-open, def-weil-pbc-etale-sheaf-of-sets, def-trf-fs-log-blowup, def-weil-size-convention.

Source: literature/stacks-project/sites.tex; Tags 04TR (lemma-glue-sheaves), 04TQ (lemma-glue-maps); ILO VIII 3.3.7 for coherent log ideals.

Old step 7 (1076 characters):

Apply [lem-trf-coherent-log-ideal-chart-construction] to $(X_i,M_i)$ and $I_i$ to obtain the saturated log blowup $(X_{i+1},M_{i+1})$. Its hypotheses are exactly local Noetherianity, fs and a nonempty coherent log ideal, as established at the initial stage and Step 6; the output is again an fs log scheme in the locally-Noetherian convention of [def-trf-fs-log-blowup]. Strict etale restriction of this construction identifies its pullback on $U_i$ with the specified blowup along $J_i$, by the universal property. Hence $U_{i+1}\simeq U\times_XX_{i+1}$, and the identical assertion on double overlaps identifies the descended transition with the transition of Step 5. The cover-base-change lemma shows that $U_{i+1}\to X_{i+1}$ is a surjective etale cover. This completes the inductive step, so induction for $i=0,\ldots,n-1$ constructs the entire global tower. Each center $I_i$ is proper: if it were whole, its restriction $J_i$ would be whole, contrary to Step 1. Thus the tower is contracted and finite of length exactly $n$, and its uncontracted pullback to $U$ is $S$.

Original uses: lem-trf-coherent-log-ideal-chart-construction, def-trf-fs-log-blowup, lem-weil-pbc-etale-covering-base-change.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VIII 3.3.7--3.3.10, global chart construction and strict etale compatibility.

### lem-trf-log-tower-cover-rigidity

Old step 8 (1028 characters):

The construction is independent of the chosen finite chart cover. For two covers $U\to X$ and $V\to X$, the common refinement $W=U\times_XV$ has a global fan chart and is quasi-compact by Step 3. Both projections are surjective strict etale. Their comparisons identify $\mathcal T(W)$ with the full pullbacks of $\mathcal T(U)$ and $\mathcal T(V)$, without deleting stages by Step 4; in particular the two lengths agree. At stage zero the two descended centers agree because their restrictions to the common cover $W$ agree, by the sectionwise description of Step 6. Their universal blowups are therefore uniquely isomorphic over $X$. Repeating this at successive stages gives the canonical comparison of the entire towers with centers. The same argument proves its uniqueness and its cocycle identity on three choices: the centers are equal after their common covering and each blowup has a unique isomorphism over the preceding stage. Chart choices introduce no further choice because the prescribed rule is chart independent.

Original uses: def-trf-fs-log-blowup, def-weil-pbc-etale-sheaf-of-sets.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VIII, proof of Theorem 3.3.15, printed pp.109--110; descent details expanded.

Old step 10 (1000 characters):

If $X$ itself has a global fan chart, use the identity as its cover in the construction: all centers descend to themselves, and the result is canonically $\mathcal T(X)$. Step 9 consequently gives the prescribed contracted tower on every chart neighborhood of any $X$. Finally consider any extension with the asserted compatibilities. Contract its whole-monoid stages, which are identities by Step 1. Its pullback to the finite surjective chart cover $U\to X$ has no further deletions by Step 4, and is $\mathcal T(U)$. Its first center must be the unique subideal descending $J_0$ by the sectionwise formula of Step 6. The first blowup is then the universal one, uniquely isomorphic over $X$ to ours. Induction gives the same assertion at every remaining stage. Thus the two contracted towers, together with their centers, are canonically isomorphic, and these isomorphisms respect all strict etale comparisons by the same uniqueness. This proves the required uniqueness and completes the extension.

Original uses: def-trf-fs-log-blowup, def-weil-pbc-etale-sheaf-of-sets.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VIII, proof of Theorem 3.3.15, printed pp.109--110; descent details expanded.

### lem-trf-log-tower-contraction-descent

Old step 9 (1287 characters):

Let $f:(Y,N)\to(X,M)$ be strict etale between members of the indicated class, and let $U\to X$ be the cover above. The scheme $W=Y\times_XU$ is quasi-compact, locally Noetherian and globally fan-charted by Step 3, and $W\to Y$ is a surjective strict etale cover. On $W$ the pulled-back global tower is the pullback of $\mathcal T(U)$; its contraction is $\mathcal T(W)$ by the assumed comparison for $W\to U$. At every stage, a center on the tower over $Y$ is whole if and only if its restriction to the covering stage over $W$ is whole, by Step 4. Thus contraction over $Y$ deletes exactly the indices deleted over $W$, even if several consecutive indices are deleted. After a deleted index the transition is canonically the identity by Step 1, so subsequent centers correspond unchanged. The surviving centers descend from exactly those of $\mathcal T(W)$. Step 6 and the blowup universal property then identify the contracted pullback over $Y$ with the extension constructed using the single chart cover $W\to Y$. By Step 8 that is the extension on $Y$. These comparisons preserve centers and order. Their identity and composition laws hold after a chart cover by the original laws for the rule, and hence globally by uniqueness of the descended ideals and of their universal blowups.

Original uses: lem-trf-coherent-log-ideal-chart-construction, lem-weil-pbc-etale-covering-base-change, def-trf-fs-log-blowup.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VIII, proof of Theorem 3.3.15, printed pp.109--110; descent details expanded.

## What remains

The requested stage-1 split is complete in the sandbox: five statement-only nodes and the short parent assembly, with all original arguments preserved above. No mathematical correction is deferred. The initial retry dry run passed on the current server base; after the common-refinement clarification and report update, the final required dry run and direct push are run again. The maintainer independently reviews and promotes the delivered split.
