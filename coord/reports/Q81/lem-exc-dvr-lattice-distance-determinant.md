# Worker report: lem-exc-dvr-lattice-distance-determinant

Group Q81; stage 1; 2026-10-17. This is the first reading, for a fresh second reader. No delivery push is authorized for this worker.

## Files written

- `dag/nodes/sec-smooth-purity/lem-exc-dvr-lattice-distance-determinant.json`: statement node, now split into nine proof steps; not a Mathlib leaf. The statement, its five statement dependencies, and the inherited blueprint ancestry are unchanged.
- No new nodes and no new Mathlib leaves. Nine of the ten existing proof dependencies are Mathlib leaves; the remaining one is the existing Cauchy–Binet theorem.
- `citations.json`: one verbatim statement quote for each of the sixteen uses in the item's numbered steps.
- `report.md`: this report. `searches.jsonl` is the search command's real log; `write_split.py` is sandbox-only preparation material, not a delivered project file.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id, lattice/distance/determinant/valuation combinations, and lattice/Smith vocabulary; no declaration states the complete item. The master reference source likewise yielded no matching lattice-length/determinant theorem. Its sorry declarations would not count as finished proofs in any event.

## WANTED

None. All sources used are present locally.

## What needed repair

The imported item had a complete correct signed statement but no proof. Stacks Tag 02MI proves a more general statement over a one-dimensional Noetherian local domain using lattice distance and generators of GL. Citing that whole theorem as a new child would merely rename this item's content. Instead the nine steps prove its DVR case using the already existing Smith normal form leaf, a common sublattice, and explicit determinant and length computations. This is a choice below the unit level; it changes neither the Kummer unit's route nor its statement.

In particular, finite length of the two intersection quotients is proved, not assumed. Noetherianity is established before the nonzero-element factorization node is applied. No finite-generation assertion about the intersection is needed. The proof does not assume that the determinant valuation is nonnegative.

I read the chapter and `sk-prop-a1-kummer` unit records. This item is not their key statement node; their realized fields therefore need no edit. I read the current blueprint ancestor at `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-exc-dvr-galois.proof.md`, first paragraph, especially its finite-free length calculation. The determinant comparison supplied here supports exactly that inherited norm/order branch. No SGA source is used.

## Searches and reuse

Whole-DAG keyword/tag searches included 02MI, 02MF, 02MG, 02MD, Smith normal form, torsion-free freeness, quotient length, powers of a uniformizer, and determinant products. Whole-blueprint searches used `tools/blueprint_refs.py search` for lattice, Smith, length and determinant; `ancestor` confirms `lem-exc-dvr-galois`. No blueprint node states this full DVR identity, so `same_as` remains empty.

The six Mathlib queries in the item's new `mathlib_searches` are exactly the six real msearch calls logged in this sandbox. Both semantic phrasings were checked. I read the main hits in FreeModule/Finite/CardQuotient.lean:35-92 (integer lattice indices), FreeModule/Finite/Quotient.lean:115-135 and FreeModule/IdealQuotient.lean:54-73 (dimensions over an auxiliary scalar ring), FreeModule/Int.lean (cardinal indices), and LinearAlgebra/Determinant.lean:160-220,327-330,573-591 (determinant properties). None is the full DVR relative module-length statement, or a one-line specialization giving it. The Smith decomposition and determinant constructions are components already represented in the DAG. All six services/queries returned successfully; none is recorded as unavailable.

The only off-unit non-Mathlib citation is `lem-weil-pbc-cauchy-binet`, used solely for its square-matrix determinant product formula. It is declared in `split_report.tool_uses` with its precise role. The unit does not supply this generic matrix tool. It does not replace a unit proof step. All other off-unit proof citations are existing Mathlib leaves.

## Review by Q81

I read Algebra Tag 02MI, label `lemma-order-vanishing-determinant`, together with 02MF (`lemma-compare-lattices`), 02MG (`definition-distance`), and 02MD (`definition-ord`), directly in `literature/stacks-project/algebra.tex`. The source assumes a finite spanning lattice and an invertible fraction-field-linear map. A DVR is a permitted special case. The source distance has the same sign as the item: length of M modulo the intersection minus length of g(M) modulo it. I kept every clause and hypothesis. The equality between Stacks order and the normalized exponent is supplied explicitly in Steps 2–3, rather than assumed from the word valuation.

For Step 1 I opened `lem-sc-dvr-fg-torsionfree-free`: its actual statement requires just a DVR and a finitely generated torsion-free module and gives finite freeness. Torsion-freeness is proved inside the step from the embedding in V. I also read More on Algebra Tag 0AUW (`lemma-dedekind-torsion-free-flat`), part (3), and Mathlib FreeModule/PID.lean:376-390. Clearing a common scalar denominator proves the asserted K-linear independence. The three cited definition statements really do give the length of zero via chains, the empty matrix determinant, and the endomorphism determinant via a basis; consequently the rank-zero branch is justified without excluding it.

For Step 2 I opened `def-sc-discrete-valuation-ring`, `lem-weil-pbc-pid-noetherian-normal`, and `lem-weil-pbc-dvr-unit-times-uniformizer-power`. Their statements respectively supply a local PID with a nonzero principal maximal ideal, Noetherianity of a PID, and the unit-times-power expression for a Noetherian local domain with maximal ideal generated by one nonzero element. I read Tag 00PD, label `lemma-characterize-dvr`, including its final assertion and the valuation construction in its proof. The ring in hand satisfies every hypothesis before factorization is used. The exponent formula for fractions, uniqueness, multiplicativity and inverse rule are written out, so no uncited valuation theorem is needed.

For Step 3 the same DVR and factorization statements give precisely the principal-ideal classification actually used. I read the length definition in `def-weil-pbc-module-length` and Tag 02LY, label `definition-length`. Submodules of R/t^sR are exhibited by inverse image as the listed ideals; their strict chain has exactly s inclusions. Thus the length assertion, including s=0, follows directly from the definition. Invariance under the explicit isomorphisms used later is justified by the bijection on chains. This is an elementary calculation, not a new lemma node.

Step 4 uses only the finite coordinate array and the exponent calculation already proved in Step 2. It specifies q and verifies each t^q b_j belongs to g(M). There is no hidden appeal to commensurability or to finite generation of H. This writes out the common-denominator operation from the proof of Tag 02MF instead of using that phrase as a gap.

For Step 5 I opened `lem-sc-dvr-saturation-line-smith-normal-form` and Mathlib FreeModule/PID.lean:492-510. The node gives diagonal inclusion bases for any submodule of a finite free DVR module. E is finite free by Step 1, and N is a submodule by Step 4, so it applies. Its statement allows fewer basis vectors in N: the step proves equality of the two basis sizes using their K-spans, instead of falsely attributing full rank to the node. Nonzero diagonal entries follow from nonzero basis vectors, and the exponents come from Step 2.

For Step 6 I opened `lem-weil-pbc-length-additive-short-exact` and read Algebra Tag 00IV, label `lemma-length-additive`, statement and proof. The cited node states additivity in extended nonnegative integers and the finite-length equivalence, exactly as needed. The coordinate quotient map is written explicitly, with its kernel and surjectivity verified, and the finite direct-sum length computation is an induction through displayed split exact sequences. Thus neither the quotient decomposition nor finite-sum additivity is an uncited black box.

For Step 7 I opened the complete statement of `lem-weil-pbc-cauchy-binet` and the Leibniz definition `def-weil-pbc-matrix-determinant`, and read Tag 0F0K, label `item-cauchy-binet`, in algebra.tex. Setting m=n in the cited statement leaves exactly one subset, which gives determinant multiplicativity. The diagonal determinant and identity determinant follow directly from the cited Leibniz formula. The equations e'=eP, f'=fQ give PD=AQ with this orientation, so the valuation computation has the required sign. Inverse basis matrices lie over R; applying multiplicativity to both inverse equations proves the determinants of P and Q are units before their valuations are discarded. The full formula for length E/N is proved here and in Steps 5–6, not moved into a child node.

Step 8 uses the actual basis-coordinate assertion of `def-weil-endomorphism-determinant`, whose statement I opened. It identifies det G with det_K(g) and gives nonvanishing for the isomorphism g. The coordinate equation is GA_g=t^q I, because the E=g(M) basis is g(b); using A_g G instead without justification would be an indexing error. The determinant and valuation rules were already proved in Steps 2 and 7. This yields qn minus the valuation for the second length, and their difference is the positive valuation in the item's orientation.

For Step 9 the length-additivity node states both equalities and the finiteness implication used. The quotient maps are specified and their kernels verified. From finite M/N and g(M)/N it gives finite H/N and the two desired quotient lengths; only then are the length equalities subtracted as integers. This is the cancellation argument in Tag 02MF(4)–(5). Its only non-elementary input is the cited additivity statement. Every cited statement in every step was copied verbatim into citations.json; no proof of a node is used in place of its statement.

I checked the B–E return checklist against the actual node and sources: no new unsplit statements, duplicate nodes, tag-only proof inputs, external missing facts, moved clauses, ill-typed objects, or unverified hypotheses. No corrections to the item's statement were necessary. The source comparison and the proof do not impose excellence, henselianity, finite residue field, positive rank, or g(M) contained in M.

Small cases checked: V=0 gives determinant 1 and two zero lengths; g=1 gives H=M; g=t on a rank-one lattice gives lengths 1 and 0; g=t^{-1} gives 0 and 1; a unit scalar gives equal lattices and valuation zero; g=diag(t^2,t^{-3}) gives H=t^2R times R, lengths 2 and 3, hence difference -1, agreeing with det=t^{-1}. These also check why cancellation must be done with finite lengths before passing to integers. There are no new statements requiring separate small-case testing.

## Unfinished work and validation

No mathematical subtask is left in this one-level split. A fresh second reader must read it and perform delivery. The separate server checks returned `check_dag OK: no finding introduced by the sandbox or on its nodes` and `review_split: PASS; 0 new nodes; proof written by an agent`. The required `deliver.py Q81 lem-exc-dvr-lattice-distance-determinant --no-push` is run after this report is written; its console result is the final dry-run validation record. No local DAG checker, Lean compiler, Lake command, live-project write, or git command was run by this worker.

## Second reading by Q81

I reread the item statement against Algebra Tag 02MI (`lemma-order-vanishing-determinant`), with Tags 02MF (`lemma-compare-lattices`), 02MG (`definition-distance`), 02MD (`definition-ord`), and 02ME (`definition-lattice`) open. The DVR definition node supplies the Noetherian local one-dimensional hypotheses of those source statements; the finite-generation and $K$-span hypotheses are retained. The sign is correct: the item’s first quotient length minus the image quotient length is Stacks’ distance $d(M,g(M))$. I checked rank zero, rank one with $g=t^r$, units, and mixed diagonal exponents, including negative determinant valuation.

- Step 1 checked against `lem-sc-dvr-fg-torsionfree-free`, the module-length definition, the matrix determinant definition, and the endomorphism determinant definition. The torsion-free argument from $M\subset V$, the clearing-denominators $K$-basis argument, the transported basis of $g(M)$, and the rank-zero empty determinant case are all explicit; verdict: correct.
- Step 2 checked against `def-sc-discrete-valuation-ring`, `lem-weil-pbc-pid-noetherian-normal`, and `lem-weil-pbc-dvr-unit-times-uniformizer-power`, and against Tags 00PD and 02MD. Noetherianity is established before the unit-times-power factorization is applied; uniqueness and the fraction valuation rules are written out; verdict: correct.
- Step 3 checked against the DVR and unit-times-power statements and the module-length definition, with Tag 02LY read. The ideal chain above $t^sR$ is enumerated, including $s=0$, and isomorphism invariance is explained by chains; verdict: correct and elementary.
- Step 4 checked against the common-denominator construction in Tag 02MF. Every coefficient is handled, $N=t^qM$ is shown inside both lattices, and its basis and $K$-span are stated; verdict: correct and elementary.
- Step 5 checked against `lem-sc-dvr-saturation-line-smith-normal-form` and its Mathlib Smith-normal-form declaration. The node’s rank bound is not overread: equality of ranks is proved from the $K$-span of $N$, and diagonal entries are nonzero before valuation; verdict: correct.
- Step 6 checked against `lem-weil-pbc-length-additive-short-exact` and Tag 00IV. The coordinate quotient map, kernel, surjectivity, split exact sequences, and finite direct-sum induction are explicit; verdict: correct.
- Step 7 checked against `lem-weil-pbc-cauchy-binet`, the Leibniz determinant definition, and Tag 0F0K. The square specialization, basis-change orientation $PD=AQ$, unit determinants of $P,Q$, and valuation comparison are all written; verdict: correct.
- Step 8 checked against `def-weil-endomorphism-determinant` and the determinant/valuation calculations established in Steps 2 and 7. The coordinate relation is correctly $GA_g=t^qI$, and the formula for the second quotient has the required sign; verdict: correct and elementary from prior steps.
- Step 9 checked against `lem-weil-pbc-length-additive-short-exact` and Tags 02MF(4–5), 02MG. Both quotient exact sequences have their kernels identified, finiteness is obtained before subtraction, and the common $H/N$ term cancels; verdict: correct.

The sole node is the existing item itself; there are no new child nodes or Mathlib leaves to audit. Its statement is self-contained and cites all definition nodes, its source is the correct Stacks tag and label, its blueprint ancestry and `same_as` field are present, and its proof dependencies are existing DAG nodes. I searched the whole DAG for Tags 02MI, 02MF, 02MG, 02MD, Smith normal form, lattice, quotient length, and determinant vocabulary; no duplicate child node states the required full identity. The recorded Mathlib searches were rerun and their hits read; none gives the signed DVR length identity.

Changes made during second reading: applied the worker’s prepared nine-step proof and regenerated `citations.json` from the exact cited node statements. No mathematical statement, hypothesis, source, proof step, dependency, or search result required correction. No new nodes were created. The delivery dry run is the remaining validation.
