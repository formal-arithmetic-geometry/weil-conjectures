# Stage-1 delivery: lem-sfb-affine-properness-formal-arc-test

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-properness-formal-arc-test.json: existing statement, split into six steps; no statement or statement-dependency change; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-properness-normal-curve-local-test.json: new statement-only lemma, unsplit; no Mathlib match after two semantic formulations, LeanSearch, Loogle and source grep.
- citations.json: all 23 step/node citations, with the verbatim statement of each dependency. Searches and the generation script remain sandbox working material.

## Attachments

None. Searched the live lean/WeilConjectures source by blueprint id and by formal-arc, PowerSeries/properness, curve and valuative terminology. No project declaration states the item. General Mathlib valuative criteria quantify over every valuation ring; they do not finish the item.

## Wanted literature

WANTED: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, third edition, Chapter 2 Section 1, proof of Theorem 2.1, for the item's original source. The book is absent locally and I do not claim to have read it. Instead the proof follows the available Stacks normal-curve criterion 0GWX and the available completion results. The assembly is marked proof_origin.by = agent.

## Corrections and scope

The imported statement is true as written, including the original algebraically closed field, arbitrary characteristic and nonreduced X,Z. No STATEMENT-DISPUTED correction was needed. The source reference originally mentioned curve selection without supplying its theorem or a descent argument; both are now exposed: the new 0GWX node states the precise source test, and steps 3–5 complete its DVR and descend explicitly. No generic lift over an arbitrary field extension is silently substituted for a lift over k.

The item has inherited blueprint.from.node = null. The required ancestor command prints None, through its existing chain ending at the direct-images proof. I retain that ancestry and fill the new node's via list by prepending this item. The newest blueprint read is literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/, including its _section.md and sk-thm-sf-ctf-stability-direct-images.proof.md (3). The inherited unit record uses an older chapter path; no chapter or unit statement is edited. This lemma remains a generic algebraic-geometric prerequisite below the specified alteration/Gieseker/Hilbert–Mumford chain.

## Unfinished work

Only the new normal-curve local criterion remains unsplit, as required for newly created nodes. There are no omitted proof obligations in this item's natural-language assembly. No Lean was written, and no compiler, Lake or build tool was run.

## Not duplicates

The DAG, all imported blueprint nodes and the live Lean source were searched for 0GWX, essentially-finite-type-criterion-proper, normal curve and valuative terminology before the new node was written. No existing node has its statement or source tag. In particular:

- lem-sfb-properness-normal-curve-local-test vs lemma-nagata-proper-separated-valuation-extension: the existing statement gives extension for an already proper map and every valuation ring; the new statement characterizes properness using only the source's normal-curve local squares.
- lem-sfb-properness-normal-curve-local-test vs lem-sfb-affine-properness-formal-arc-test: the new lemma tests local DVRs of finite-type normal curves over any field; the item tests one completed DVR over a fixed algebraically closed field. Completion with the specified coefficient field and descent of affine maps are the substantive steps still proved in the item.
- lem-sfb-properness-normal-curve-local-test vs lem-sfb-dense-generic-trait-selection: that existing statement selects a trait over a specified DVR with a finite extension of its fraction field; it does not give a properness criterion or ensure residue field k for these curve tests.
- lem-sfb-properness-normal-curve-local-test vs lem-trf-regular-complete-coefficient-coordinates: the latter gives the coordinate isomorphism for a supplied complete regular local ring; it supplies no reduction of properness to curve squares. It is reused directly in step 3.

## Review by Q76

I checked the statement and its proof against the actual text of Stacks limits.tex, Tag 0GWX (lemma-essentially-finite-type-criterion-proper), including its C,U,c hypotheses and the distinction between a global punctured-curve diagram and its induced local square. The new node states exactly the field specialization of that result: X,Y locally of finite type over k, f quasi-compact, C normal integral and finite type, c closed and its local dimension one. A field is a Nagata base; no excellence of an arbitrary DVR is asserted. I read the preceding 0GWV proof as well to check that the normalization/curve-selection input is substantive and belongs in a node. The new node is statement-only; it does not hide an inline proof sketch or merely rename one clause about formal arcs.

For step 1 I opened the statements of lem-weil-pbc-power-series-field-cohen-regular-complete, def-sc-discrete-valuation-ring, lem-weil-pbc-dvr-unit-times-uniformizer-power, lemma-nagata-proper-separated-valuation-extension and def-weil-proper-morphism. The first gives all the ring hypotheses for the field case d=1; the DVR definition gives valuation-ring status; factorization proves explicitly that the Laurent localization is the fraction field. The extension node asserts existence AND uniqueness, and properness supplies its separatedness hypothesis. I also read Mathlib AlgebraicGeometry/ValuativeCriterion.lean:330–343: its theorem covers the forward direction, but not the restriction to this one DVR in the converse.

For step 2 the new criterion's exact C,U,u,v square is fixed, rather than an arbitrary fraction-field map. The affine spectrum node supplies the ring maps; finite k-generators also generate over D, and principal-open preimages prove quasi-compactness directly. pqf-lem-locnoeth-lft is applied over the Noetherian field k. lem-sc-normal-dim1-dvr requires a Noetherian normal local domain of dimension one; each hypothesis is provided by C and c. lem-kun-closed-point-field gives a finite residue extension, not an equality with k; the minimal-polynomial argument written in the step supplies that equality. I read the corresponding Stacks morphisms.tex statements 01T6 and 01TF and algebra.tex 00PD.

For step 3 I opened the full statements of completion-of-dvr-is-dvr, local-completion-local-ring, adic-completion-mod-ideal, dvr-unit-times-uniformizer-power, def-weil-regular-scheme and regular-complete-coefficient-coordinates. I read More on Algebra 0AP1, Algebra 05GG, 05GI, and 0C0S(2). These separately provide the DVR structure, the image maximal ideal and residue field, completeness, and coordinates over the SPECIFIED structural coefficient field. In particular I did not use 0C0S(1), which only provides some coefficient field. A DVR has exactly its zero and maximal primes by the cited element factorization; hence its dimension is one and its principal maximal ideal verifies the stated definition of regularity. The image of the chosen uniformizer generates the completed maximal ideal, so the coordinate theorem applies to that parameter.

Step 4 uses only the preceding results, the DVR factorization and affine spectrum functoriality: a nonzero element u*pi^n maps to a unit times t^n and stays nonzero. This proves the needed inclusion F into k((t)), so restricting u and v really gives a formal-arc square over k. It does not use flat descent or an uncited completion theorem. Its elementary flag refers to this direct substitution and application of the hypothesis.

Step 5 proves the intersection identity by factoring a numerator and denominator with the cited DVR factorization. A negative exponent makes a unit divisible by t in k[[t]], impossible. The two coordinate maps agree in the Laurent field; every coordinate is consequently in R. Addition, multiplication and base compatibility are checked after the injective inclusion into that field. This is a few-line denominator argument using the cited factorization and affine-spectrum correspondence, not an unproved descent theorem. The statement of every cited node supplies exactly the portion quoted in citations.json.

For step 6 I checked that uniqueness is for the same prescribed generic map, so injectivity R -> F proves equality of the ring maps. The normal-curve criterion then applies with all its global diagram quantifiers satisfied. None of the steps uses a construction hidden in a cited proof. All non-elementary inputs occur as cited statements and proof_deps is their union. The off-unit dependencies are declared as generic tool uses in split_report, never installed in maintainer-owned tool_uses.

I checked delivery-errors B1–B10: the sole new node is self-contained and unsplit, uses cited definitions or inline meanings, has correct TeX, source tag 0GWX and its exact source label, no unrun search, and an explicit blueprint place. Mathlib searches found only all-valuation-ring criteria and unrelated completion constructions; none states this normal-curve restriction. I checked C1–C8 by opening each cited statement and producing verbatim quotations; the new node has no dependency on this item and no backwards edge was introduced. I checked D1–D5: the assembly retains the DVR completion, coefficient-field identification and denominator descent, so it is not relabelling or moving the entire item into the new node. All six steps are below 2000 characters. I checked E1–E7 on the actual objects: base field k, closed point c, its local ring R, its completion H, and F=Frac R.

Small cases: empty X or Z give vacuous curve squares in exactly the expected cases; a closed immersion including a nilpotent thickening is proper and satisfies the test; the nonproper open immersion G_m -> A^1 fails on the arc x=t; the constant map A^1 -> Spec k fails on x=t^(-1). A singular normalizable curve is allowed in the source reduction because its selected C is normal before taking the DVR; no assertion that the original X is smooth or reduced is used. In positive characteristic the same structural residue map k -> H is retained, so no separability or characteristic-zero assumption enters the coordinate isomorphism. Zero elements are separated explicitly in the intersection calculation. No SGA source is cited.

In the resumed final reading I corrected a citation omission in step 2: affine quasi-compactness now cites the existing Mathlib leaf lem-weil-pbc-affine-scheme-qcqs. I read its whole statement and Algebra 00E8 (lemma-quasi-compact), and wrote the finite principal-open cover argument for every affine target open, so checking quasi-compactness does not silently check only a basis. This adds one verbatim quotation to citations.json, with no new node or statement change. The completed dry run before this correction passed at 030f872cc4d; the corrected files are checked again before delivery.
