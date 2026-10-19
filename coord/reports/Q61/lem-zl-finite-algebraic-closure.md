# Q61: lem-zl-finite-algebraic-closure

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-finite-algebraic-closure.json`: four-step proof of Fields Tag 037J; statement unchanged, status split.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-rational-function-degree.json`: Mathlib leaf, the one-variable case of Fields Tag 0G1M; cardinal-rank and finite-rank equalities at RatFunc/Basic.lean:798,802.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-independence-algebraic-base.json`: Mathlib leaf, algebraic independence under an algebraic base extension; AlgebraicIndependent/AlgebraicClosure.lean:96.
- `citations.json`: seven verbatim statement quotations, one for every step/node citation.

## New nodes

Two new nodes, both statements and both Mathlib leaves. They have no proof steps or proof dependencies. The rational-function field and algebraic-independence notions cite existing definitions. No new definition or unit record is needed.

## Attachments

None. I searched the read-only project's `WeilConjectures/` for the exact item id, blueprint tag, 037J, algebraicClosure, finite algebraic closures, and finitely generated field extensions. No project declaration states the item without sorry. Searches of the relevant FieldTheory and Mathlib/FieldTheory project modules likewise did not find project declarations for the two leaves. Mathlib declarations are recorded as leaves, not project attachments. The item has no slopmaster2 declaration or open-hole audit requiring a separate attachment.

## WANTED

None. The source `literature/stacks-project/fields.tex` is local.

## Audit of the imported item and blueprint route

I read Fields Tag 037J (`lemma-algebraic-closure-in-finitely-generated`, lines 3584--3607), Tag 0G1M (`lemma-purely-transcendental-degree`, lines 3557--3582), and their full proofs, checking their tag labels against `stacks-project/tags/tags`. The item agrees with 037J exactly: finite generation is as a field, the closure is relative inside K, and the conclusion is finite vector-space dimension. No statement dispute or correction is needed. The statement, source, statement dependencies, creation metadata, inherited searches and blueprint ancestry are retained; the blueprint place is made precise.

I read the chapter and unit records and the current main-20261015 `lem-zl-bertini-finite-cover-curve.md` and `.proof.md`. Paragraph 3 uses Tag 0G4F; its field argument goes through 0G4D and the existing finite-separable-closure node, whose finiteness clause uses this item. The split follows that route and makes its 037J input explicit. This item is not the unit's key statement, so no realization record is changed. Every off-unit input is a definition or an existing Mathlib leaf; `split_report.tool_uses` is empty.

## Searches

I searched the whole DAG for 037J, 0G1M, the Stacks label, finite subextensions, finite transcendence bases, algebraic-independence persistence, and the exact Mathlib declaration names. I opened the statements returned, including the finite-basis and algebraic-generators leaves already in sec-proper-base-change. Whole-blueprint searches with `tools/blueprint_refs.py search` for `0G1M`, `lemma-purely-transcendental-degree`, `purely transcendental`, `algebraically independent`, `algebraic independence`, and `rational function` found no node stating either new fact. The ancestor command gives `lem-zl-bertini-finite-cover-curve`; each new node puts this item in front of its inherited via chain.

All fresh Mathlib searches were actually run through `msearch.py Q61 lem-zl-finite-algebraic-closure ...`, and their query text, returned names, and verdicts are recorded in the node files and `searches.jsonl`. The item's inherited four searches are preserved separately. Fresh item searches return only the algebraicClosure definition/properties, algebraic-plus-finitely-generated finiteness, finite normal closures, and results assuming a finite set of intermediate fields; none states 037J. I read the entire relative-AlgebraicClosure source and the relevant adjoin finiteness declaration. A second phrasing was tried before concluding no item match.

For the new leaves, semantic searches, valid Loogle names, and actual source greps returned the exact declarations. I read `RatFunc/Basic.lean:794--811`, including the algebraicity hypothesis and both rank equalities; `RingTheory/Algebraic/Integral.lean:101--109`, giving the finite-implies-algebraic instance; and the standard cardinal-rank/finite-dimension conversions at Dimension/Free.lean:263 and StrongRankCondition.lean:523. For independence I read AlgebraicIndependent/AlgebraicClosure.lean:29--99, not merely the search service's truncated signature. No unavailable search was interpreted as an absence result. Earlier exploratory commands using a nonexistent `Mathlib/FieldTheory` subdirectory returned zero hits; those zero-hit searches are not used as evidence in the new node records. The source greps in the final records use the correct paths relative to Mathlib.

## Not duplicates

- `lem-zl-rational-function-degree` vs `lem-zl-geometric-irreducibility-transcendental`: the new node preserves finite field-extension degree under one rational-function variable; the existing node concerns geometric irreducibility after variables are adjoined.
- `lem-zl-rational-function-degree` vs `lem-zl-finite-algebraic-closure`: Tag 0G1M compares the degrees of two rational-function fields; Tag 037J bounds and identifies the relative algebraic subfield of a finitely generated extension.
- `lem-zl-independence-algebraic-base` vs `lem-zl-finite-algebraic-closure`: the independence equivalence applies to an arbitrary algebraic base extension and any family; the item proves finite-dimensionality of a particular relative closure. The leaf supplies an implicit hypothesis check in the 037J proof, not its conclusion.
- `lem-zl-independence-algebraic-base` vs `lem-zl-finite-separable-closure`: the existing node gives geometric irreducibility over the relative separable closure and finiteness of that closure, not independence under algebraic scalar extension.
- `lem-zl-independence-algebraic-base` vs `lem-zl-rational-function-degree`: the first changes the coefficient field of an independent family; the second computes extension degrees of rational-function fields.
- `lem-zl-independence-algebraic-base` vs `lem-zl-bertini-independent-functions`: the existing node constructs special independent functions from a codimension-two geometric hypothesis, and does not state persistence under algebraic scalar extension.
- `lem-zl-independence-algebraic-base` vs `lem-weil-pbc-finite-rooted-extension`: that node constructs finite purely inseparable coefficient/root extensions with an independent replacement tuple; it does not state the general independence equivalence for a given tuple.

## Review by Q61

I checked B--E with the source and each cited statement open. The two new statements introduce all their fields, maps, families, and hypotheses, and carry statement only. Neither is a clause of the item or an elementary restatement of a cited theorem outside Mathlib. Both are genuine Mathlib leaves: the field-specialized independence equivalence is exact; the degree lemma is the finite specialization of the cardinal rank equality, with algebraicity supplied by the finite-extension instance. Cardinal rank equality establishes finiteness of the rational-function extension, so the match does not incorrectly infer finiteness from two potentially zero-valued `finrank`s. The source of the independence lemma is identified honestly as the implicit prerequisite in the application in 037J; its precise general statement and proof are supplied by the inspected Mathlib theorem.

Step 1 uses the statement of `lem-weil-pbc-finitely-generated-field-finite-transcendence-basis`: it supplies the finite independent tuple and algebraicity over L. The statement of `lem-weil-pbc-algebraic-generators-finite-extension`, applied over L to the original finite field generators, then gives finite n=[K:L]. These are exactly the hypotheses present; no separable-generation or perfection assumption is inserted.

Step 2 checks that each element of the finite intermediate field k' is algebraic by linear dependence of its first m+1 powers. The new independence leaf therefore applies to k inside k' inside K and the tuple from step 1. The new degree leaf applies inductively to E_j/F_j. I checked the base j=0, the finite-degree invariant, and that x_(j+1) is transcendental over both current coefficient fields. The denominator argument explicitly multiplies by a finite product of nonzero denominators and preserves a nonzero coefficient. Evaluation identifies E_j(T) with E_(j+1), and F_j(T) with F_(j+1), by the stated fraction model of `def-weil-rational-function-field`: independence makes evaluation injective, all generated-field elements are fractions, and the evaluations commute with coefficient inclusion. This is a routine use of that definition, not a new comparison theorem. Thus the one-variable leaf gives the desired degree equality at every induction step. There is no new node for the elementary finite-tuple iteration.

Step 3 is elementary and is the source's displayed inequality: the inclusion of the intermediate field into K preserves L-linear independence, so its dimension is at most n. It uses only what steps 1--2 established.

Step 4 uses the statement of `def-weil-relative-algebraic-closure`, specifically that A is a subfield containing k and algebraic over k. Finite-subextension degrees lie in {1,...,n}, and k itself supplies degree one. A finite-dimensional subfield has a finite basis which generates it as a field (the field contains the full linear span). Applying the existing algebraic-generators finiteness leaf to that basis and alpha gives the finite compositum k'(alpha), contained in A. Maximal degree and the elementary strict dimension inequality for a proper vector subspace force alpha into k'. This expands the bounded-degree sentence of 037J, with no unnamed finite-generation theorem for A.

The seven quotes in `citations.json` are copied verbatim from the cited statements. The rational-function quote uses only its fraction-field clause. Every non-elementary input is cited, proof_deps equals the union of the step uses, and the server graph check will verify the dependencies. All four steps are below 2000 characters. No source error, SGA citation, hollow definition, Lean edit, or compile/build operation occurs.

Small cases checked: K=k and empty transcendence basis; finite algebraic K/k, including inseparable extensions in characteristic p; k(t)/k, for which the relative closure is k; and Q(i)(t)/Q, for which it is Q(i). For the independence leaf I checked the empty family, E=k, an algebraic finite or infinite E/k, and a nontrivial transcendental x over E; the common-field/tower hypothesis matters and is present. For the rational-function leaf E=k gives degree one, E=Q(i) over Q gives degree two, and E=F_p(u^(1/p)) over F_p(u) gives degree p without separability. The induction includes r=0, and the maximal-degree set is nonempty because all fields here are nonzero.

During self-review I replaced an unnecessary general finite-tuple support node with the exact one-variable Mathlib leaf, wrote the finite-tuple induction in the item, and cited the separate exact independence theorem to justify changing the coefficient field. This repairs the only substantive gap in the first draft. I also corrected the source-search directory and kept the actual logs. No mathematical statement of the imported item changed.

## Unfinished work

No mathematical work remains in this stage-1 split. Delivery is subject to the required server preflight and dry run.
