# p-real-sections — Q102 stage-1 report

## Files written

- `dag/nodes/sec-purity-real-sheaves/p-real-sections.json`: split statement; no Mathlib match for the geometric statement. Five proof steps follow the unit's Hom-from-the-unit route.
- `dag/units/sk-p-real-sections.json`: only `realized` and `realized_by`, binding the statement and sole unit proof paragraph to p-real-sections.
- `citations.json`: verbatim statement excerpts for every dependency of every proof step.
- No new nodes and no Mathlib leaves.

## Attachments

None. I searched the project source both for p-real-sections and for global sections/invariants. `AlgebraicGeometry.WeilGroup.globalSections_eq_invariants`, `WeilConjectures/EtaleCohomology/Purity/RealSheaves/LocalSystems.lean:396`, is sorry-free in its own body and proves the evaluation-at-one calculation and its Frobenius compatibility. However `AlgebraicGeometry.WeilGroup.globalSections` at line 329 is DEFINED as the submodule of equivariant linear maps. It is not étale global sections of a sheaf. The module explicitly acknowledges at lines 77–82 that the lisse sheaf itself is unavailable and that `CategoryTheory.Sheaf.H` is not used. Thus this is not an exact attachment for the item, whose left side means actual ordinary étale global sections. No compiler or axiom checker was run.

## WANTED

None. The split is agent-written following the available main-20261015 blueprint proof, with the precise statements of the existing dependency nodes as its interfaces.

## What was wrong and what changed

The statement is retained verbatim; no hypothesis or conclusion was changed. The imported proof's instruction to apply the Weil-sheaf equivalence on the connected geometric open did not identify the correct Hom sets. That equivalence gives Weil-equivariant morphisms, whereas geometric sections are morphisms of underlying lisse sheaves. A constant geometric line with Frobenius scalar a ≠ 1 has one-dimensional geometric global sections, but no nonzero Weil-equivariant morphism from the trivial Weil line. I replaced this use with the existing `cor-galois-lisse-representations`, whose clause 2 explicitly is the underlying geometric equivalence and preserves the unit.

The imported last phrase asserted Frobenius equivariance without computing it. Step 5 computes pullback followed by the Weil structure on the source unit and on the target fibre, then evaluates at 1. Since the item inherits a fixed degree-one lift on C_0, I also used the existing dense-open Weil-group surjectivity clause to choose a compatible lift on U_0, rather than silently choosing a different operator. Normality and connectedness hypotheses are verified first. No assertion of another node or any maintainer-owned metadata was changed.

## Search record and reuse

The initial sandbox contained only dispatcher markers and had no earlier node, report, citations or search log. All six searches in `searches.jsonl` were run through msearch.py and read; the item's records use the exact tool and query strings. They include LeanFinder twice with different phrasings, Loogle, LeanSearch and two source greps. No service was unavailable. The first searches found general constant-sheaf or Galois-category facts. The second LeanFinder phrasing found `Rep.invariantsAdjunction`, its homEquiv formula, and `Representation.linHom.invariantsEquivRepHom`. I read `Mathlib/RepresentationTheory/Invariants.lean:151–182, 191–237, 265–290`. These give the algebraic part only and do not identify sections of an adic étale sheaf. The item's proof writes the short algebraic specialization directly as an elementary step; creating a new node for it would violate the elementary-node rule.

I searched the entire DAG and imported blueprint with `blueprint_refs.py ancestor p-real-sections` and searches for `global sections invariants`, `sections`, `invariants`, and `H^0`, and searched DAG/source text for the notions. There is no second node with the full statement. The same-named sketch is the unit record realized here, not a separate DAG node. `lem-pod-connected-constant-h0` only treats constant coefficients and cannot replace the item's arbitrary lisse sheaf. `lem-a1-affine-hc2` uses this item and is not a permissible dependency. No new node is proposed, so there are no duplicate-tag pairs requiring a Not duplicates section.

## Review by Q102

I read the master-imported item, its unit and chapter, the current main-20261015 `p-real-sections.md`, its separate proof, and both files of the matching unit. The mathematical statement and the sole unit paragraph have not changed between the snapshots. I also read the current main-20261015 sheaf–representation statement, and opened the statements of every node cited in the final proof. This is my own check of the split, not an independent review.

Step 1 uses `d-real-setup` for the standing nonempty smooth separated geometrically connected curve and ell ≠ characteristic. The first clause of `lem-sc-smooth-connected-curve-local-rings` actually says that its geometric curve is Noetherian and integral; `lem-sc-smooth-normal` actually says that a smooth curve over a field is normal. The open U is dense and connected by the two-open-intersection criterion written in the step. Being an open subscheme gives the Noetherian and separated restrictions. This checks the connected, Noetherian, separated and invertible-ell hypotheses for the equivalence, and the connected-normal hypotheses for later dense-open surjectivity. I do not use the local-ring lemma's DVR or valuation clauses.

Step 2 uses the explicit coefficient-system definition `def-pod-lisse-l-adic-sheaves`: its clause 1 defines morphisms as compatible families, clause 2 defines rationalized Hom, clause 4 defines the scalar-extension colimit, and clause 5 identifies the unit. The section/morphism bijection is elementary: send s to multiplication by its restrictions, and send m to m(1). Locally constant scalar sections reduce the inverse identities to m(a)=a m(1). The same formulas apply to the coefficient systems and their morphisms by those definitions. This does not treat a Qlbar local system as a discrete constant-coefficient étale sheaf and does not invoke an unproved commutation of arbitrary cohomology with a limit.

Step 3 uses exactly clause 2 of `cor-galois-lisse-representations`, including its explicit preservation of the unit at every coefficient level. An equivalence is fully faithful, so it supplies the required Hom bijection with equivariant linear maps. `def-wf-fundamental-representation` explicitly identifies the underlying action as the geometric representation extended by the Weil descent datum. I do not use a definition node as evidence of an equivalence, and I do not ask the Weil-sheaf equivalence to give non-Weil-equivariant morphisms.

Step 4 uses only the invariant-subspace formula in `def-real-weil-representation-operations`. The proof checks f(1) is fixed, checks a ↦ av is equivariant, and checks the two inverse identities and linearity. This is a few-line argument, not a new lemma or a Mathlib leaf for the full item.

Step 5 reads the exact statements of the two group lemmas. Clause 2 of `lem-wf-dense-open-pi1-surjective` says both that restriction of Weil groups is surjective and that it respects degree, so the chosen degree-one element on C_0 really has a degree-one lift on U_0; Step 1 checks the dense, connected, normal and Noetherian hypotheses. `lem-wf-weil-group-exact-sequence` identifies the kernel of degree with the geometric subgroup. The displayed conjugation calculation proves stability, and the inverse lift proves invertibility. The definition of the fundamental representation gives the stalk operator supplied by phi after the same transport, not merely an abstract unrelated representation. Pullback fixes 1 in the constant unit, so evaluating the transformed map gives F f(1), exactly the requested commutative square. The action does not depend on the auxiliary lift, since two lifts differ geometrically.

The four generic tools are declared in `split_report.tool_uses`: the curve integrality/Noetherian lemma, smooth normality, the underlying lisse-sheaf equivalence, and dense-open Weil-group surjectivity. These fill hypotheses or the required underlying geometric Hom interface; they preserve the unit's stated proof route. No theorem from SGA is used. The proof sources are the blueprint, marked agent-written, and no tag is substituted for a missing node citation.

I tested zero rank (both spaces zero), the trivial geometric line with arbitrary nontrivial Frobenius scalar (both sides are the same line with that scalar, not its F-fixed subspace), a nontrivial geometric rank-one character (both spaces vanish), and U_0=C_0 (restriction and choice of lift are tautological). For a proper nonempty open, dense-open surjectivity ensures the operator of the original curve can be used. These tests expose precisely the error of taking Weil-invariant sections. No affine or proper hypothesis was inserted. All proof steps are below 2000 characters, and no non-elementary subclaim has been hidden in a long step. I checked B–E: no new-node shape obligations, no restated clause moved to a new node, no source-proof access in place of a cited statement, no added hypothesis, no circular use of a citer, and no missing equivariance argument.

## Unfinished work

No mathematical part of the stage-1 split remains. The comparison is a natural-language proof; no Lean files were written or compiled. Required server checks and delivery results follow below.
