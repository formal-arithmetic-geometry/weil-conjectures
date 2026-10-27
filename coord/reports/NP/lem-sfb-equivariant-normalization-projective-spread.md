# Stage-1 report: lem-sfb-equivariant-normalization-projective-spread

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-normalization-projective-spread.json: statement, split into eleven steps; not a Mathlib leaf. No new nodes, no Mathlib leaves created.
- citations.json: verbatim full statements for every node used by every numbered proof step.
- report.md: this report. searches.jsonl records the required searches; write_split.py is sandbox-only preparation.

## Attachments

None. Searched the project WeilConjectures source for the blueprint tag, equivariant normalization, and normalization/projectivity. The only relevant curve compactification occurrence is a different construction. The retained thirteen-step docstring in lean/Sheaf/AlgebraicGeometry/EquivariantFlatCurvePreparation.lean was read as parent proof history, not as a finished attachment.

## Wanted literature

WANTED: de Jong, Families of curves and alterations (1997), Sections 2.9–2.10, printed pp.604–605, for lem-sfb-equivariant-normalization-projective-spread. No local copy is listed or present. No download was made. The proof is explicitly agent-written using the local Stacks sources and existing DAG statements; no assertion is attributed to an unread de Jong proof.

## What needed attention

The item's statement is mathematically unchanged. Its original source field refers to the retained parent Steps 5–7; I read those in the parent Lean docstring and expanded their generic-fibre localization calculation and invariant-closure argument. The pure-inseparability definition was added to statement dependencies. The source, creation history, ancestry (whose nearest blueprint ancestor is null), and other maintainer fields were preserved.

The existing lem-sfb-normalized-base-relative-factorization assumes finite separable extensions. It cannot be applied to K0/K here. Instead Steps 3–5 explicitly construct the maps using inclusions of integral closures and compute the generic fibre using localization and integral transitivity. This follows the retained route. Similarly, finite-over-projective is applied only over the affine field base; it does not assert a global finite-projective-space embedding over an arbitrary base. Projectivity over S0 comes from the already existing closed-graph lemma with the identity constants extension k/k.

Mathlib's normalizationDesc and associated integral-morphism instances give relative-normalization universal properties. Reading Mathlib/AlgebraicGeometry/Normalization.lean, especially lines 369–415, shows that they do not state the semilinear Chow modification, the proper normal-curve isomorphism, or the invariant marking closure required here. Both natural-language phrasings, Loogle, grep and LeanSearch were actually run through msearch.py, and their exact queries and returned names are recorded. The pre-existing 2026-10-22 search records were retained unchanged.

## Unfinished work

None at stage 1. The prerequisites remain their existing DAG nodes; no Lean files were changed and no compiler or build command was run.

## Not duplicates

No new nodes. Whole-DAG title/statement and relevant-tag searches found the existing finite-normalization-model-functoriality, semilinear-equivariant-chow-modification, finite-constant-projective-graph, localization, integral-transitivity, dimension and normal-curve comparison nodes, which are reused. Whole-blueprint searches for normalization projective, equivariant Chow, normalization finite extension and generic normalization found no matching blueprint statements. The current direct-image stability proof and the recorded parent route were read; this is the normalization/Chow preparation within that route, not a replacement of the unit's direct-image argument.

## Review by NP

I read coord/delivery-errors.md B–E, the item, its parent, the parent Steps 5–7 retained in the Lean docstring, the chapter and unit records, the current blueprint direct-image proof, and the actual statements of all 25 distinct cited prerequisites. The item source was checked against coherent.tex Tag 0200, algebra.tex Tags 0307, 00GK and 00GN, varieties.tex Tag 0BXR and the proper normal-curve Tags 0AB7/0BFP, together with morphisms.tex Tag 0C4Q's closed graph. Excellence was checked in more-algebra.tex Tags 07QW/07QU and morphisms.tex Tag 0HAB; the scheme-image kernel is morphisms.tex Tag 01R8. There are no new-node sources to review and no SGA sources were used.

Step 1 uses the full statement of lem-sfb-finite-normalization-model-functoriality: it supplies the normal integral models, finite maps, specified function fields, and semilinear actions preserving compositions. Its finite-extension hypothesis on F0/F is verified by the finite K-basis tensor spanning calculation; it does not require separability or faithful actions. The field action is explicitly defined on tensors, so it agrees with the given action on C and K0.

Step 2 uses lem-fin-finite-over-projective only with the affine Noetherian base Spec k, where its statement gives global H-projectivity. lem-pc-projective-proper supplies properness, lem-weil-pbc-proper-fp-permanence(a) composes proper g and Y/k, and lem-weil-pbc-finite-morphism-permanence(c) gives properness of C0/k. Thus separatedness of the base in the next step is established, not assumed.

Step 3 uses def-fin-normalization-extension for its actual affine integral-closure construction and lem-weil-pbc-integral-closure-commutes-localization for restrictions. I checked that A' sits in B' by the same monic equation, not merely by a topological factorization. Those inclusions commute with the field automorphisms and glue. lem-weil-pbc-proper-to-separated applies over Spec k with proper source C0 and separated target S0; its statement says exactly that this k-morphism is proper.

Step 4 uses the finite-dimensional-domain field lemma on S^{-1}A', which is finite-dimensional over K because S0/Y is finite. Its fraction field is already K0 by Step 1. The localization lemma then identifies S^{-1}B' with the integral closure of B_K in the specified F0. The remaining tensor-injection assertion is elementary vector-space linear algebra with a basis extension; I wrote the reason. Localizing B_K tensor K0 at the nonzero elements of B_K gives exactly F0, so the claimed fraction field is the specified one.

Step 5 uses finite-algebra-is-integral on the finite free spanning presentation of B_K tensor K0. Integral-transitive supplies the reverse inclusion between the two integral closures, with both algebras inside F0; merely citing a definition of integrality would not suffice. The localization statement proves compatibility of the affine identifications. This preserves the embeddings of B and K0, which is what makes the generic isomorphism over C and K0 rather than an abstract normal-curve isomorphism.

Step 6 uses dimension-under-field-extension to keep dimension one, normalization-exists for finite birational normalization and its dimension/properness clauses, and proper-base-change for the initial curve. The affine domain calculation verifies integrality before applying normalization-exists. Smoothness and geometric integrality of N are hypotheses of this item; no perfection hypothesis on k is added.

Step 7 uses semilinear-equivariant-chow-modification precisely for a proper integral finite-type scheme with a possibly nonfaithful semilinear action. Its statement gives proper birational q, T integral, and both absolute and relative finite-space projectivity. The finite-constant-projective-graph statement is used with F=k, whose degree is one, and separated target S0, already established. It directly gives H-projectivity of T/S0.

Step 8 uses generic-fibre-localization-domain-irreducible only after checking injection of the base domains through K0 into F0. Integral-function-field-affine-fraction identifies the surviving fraction fields. Proper-fp-permanence gives properness after the generic base change. Closed-irreducible-dimension-trdeg applies to the entire underlying spaces of the two integral finite-type K0-schemes, whose function fields with their K0-embeddings agree. Proper-birational-normal-curve-iso explicitly requires normality only on the target. Thus it applies to possibly nonnormal T_eta and the normal curve N. The isomorphism is the displayed q_eta and consequently is equivariant and over the specified maps.

Step 9 uses exactly the finite-type Noetherian theorem, fields-excellent, finite-type-localization-excellent, and the excellent-scheme-affine-cover statement. The latter explicitly passes from the chosen cover to all affine coordinate rings. This proves the item's stated meaning of excellence, and does not silently replace it by excellence on just one chart.

Step 10 uses qcqs-morphism-permanence on quasi-compact D and quasi-separated T. D is quasi-compact by its finite-over-a-field hypothesis, and T is separated by its projective embedding. The scheme-image-qc-kernel node then states existence and the affine kernel formula used here. Equivariance is proved by applying h to the restriction maps: it preserves their kernels, so it preserves the subscheme structure, not just the underlying subset.

Step 11 is the elementary ideal extension/contraction calculation written in full. For J in S^{-1}R, each r/s in J has r in its contraction, which proves S^{-1}I=J. This identifies the whole closed subscheme on the generic fibre, including nilpotents, rather than just its support. Empty D gives the unit ideal and empty L. This step needs no hidden flat-base-change theorem for scheme images.

I checked B1–B10: no new statements or proof-carrying leaves, all item objects are introduced, definitions are cited or given inline, mathematical TeX is single-escaped, actual tag/label pairs were read, no Mathlib attachment is claimed from partial hits, and the blueprint provenance is preserved. I corrected a draft source label for 01W6 to its actual label lemma-image-proper-scheme-closed. C1–C8: every non-elementary fact has a cited statement, every citation is quoted verbatim in citations.json, proof_deps is the union of uses, and cross-unit generic tools are declared only in split_report.tool_uses as required. D1–D5: no clauses were repackaged into new nodes; the affine calculation and marking calculation remain genuine arguments. No induction is hidden. E1–E7: I checked finite/separable hypotheses, the actual tensor and localization rings, and compatibility of the structural maps; I found no statement dispute.

Small cases checked: K0=K in characteristic zero; Y=Spec k (including nontrivial finite purely inseparable K0/k); C already smooth projective; trivial or nonfaithful H; semilinear field automorphisms; and empty D. With zero-dimensional base the normal-curve lemma still makes the Chow model's whole generic fibre isomorphic to N. No normality of T is used. Every non-elementary step is at most 1151 characters, so there is no long step concealing a separate lemma.

The server review_split preliminary check passed with zero new nodes. The full dry run and delivery are run after this report is written.
