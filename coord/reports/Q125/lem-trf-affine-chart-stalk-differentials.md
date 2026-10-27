# Stage-1 delivery: lem-trf-affine-chart-stalk-differentials

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-affine-chart-stalk-differentials.json`: statement item split in four steps; not a Mathlib leaf as a whole.
- `citations.json`: one verbatim statement quotation for each of the seven citations across the four steps.
- `report.md`: worker report and direct-delivery self-review.
- `searches.jsonl`: six searches recorded by msearch.py, all successful, with results read.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves reused for chart naturality, affine-open stalk coordinates, Spec stalk maps and tilde-module stalks. No Lean files written and no compiler or build run.

## Attachments

None. Searched the project Lean source both for the exact blueprint tag and the relativeDifferentials/stalk notions. There is no project declaration of the whole item. `AlgebraicGeometry.relativeDifferentials_affine_sections` in RelativeDifferentialsAffineSections.lean covers sections only, and the relative differential constructions and affine comparison in Modules/Differentials.lean do not also state the finite-presentation chart choice and stalk/generator assertion. These partial results do not justify ATTACH.

## Literature wanted

None.

## Errors and corrections

No mathematical statement correction or dispute was needed. Added the missing notion dependency and inline reference `def-weil-pbc-module-localization` for the notation M_q. This does not change the objects, hypotheses or conclusion. The original item had no proof; supplied the chart square, actual germ maps, restricted stalk comparison and explicit tensor transport instead of leaving these as implicit identifications. Existing blueprint metadata and inherited searches are retained.

## Unfinished work

None within this one-level stage-1 split. The reused affine relative differential description is already part of the statement of `def-sc-relative-differential-sheaf`; it is not inferred from its implementation or a private proof. There is no new unsplit lemma here.

## Not duplicates

No new nodes. Whole-DAG title/statement searches and searches for Tags 01HV, 01UT, 01US and 01TP recovered the existing affine and stalk nodes used in the proof. Blueprint searches for differential, cotangent, stalk localization, relative differentials and affine chart yielded no node stating this full chart/stalk assembly. In particular, the derived cotangent comparison is a different theorem and is not used. `same_as` remains empty; ancestor is `lem-trf-local-term-locality` with the inherited via chain.

## Review by Q125

I read the item against Stacks morphisms.tex Definition 01TP (definition-finite-presentation), Lemmas 01US (lemma-differentials-restrict-open) and 01UT (lemma-differentials-affine), and the smooth-at-point criterion 01V9. I also read schemes.tex Lemma 01HV (lemma-spec-sheaves), including clauses (6)-(7) and its functoriality statement, and the ring-map/point discussion in 01HY and 01I1; algebra.tex Definition 00HB supplies flatness. No new node needs a source review. I read the chapter, unit, current blueprint ancestor and the existing parent smoothness criterion: this item supplies the parent's affine reduction and changes no unit-level route.

Step 1 uses exactly the affine-neighbourhood assertion in `def-sbc-locally-finite-presentation`, read in full. It gives both the finite-presentation ring map and containment of the source chart in the inverse image of the target chart, so no assertion about arbitrary affine neighbourhoods is needed. In particular the target chart contains s=f(x).

For step 2 I opened all three cited nodes. `lem-weil-pbc-affine-opens-induced-ring-map-spec-square` states equality of the actual chart morphisms; `lem-weil-pbc-spec-map-stalk-localization` states both contraction of the point prime and the fraction formula for its actual stalk map. `lem-weil-pbc-affine-open-stalk-localization` states the germ-preserving stalk isomorphisms for the ambient schemes. Their hypotheses hold for W,V from step 1. Taking stalks of this equality identifies f's stalk map, rather than an arbitrary isomorphic ring homomorphism. A denominator t outside p maps outside q by the definition p=phi^{-1}(q).

Step 3 uses the full statement of `def-sc-relative-differential-sheaf`, which explicitly says that its affine restriction is the associated sheaf of Omega(A/R), with derivations compatible under restriction. `lem-weil-pbc-spec-tilde-stalk-localization` explicitly supplies localization over the structure-sheaf stalk and the formula sending the germ of m to m/1. It applies to the arbitrary A-module Omega(A/R); neither Noetherianity nor finite generation is required. The short neighbourhood-intersection argument explains why the restriction stalk equals the ambient stalk. Together these give the requested A_q-linearity and the formula for da, not just an additive bijection.

Step 4 cites only `def-weil-pbc-flat-ring-map`, whose injective-tensor formulation is precisely what the written argument checks. I wrote the scalar relabelling, tensor map, inverse, balancing equation and naturality in the input module, so invariance of flatness is a calculation from that definition rather than an unquoted theorem. The spanning-family calculation uses the actual semilinear identification from step 3 in both directions. The cases r=0 and zero differentials are covered: an empty spanning family is equivalent to the module being zero.

I checked the seven original notion dependencies and the added module-localization definition. The definitions respectively give schemes, affine spectra, local finite presentation, prime localization, Kahler differentials, the affine differential sheaf and flat maps; none is used for an unstated theorem. Edge cases include the identity of Spec R (zero relative differentials), a polynomial affine line (one differential generator), nonreduced/non-Noetherian rings, and empty schemes (no x to choose). No reducedness, separatedness, field or characteristic hypothesis enters. All non-elementary proof steps cite existing statements, and citations.json copies their actual relevant text. Both such steps are under 2000 characters. No new clause-relabeling nodes or source-only proof steps were introduced, no hidden proof is moved into a new node, and the only off-unit results used as tools are already Mathlib leaves. All searches appended to the item were actually run with msearch.py and their logged hits were read. The proof is 2268 characters in total and retains all clauses of the item.
