## What changed

Completed the proof of `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_cyclic_data`
without changing its signature or existing docstring. Added proof-only imports of
`StalkNormalizationTraitSectionChartGenericFactor` and `GaloisCoverOpenFactorRationalPoint`.
The former isolates the geometric tame chart, including its generic polynomial factor,
without assuming the rational point. The latter imports only EtaleTorsor and is proved from the torsor identity:
locally select a coproduct component, lift a group translate through the open immersion,
and use full faithfulness of Spec to obtain an algebra map.
The item's proof extracts the polynomial root, proves it nonzero, constructs its unit,
and combines it with the chart's ideal and valuation data. The DAG follows this proof.
All three modules compile without warnings using the default heartbeat budget.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_cyclic_data`
(node `lem-sbc-stalk-normalization-trait-section-cyclic-data`); no sorry remains in the item.
Also proved the new
`AlgebraicGeometry.Scheme.GaloisCover.open_factor_rational_point`
(node `lem-sbc-galois-cover-open-factor-rational-point`) with no proof holes.

One new hole is left in
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_chart_generic_factor`
(node `lem-sbc-stalk-normalization-trait-section-chart-generic-factor`).
Its proof is exactly `by sorry`, with the complete geometric argument and source in its docstring.
Thus this delivery is a decomposition: one original hole closed, one geometric hole added,
net zero holes. The generic splitting and root extraction are actual Lean proofs;
the tame-chart construction remains to be formalized. No definitions or axioms were added.

## No longer needed

None. No existing imports were removed, and the original node had no proof dependencies.
The source's tame-chart and transverse-section route is retained; only its geometric
portion becomes the next item. The fully proved generic splitting theorem has no
additional Sheaf proof dependency. There are no obsolete delivered modules or nodes.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox's item path contained an unrelated raw higher-direct-image triangle
module with an unfinished trace_state proof. It was replaced by the repository's actual
item before completing this reduction. Its report also said no proof changes were made.
The existing DAG has three non-elementary proof steps with empty uses lists; there were
no named dependencies directly implementing those steps. The existing trait chart theorem
provides product charts but does not retain the divisor compatibility needed to identify
the uniformizer and transverse generic factor, so it alone cannot close this item.

The initial local compiler timeout was caused by reconstruction of the bundled function
field in a generic helper's interface. Taking F as CommRingCat and splitting elaboration
of the chart function from its application resolved it; no shared definitions or tools changed.
Empty fibres are vacuous; positive e makes the polynomial factor nonzero; the proof handles
disconnected G-torsors by the torsor coproduct identity. The remaining chart statement does
not assume splitting and asserts no root. It follows the construction before the two cases
in 0EYI and keeps the unit's trait/section route. No existing signatures were adapted.

## New nodes

`lem-sbc-stalk-normalization-trait-section-chart-generic-factor`:
`lean/Sheaf/AlgebraicGeometry/Morphisms/StalkNormalizationTraitSectionChartGenericFactor.lean`.
The geometric local ideal and valuation data together with the generic polynomial factor
as an open part of the section fibre, from 0EYH and the preliminary construction in 0EYI.
It is the single remaining geometric hole. Three search kinds are recorded; LeanSearch
was unavailable, and LeanFinder/library searches found no matching refinement.

`lem-sbc-galois-cover-open-factor-rational-point`:
`lean/Sheaf/AlgebraicGeometry/Morphisms/GaloisCoverOpenFactorRationalPoint.lean`.
A fully proved generic torsor lemma supplying an algebra map for every nonzero affine
open factor after field extension. It uses no trait or normalization assumptions.
Three search kinds are recorded; Mathlib's categorical primitives supply the proof,
while the additive EtaleTorsor argument provided the local coproduct-lifting pattern.
No change record is needed because all existing statements and interfaces are unchanged.

## Second reading by K2

1. Interface: PASS. Diffed the existing module and node against the repository.
   The existing theorem signature and docstring are byte for byte unchanged;
   only its proof and two plain proof imports changed. Neither new module exists
   in the repository. No definitions, target statements or forced adaptations changed.
2. Proof: PASS as a decomposition. All three modules compiled cleanly via lcompile.py.
   Scratch copies with #print axioms showed only propext, Classical.choice and Quot.sound
   for open_factor_rational_point; the chart and the item additionally use sorryAx,
   from the single named chart hole. Checked every delivered Lean file for forbidden
   declarations and hollow definitions: none. The chosen point in Spec A uses the proved
   Nonempty instance for a nonzero ring, not a witness from an unproved existence theorem.
3. Split statements: PASS. Read 0EYH and the construction in 0EYI before its two cases.
   The chart omits hZ and asserts no root; the torsor splitting and root extraction are
   strictly separate, proved parts of the original argument, not a renamed restatement.
   Checked the trivial-group case (e=1), a ramified Kummer trait (e>1 before splitting),
   empty fibres (no x), and disconnected torsors (the coproduct identity still applies).
   Both new statements have their source, full proof docstring and matching node.
   Independent LeanFinder searches for transverse DVR Kummer factors and sections of
   nonempty opens of trivial torsors, a Loogle AdjoinRoot/AlgHom search and rg on the
   library found no duplicate refinement. The existing product-chart statement does
   not assert compatibility of f with the closed divisor and cannot supply this lemma.
   The remaining geometry cannot be closed in a few minutes from those interfaces.
4. Route and pruning: PASS. The root proof uses Mathlib's direct AdjoinRoot evaluation
   identity and Units.ext. Read the source unit and its realized field: its entries
   are already empty in the repository; this delivery does not alter them or bypass
   the prescribed tame-chart / transverse-section route. The old proof_deps was empty,
   so there is no old node to list as unused. All existing public imports supply the
   unchanged interface; the two added imports are proof-only and both are used.
5. DAG: PASS. The existing node changes only proof, proof_deps and proof_origin.
   Its two proof dependencies are exactly the two invoked new theorems. Checked the
   new nodes' Lean signatures, sources, searches, creation records, unit/chapter and
   blueprint provenance. Their proof steps describe the displayed Lean argument or,
   for the chart, the remaining sourced geometric construction.

Second-reading change: removed the redundant public import
Mathlib.AlgebraicGeometry.OpenImmersion from the new rational-point module, verified
by compiling its scratch copy without that import and checking its axioms. EtaleTorsor
already exposes the required interface and proof primitives. No mathematical proof or
statement repair was necessary. No additional holes were closed or added: one original
hole closed, one geometric hole added (decomposition, net zero), plus the new rational-point
lemma proved. No existing node or module was pruned.
