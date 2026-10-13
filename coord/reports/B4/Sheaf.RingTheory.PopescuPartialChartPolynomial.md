## What changed

Proved `Algebra.popescu_partial_chart_polynomial` in
`Sheaf.RingTheory.PopescuPartialChartPolynomial`, preserving its entire signature,
public imports, definitions, and existing docstring. Added proof-only imports of
`Sheaf.RingTheory.PopescuZeroBaseSingleChartPolynomial` and
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`.

The proof compares the partial quotient with the quotient imposing all original
relations and the fixed chart's relations. In the localized scalar extension,
selected f_j vanish. The prepared relation and invertibility of a_k force all f_l
to vanish. Normalization makes each selected auxiliary relation identically zero.
Tensor right exactness and localization then make the natural surjection an
isomorphism. Compose its inverse with the existing single-chart polynomial model
and reindex E_k by Fin(card E_k). The localization argument applies the existing Mathlib declarations
`IsLocalization.Away.map_injective_iff`, `IsLocalization.map_eq_zero_iff` and
`IsLocalization.Away.mapₐ_surjective_of_surjective` directly inside the proof.
The repair removes the duplicate private theorem `localized_surjection_bijective`.
Its namesake in `PopescuZeroBaseChartPolynomial` is private and cannot be imported
as a callable declaration; no visibility or interface of that other module is changed.

Updated the item's node proof, proof_deps and proof_origin to record this route.
The unit's statement and realized proof steps are unaffected: this is a calculation
below those steps. Source checked against Stacks Project Tag 07CP,
https://stacks.math.columbia.edu/tag/07CP, the displayed partial-chart calculation.

Validation: the complete module compiles cleanly through lcompile.py, within the
single-file limit. The proof assumes no nontriviality or nonempty free-variable set;
it includes the empty E_k, all auxiliary variables selected, and zero-ring cases.

## Proved and sorry left

Closed 1 of 1 local holes: `Algebra.popescu_partial_chart_polynomial`
(node `lem-weil-pbc-popescu-partial-chart-polynomial`). No sorry remains in the item
and no holes were added or split off elsewhere.

This is a proof from existing declarations, not a claim that its complete axiom
closure is already sorry-free. The imported single-chart polynomial theorem is
proved from the existing presentation lemma
`Algebra.PopescuLiftPresentation.zero_base_single_chart_presentation`
(node `lem-weil-pbc-popescu-zero-base-single-chart-presentation`), which currently
has sorry. That module is unchanged and is an existing imported proof obligation.

## No longer needed

The duplicate private helper is no longer needed. No original imports were removed: the sole original import supplies the statement's
presentation data. No modules can be claimed globally pruned by this delivery.

The item's direct dependency on
`lem-weil-pbc-algebra-localization-away-base-change` is removed: the coefficient-ring
identification and variable elimination are supplied by the existing single-chart
polynomial theorem. The other original generic dependency nodes remain for renaming,
tensor extension and localization. Their direct hand-written coefficient quotient
and elimination calculation is no longer needed in this module. The base-change
result may still be needed inside the single-chart presentation; no global pruning
of it is asserted.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The node's earlier search had
identified the single-chart quotient as different over R, but its existing theorem
can be reused after killing pi and inverting a_k. The comparison has been proved
here, using only Prepared.relation, normalized_h and normalized_g; no conormal,
smoothness or differential-basis argument is needed for this comparison.

Searches: LeanFinder returned generic localization presentations; Loogle and grep
searched quotient equivalences and polynomial renaming. Local rg found the existing
single-chart polynomial theorem and its linear-elimination proof. The original
plan's dependency signatures and the single-chart presentation were read before
choosing this route. No additional nodes or interface changes are required.


The returned delivery correctly identified a duplicate private localization helper.
This repair removes that declaration entirely and applies the existing Mathlib
localization API directly at its sole use. The mathematical route and node
dependencies are unchanged. The earlier second reading's acceptance of the
duplicate helper was incorrect; that reading is removed pending a fresh reader.

Repair validation: lcompile.py compiled the repaired module cleanly in 12 seconds.

## Second reading by B4

1. PASS: compared the only delivered module with the repository using diff and
   independently compared the complete theorem signature byte for byte. Only its
   proof and two plain proof-only imports changed. No existing definition,
   docstring, public import, declaration visibility or target statement changed;
   no change record or forced adaptation is necessary.
2. PASS: compiled the repaired module through lcompile.py (13.8 seconds, no
   diagnostics). Replaced the stale scratch axiom probe with the current file and
   compiled it (14.1 seconds). The theorem's axioms are exactly propext,
   Classical.choice, Quot.sound and sorryAx. The latter is inherited from the
   existing zero_base_single_chart_presentation theorem, not introduced here.
   The delivered source has no sorry, axiom, unsafe, opaque, implemented_by or
   extern, and introduces no definitions or arbitrary existence-chosen data.
3. PASS: no statement is split off and no holes are added. Read the imported
   single-chart theorem and its presentation theorem: they have a different,
   full-original-relation quotient, so the comparison proved here is necessary.
   Checked the comparison for E_k empty (the empty sum forces every f_l=0),
   E_k all auxiliary indices (normalization kills every auxiliary equation),
   m=0, and the zero ring. No nontriviality or cancellation by a nonunit is used.
4. PASS: searched the project's RingTheory modules for partial-chart and
   single-chart polynomial models and localized-surjection proofs, and read
   Mathlib's tensor kernel API. The existing single-chart theorem is reused;
   the private helper in PopescuZeroBaseChartPolynomial is unavailable publicly,
   and the current proof correctly uses Mathlib's localization API directly.
   Both added imports supply declarations actually used. The original import
   supplies the statement's data. No original import is unused or removed.
   The old proof_deps minus the new proof_deps consists exactly of
   lem-weil-pbc-algebra-localization-away-base-change, already listed above.
   Read dag/units/sk-thm-p1.json including realized: this calculation lies below
   the unit steps and bypasses none of its realized nodes.
5. PASS: compared the old and delivered node JSON. Only proof, proof_deps and
   proof_origin changed. Checked each step against the Lean: quotient
   surjectivity, vanishing of J after scalar extension and localization,
   lTensor_ker and localized bijectivity, then the existing polynomial model
   and finite reindexing. The dependency list is the union of the steps' uses;
   the new single-chart dependency names its existing declaration. No new node
   is required.

Second-reading changes: corrected the report's description of the inherited
presentation obligation from downstream to imported, refreshed the scratch
axiom check to remove the obsolete private helper, and added this review.
The repaired Lean proof and DAG route required no further changes.
