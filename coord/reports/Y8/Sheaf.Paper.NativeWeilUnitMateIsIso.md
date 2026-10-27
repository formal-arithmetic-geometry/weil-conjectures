## What changed

Proved `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_unit_mate_isIso` in
`Sheaf.Paper.NativeWeilUnitMateIsIso`, preserving its statement and public imports.
Added proof imports of `NativeWeilRingedTensorModel`,
`NativeHomRepresentativeUniqueness`, and Mathlib's `Adjunction.Unique`.

The existing ringed tensor model supplies a closed structure W, an invertible tensor
comparison t, its normalized Hom comparison chi, and the canonical unit-mate equation.
Representative uniqueness identifies the supplied eta with chi. For the supplied
adjunction a, the isomorphism `(W.adjunction K).leftAdjointUniq a` compares units.
A proved private lemma carries out the categorical calculation for arbitrary
categories, keeping large derived-category definitions out of elaboration.
Naturality of chi and of inverse ordinary transposition shows that the requested
mate equals t inverse followed by the forgotten adjoint isomorphism. Both factors
are invertible. No adjunction normalization is imposed on a.

Updated only the item's DAG proof, proof dependencies and proof origin to record
this reuse and the explicit formal calculation. No definition, signature,
instance, attribute or public import changed. No other module requires adaptation.
The unit record has no realized statements or proof steps that this route bypasses.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_unit_mate_isIso`
(node `lem-sf-native-weil-unit-mate-iso`).

Zero holes remain in the item. Zero holes were added, and zero statements were
split off. The final single-file server compile passed in 11.4 seconds.
This proof uses existing declared dependencies; it does not claim
that all their underlying geometric proof obligations are closed.

## No longer needed

No existing import was removed and no module is withdrawn or claimed globally
pruned. The direct proof-dependency list now uses
`lem-sf-native-weil-ringed-tensor-model` and
`lem-sf-native-hom-representative-uniqueness`.

The former direct dependencies are no longer needed as direct applications here:
`lem-sf-weil-frobenius-action-resolutions`,
`lem-sf-ringed-derived-tensor-hom-adjunction`,
`lem-sf-ringed-forget-two-injective-hom`,
`lem-sf-ringed-derived-closed-symmetric-monoidal`, and
`lem-weil-pbc-site-derived-tensor-descent`.
Their action-site, tensor, and representative calculations are already packaged
by the reused ringed tensor model. They may remain needed transitively and must
not be withdrawn on the strength of this delivery.

## Where the brief, the DAG or earlier work was wrong

The original DAG proposed reconstructing a resolution-defined adjoint and its
unit comparison. The library now already states and proves exactly that normalized
model in `native_weil_ringed_tensor_model`, with a separately proved uniqueness
lemma for Hom comparisons. Reusing these declarations leaves only the ordinary
categorical uniqueness-of-adjoints calculation. No mathematical statement was
changed. The rework row was checked before copying: the current source is present
and no longer imports the false-tail module named in that quarantine record.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
