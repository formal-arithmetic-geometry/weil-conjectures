## What changed

Completed `AlgebraicGeometry.Etale.compactProjectionMapCoeffFirst_baseChangeMap` by symmetry
conjugation of the upstream right-coefficient exchange theorem. The private categorical
lemmas `symmetryPasting` and `coefficientFirstExchange` perform the pasting before specialization,
so Lean need not repeatedly unfold the concrete sheaf tensor instances. The final
specialization uses the concrete coefficient type explicitly: a local type abbreviation
caused expensive definitional comparisons; the explicit specialization stays within the
standard limits.

Completed the retained `derivedPullback_tensorSymmetry` helper directly from the upstream
`leftDerivedUpperStar_map_braiding_hom_δ`. Refactored `EtaleDerivedTensorSymmetry` through the
proved generic `DerivedCategory.canonicalTensorSymmetry` interface to make this specialization
compile. Its equality with the old canonical package is proved by `rfl`.
Existing definitions have the same signatures and canonical maps. Change record:
`coord/changes/W4-derived-tensor-symmetry-generic-interface.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.compactProjectionMapCoeffFirst_baseChangeMap`.
The retained helper `AlgebraicGeometry.Etale.derivedPullback_tensorSymmetry`
(lem-asd-derived-pullback-symmetry) is also proved. Holes closed: 1 of 1 original;
holes added: 0; split off: 0. No `sorry` remains in any delivered module.
The generic equality lemma and both private pasting lemmas are proved; the generic symmetry
is a concrete construction, with no postponed data.

## No longer needed

The upstream `projectionMap_rightDerivedLowerShriekBaseChangeMap` already performs old
steps 1–5. This proof does not import or separately use:

- `Sheaf.Paper.RingedExchangeTensorCoherence`
  (lem-weil-pbc-ringed-exchange-tensor-coherence);
- `Sheaf.Paper.ProjectionMateExact` (lem-weil-pbc-ringed-projection-mate-exact);
- `Sheaf.AlgebraicGeometry.EtaleOpenProjectionExchange` (lem-asd-open-projection-exchange);
- `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal`
  (lem-kun-derived-pullback-composition-monoidal);
- `Sheaf.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange`
  (sbc-prop-extension-by-zero-and-arbitrary-base-change);
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets` (sbc-def-base-change-map).

Removed the obsolete tool-use approvals for `sbc-def-base-change-map`,
`sbc-prop-extension-by-zero-and-arbitrary-base-change`, `def-kun-projection-formula-map`,
`lem-weil-pbc-ringed-exchange-tensor-coherence`,
`lem-weil-pbc-ringed-projection-mate-exact`,
`lem-kun-derived-pullback-composition-monoidal`, `lem-kun-inverse-image-monoidal`, and
`lem-pur-etale-open-derived-tensor`. The tensor-symmetry approval is retained.
Pullback/tensor compatibility is now supplied by the proved helper node.

The proper projection invertibility statement lem-amb-proper-coproducts-projection is
unnecessary: the proof uses the projection map itself and naturality. The projection-map
and open-tensor definitions remain transitively used by the upstream compact projection.
Removed direct imports, whose declarations remain available through the upstream theorem:
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
`WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`,
`WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`, and
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`.
The removed `Sheaf.AlgebraicGeometry.ProperProjectionFormula` import supplies the unnecessary
proper projection invertibility statement mentioned above. The braided-pullback theorem is
imported only by the compatibility helper. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained attempt left the compatibility theorem open because direct specialization
triggered expensive monoidal-instance comparisons. Generic packaging of the actual derived
braiding removes that obstruction. The parent also selects the same local sheaf-braiding
instance as the upstream projection/exchange theorem. The original DAG's proper/open
pasting duplicates an upstream theorem, as its own step 5 notes. No mathematical statement was weakened.

Edge cases: identity pullbacks and zero objects require no additional assumption; zero
coefficient rings are allowed; no invertibility of exchange or projection is used.
The symmetry is still the canonical signed swap, by the proved generic equality.
The current consumer scan includes the duality hypotheses in
`Sheaf.Paper.CtfHomConditionB` and `Sheaf.Paper.CtfHomLocalizationDevissage`,
and the newer purity, coefficient-comparison, bidual-evaluation, and shift-conjugation
consumers listed in the change record. They use the same canonical map and require no
adaptation. `Sheaf.Paper.ShiftedTensorMorphismCalculus` instead defines a separate symmetry
with the same short name. The source scans use the supported uncached mode because
cached preflight scans wait repeatedly as the shared source state changes.
The resumed dry run reproduced the timeout in the pullback/symmetry helper after the earlier
compatibility edit. Selecting the named derived braiding in the generic wrapper fixes this:
Lean tries the current `braidedCategory'` name first and the earlier `braidedCategory` name
second. The localization package retains explicit isomorphism fields, compatible with both
source versions. The generic equality remains `rfl`. All three modules now compile without
warnings in 6.4, 10.4, and 13.5 seconds respectively, within the standard limits.
The latest retained source consumer scan lists 1782 modules and 33 textual declaration
users, covered by the change record. No consumer needs adaptation, because existing signatures
and the canonical map are unchanged. Delivery preflight and axiom checks are rerun below.

## New nodes

lem-asd-derived-pullback-symmetry, in
`lean/Sheaf/AlgebraicGeometry/DerivedPullbackTensorSymmetry.lean`, states the strictly simpler
pullback/symmetry square. It is proved, with no new hole, from the existing upstream braided
pullback theorem. Its proof is used twice, at g and g′, by the parent theorem.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
