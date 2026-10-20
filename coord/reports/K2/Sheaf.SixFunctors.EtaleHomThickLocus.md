## What changed

Constructed the evaluation-transpose family in `EtaleHomThickLocus`, with naturality
in both variables, directly from the published parametrized tensor-Hom adjunction.
Proved the five thick-locus clauses using the Mathlib exact-functor, triangle and
retract APIs. The reversed-exactness argument is a separate genuine step, not a
renamed copy of the original theorem: it takes an already constructed transformation
and proves only its signed exactness, with no construction, second-variable naturality
or isomorphism-locus conclusion.

Moved the fourteen original interface declarations to the publicly reexported
`EtaleHomComparisonModels` to avoid a cycle. One definition-body edit replaces
`H.flip.obj M |>.obj (op K)` by `(H.obj (op K)).obj M`, a definitional equality, in
the transpose predicate. The quadratic Hom-shift normalization and all target
signatures are preserved. Change records:
`coord/changes/K2-etale-hom-model-interface.md` and
`coord/changes/K2-etale-hom-tensor-normalization.md`.
The cochain normalization specializes the identical named generic predicate; this
avoids repeated kernel conversion between the same preadditive and zero-morphism
instances in the expanded equation. The explicit tensor bifunctor in that predicate
is definitionally the original cochain tensor. Its module is publicly imported
because the public definition uses it.

Proved the tensor comparison via a new general theorem for a strong monoidal left
adjoint preserving flat objects. This generalizes the adopted exact-functor proof
by using models that are both K-flat and have K-flat image. It does not assume the
ordinary scalar extension exact. Proved separately the precise cochain counit identity
for a chosen derived left adjoint, including the quotient-to-homotopy maps. Stalkwise
flat base change and faithful exact restriction establish the scalar hypotheses.
Canonical monoidal structures are cached locally in the private tensor argument to
avoid repeatedly elaborating localization and cochain tensor structures.

Validation: all five delivery modules compile (the model module in 44.5 seconds,
the main module in 48.9 seconds). The five direct consumers
`CoefficientChangeDualizing`, `CtfHomCoefficientComparison`, `EtaleGeometricBiduality`
`EtaleOpenTensor`, and `InternalAdjunctionPairingChange` compile unchanged against the packet. The normalization predicate
checks by `rfl` against the expanded ordinary equation in abstract categories. A direct
expanded comparison after sheaf specialization still reaches the known conversion
timeout; this is the conversion avoided by the named interface. The independent
reader should check this definitional presentation change. Axiom checks for the
scalar tensor theorem and both new general theorems show exactly `propext`,
`Classical.choice`, and `Quot.sound`. The main theorem signature is verbatim unchanged.

## Proved and sorry left

Original holes closed:

- `AlgebraicGeometry.Etale.etaleHomTensorComparison_existsUnique`: proved from the
  derived bifunctor universal property, flat resolutions, and the cochain counit formula.
- `AlgebraicGeometry.Etale.etaleHomComparison_thickLocus`: constructed the transformation,
  both naturalities, and its thick locus, conditional on the separate exactness lemma.
  This part is a decomposition, not a complete proof of the remaining exactness argument.

Proved new public results:

- `CategoryTheory.Adjunction.leftDerivedCochainCounit`.
- `CategoryTheory.Functor.rightExact_tensorComparison_existsUnique`.

One hole added and remaining in the packet:

- `AlgebraicGeometry.Etale.etaleHomComparison_reversedExact`, in
  `Sheaf.SixFunctors.EtaleHomTransposeExact`, node
  `lem-coef-etale-hom-transpose-exact`. Its docstring gives the complete signed
  Hom-complex, cone and scalar-balancing proof. The actual number of retained
  `sorry` terms is one. No `sorry` occurs in a definition or private helper.

Thus two original holes are filled, one separate hole remains: net one hole closed.
There are no holes in the item module or the tensor-model module.

## No longer needed

Removed all eleven original private proof imports from the item and models:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.Algebra.Homology.DerivedScalarExtensionCounitShift`
- `WeilConjectures.Algebra.Homology.HomComplex`
- `WeilConjectures.Algebra.Homology.HomTensorTotal`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The main node directly uses the new normalized tensor comparison, the exactness
step, and the triangle-isomorphism lemma. All nine existing tool approvals remain
in their original order; none is added or replaced. The tensor-pullback lemma
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` is unnecessary for the new tensor
existence proof, which uses the two-variable universal property. The old Hom,
shift, resolution and descent dependencies remain in the proof plan of the new
exactness node where needed; their transitive dependencies are not claimed
pruned globally.
No existing module is withdrawn, and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The adopted `Functor.leftDerivedTensorComparison` assumes ordinary exactness.
Ordinary extension along an arbitrary A→B is not exact, so it cannot be used directly.
The correct resolving class is the intersection of source K-flat models and models
with K-flat scalar image; flat resolutions provide this class. This repairs the
proof route without adding a flatness hypothesis on B.

The existing ringed-Hom statements use a different module-sheaf presentation and
provide no direct normalized-shift identification with the published étale
`derivedHom`. Merely importing them does not prove the exactness clause. The new
exactness node records precisely the remaining compatibility for that actual Hom.
The unit `sk-prop-sf-biduality-general` has empty realized statement/step lists;
its route is retained through the original main node.

## New nodes

`lem-coef-etale-tensor-model-comparison`: the original tensor-existence obligation
and unchanged common interface, now in `EtaleHomComparisonModels`.

`lem-derived-right-exact-tensor-comparison`: the proved general normalized tensor
comparison, in `DerivedTensorRightExact`.

`lem-derived-adjoint-cochain-counit`: the proved chosen-adjunction cochain counit
formula, in `DerivedAdjointCochainCounit`.

`lem-coef-etale-hom-transpose-exact`: the one remaining exactness step, in
`EtaleHomTransposeExact`. It is strictly part of the original argument.

The interface relocation and definitional spelling are recorded in
`coord/changes/K2-etale-hom-model-interface.md` and
`coord/changes/K2-etale-hom-tensor-normalization.md`.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
