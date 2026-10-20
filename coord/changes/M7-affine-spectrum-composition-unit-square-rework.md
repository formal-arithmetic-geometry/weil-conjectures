# affineSpectrum_composition_unit_square

## Reason

The assigned Sheaf module was quarantined after the upstream sync: it tries to
mark `derivedPullback` locally irreducible although the imported upstream
construction is already an `irreducible_def`. The upstream unit-square module
already provides the identical public theorem and a complete proof. Reuse that
implementation, avoiding duplicate declarations and obsolete local attributes.

## Old

The quarantined module has this public import, followed by fully proved private
coherence helpers, local reducibility commands and the public theorem
`AlgebraicGeometry.affineSpectrum_composition_unit_square`:

```lean
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates
```

The original public signature, also provided verbatim by the upstream module, is:

```lean
theorem affineSpectrum_composition_unit_square
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X) (K : schemeDerivedCategory X) :
  let c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  let i : ∀ Y : Scheme.{u}, derivedPullback (𝟙 Y) ≅ 𝟭 _ :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec exists_derivedPullbackComposition)))).2
  (affineSpectrumForwardPullbackIso g').hom.app ((derivedPullback X.isoSpec.inv).obj K) ≫
      (derivedPullback X'.toSpecΓ).map
        ((affineSpectrumDerivedPullbackIso g').hom.app K) ≫
      (c X'.isoSpec.hom X'.isoSpec.inv ≪≫
      eqToIso (congrArg (fun k : X' ⟶ X' ↦ derivedPullback k) X'.isoSpec.hom_inv_id) ≪≫
      i X').hom.app ((derivedPullback g').obj K) =
    (derivedPullback g').map
      ((c X.isoSpec.hom X.isoSpec.inv ≪≫
      eqToIso (congrArg (fun k : X ⟶ X ↦ derivedPullback k) X.isoSpec.hom_inv_id) ≪≫
      i X).hom.app K)
```

Its DAG Lean attachment names
`Sheaf.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare`.

## New

The former Sheaf path is a compatibility module whose only import is:

```lean
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare
```

The upstream module supplies exactly the old public statement and its complete
proof. The DAG Lean attachment names that upstream module. No theorem signature
or definition changes, and no upstream source is edited.

For the returned landing at `2b4dbbb5ca`, reconcile against current
`sheaf-dag` at `28f23e0d1ee`: the item remains quarantined and the upstream
implementation is unchanged. Restore the compatibility module on the freshly
fetched delivery base, with an explicit `@[expose] public section` after its
module docstring. Preserve the quarantine archive and all node dependencies.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare | M7 | Replaced the quarantined duplicate by a compatibility import of the identical upstream theorem. |

No current module in `lean/` or `quarantine/` imports this Sheaf module.
The upstream module is imported by
`WeilConjectures.AlgebraicGeometry.AffineSpectrumComparisonCancellation`
and the upstream root; both remain unchanged. All former public names and
imports remain available through the compatibility module. No forced adaptation.

## Status

landed 20261020T154938-L-3174869 2026-10-20 (merge of deliver/M7/Sheaf.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare)
