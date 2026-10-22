# AlgebraicGeometry.derivedPullbackComposition_tensor_kFlat

## Reason

Restore the assigned zero-hole quarantine item using its complete adopted source
implementation. The archived Sheaf file would duplicate the existing public
AlgebraicGeometry.derivedPullbackComposition_tensor_kFlat declaration. Its obsolete
IsAcyclicTensorKFlat spelling differs from the source's IsKFlatTensor; the two
predicates have identical definition bodies. The full archived theorem statement
AND proof equal the adopted theorem statement and proof after only that rename.

The restored Sheaf module publicly imports the adopted theorem and the legacy
K-flat interface, preserving the old import path and its usable statement without
redeclaring the theorem. Its DAG attachment now identifies the source declaration.
All statement dependencies, proof dependencies and proof steps remain intact.
The quarantine archive, the adopted source and every target are unchanged.
This is an actual restoration of a missing module, not a withdrawal or a rebase.

## Old

In the quarantined Sheaf module, with universes u w and the unchanged assumption
[∀ Z : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]:

```lean
theorem derivedPullbackComposition_tensor_kFlat
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (hN : N.IsAcyclicTensorKFlat) :
    let c : ∀ {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W),
        derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
      fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) a b
    (derivedPullback f).map ((mixedHomTensorPullbackIso g).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
      (mixedHomTensorPullbackIso f).hom.app
        ((derivedPullback g).obj (DerivedCategory.Q.obj P),
          (derivedPullback g).obj (DerivedCategory.Q.obj N)) ≫
      ((c f g).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
        (c f g).hom.app (DerivedCategory.Q.obj N)) =
    (c f g).hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N) ≫
      (mixedHomTensorPullbackIso (f ≫ g)).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)
```

The archive declared this theorem locally with a complete proof and imported
Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso publicly, plus
CanonicalPullbackTensorComparison (all) and
DerivedPullbackTensorSuccessiveNormalization privately.

## New

The restored module publicly imports
WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat and
Sheaf.Algebra.Homology.KFlat. The existing source theorem has the same universes
and derived-category assumption, with this signature:

```lean
theorem derivedPullbackComposition_tensor_kFlat
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hN : N.IsKFlatTensor) :
    let c : ∀ {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W),
        derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
      fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) a b
    (derivedPullback f).map ((mixedHomTensorPullbackIso g).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
      (mixedHomTensorPullbackIso f).hom.app
        ((derivedPullback g).obj (DerivedCategory.Q.obj P),
          (derivedPullback g).obj (DerivedCategory.Q.obj N)) ≫
      ((c f g).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
        (c f g).hom.app (DerivedCategory.Q.obj N)) =
    (c f g).hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N) ≫
      (mixedHomTensorPullbackIso (f ≫ g)).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)
```

The only difference is the definitionally identical predicate name. A compiled
consumer checks predicate equality by rfl and applies the source theorem at the
full verbatim archived signature. Thus all hypotheses, chosen composition maps,
tensorators and conclusions agree, including zero complexes, identity morphisms
and empty schemes without further assumptions.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat | F4 | Restore public import path; reuse the existing complete theorem. |
| Sheaf.AlgebraicGeometry.MixedPullbackSquareTensorCoherence | unclaimed (quarantined) | Existing theorem application at line 167 remains valid with legacy K-flat hypotheses; the full-signature consumer verifies it. No adaptation. |
| WeilConjectures.AlgebraicGeometry.MixedPullbackSquareTensorCoherence | unclaimed | Already imports the unchanged adopted theorem directly. No effect or adaptation. |

The read-only tools/downstream.py query with --allow-missing and --uses finds
zero live downstream modules or textual users of the absent Sheaf path. A separate
search of quarantine finds the parent above. Its dependency and the item's node
are preserved. Zero live importers is not used to withdraw either module.
No declaration signature, visibility, definition or proof in another module changes.

## Status

landed 20261022T013410-L-3563426 2026-10-22 (merge of deliver/F4/Sheaf.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat)
