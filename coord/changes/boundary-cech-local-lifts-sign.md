# AlgebraicGeometry.Scheme.Modules.boundary_cech_local_lifts

## Reason

The local-lift signs in this module and the recorded lower compatibility theorem disagree.
`boundary_cech_compatibility` gives `t₁ - t₀`, with exactly the canonical comparison and
`moduleCohomologyBoundary` of this module. The original statement instead requested
`t₀ - t₁` with the same boundary. Negating a cocycle also negates its image under the
linear comparison, so these cannot be interchanged while keeping the boundary fixed.

Stacks Tag 0B8S explicitly uses `t₀ - t₁`; the present correction follows the recorded
library boundary convention, as exposed by BoundaryCechCompatibility and explained in
BoundaryCechInjectiveMiddle. The latter computes the snake boundary as `-[q̃]` and the
comparison image of `t₁ - t₀` as the same class. This is a sign translation, not a
weakening or an additional hypothesis. Independent review should check this convention
against ModuleCohomologyBoundary before accepting the interface correction.

The lower compatibility theorem is still unproved and remains the next item. We do
not claim to have independently proved its sign computation. No target in Challenge,
no definition, no universe, and no binder is changed. Square-zero remains a hypothesis.
The unused proof-only SiteCechComplex import is removed; all public imports are retained.

## Old

```lean
theorem boundary_cech_local_lifts (X : Scheme.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C) (I : X.Modules)
    (j : I ⟶ B.toModule)
    (hzero : j ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (hshort : (ShortComplex.mk j
      ((commAlgebraSheafModuleFunctor X.sheaf).map p) hzero).ShortExact)
    (hsquare : ∀ (W : X.Opens) (a a' : I.val.obj (op W)),
      (@id (B.right.obj.obj (op W)) (j.val.app (op W) a)) *
        (@id (B.right.obj.obj (op W)) (j.val.app (op W) a')) = 0)
    {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤) :
    ∃ c : ((CategoryTheory.cechComplexFunctor U).obj I.presheafModuleCat).homology 1 ⟶
        (RingedSpace.moduleCohomology X.toRingedSpace 1).obj I,
      IsModuleCechComparison U I 1 c ∧ Function.Injective c ∧
      ∀ (f : C.right.obj.obj (op ⊤))
        (t : ∀ i : ι, B.right.obj.obj (op (U i))),
        (∀ i : ι, p.right.hom.app (op (U i)) (t i) =
          C.right.obj.map (homOfLE (le_top : U i ≤ ⊤)).op f) →
        ∃ z : ((CategoryTheory.cechComplexFunctor U).obj I.presheafModuleCat).cycles 1,
          (∀ x : Fin 2 → ι,
            j.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (x k)))
              ((Pi.π (fun y : Fin 2 → ι ↦
                I.presheafModuleCat.obj (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))) x)
                (((CategoryTheory.cechComplexFunctor U).obj I.presheafModuleCat).iCycles 1 z)) =
              B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (x k)) 0).op (t (x 0)) -
                B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (x k)) 1).op (t (x 1))) ∧
          c (((CategoryTheory.cechComplexFunctor U).obj I.presheafModuleCat).homologyπ 1 z) =
            RingedSpace.moduleCohomologyBoundary X.toRingedSpace
              (ShortComplex.mk j
                ((commAlgebraSheafModuleFunctor X.sheaf).map p) hzero) hshort 0
              ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
                C.toModule f)
```

## New

```lean
theorem boundary_cech_local_lifts (X : Scheme.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C) (I : X.Modules)
    (j : I ⟶ B.toModule)
    (hzero : j ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (hshort : (ShortComplex.mk j
      ((commAlgebraSheafModuleFunctor X.sheaf).map p) hzero).ShortExact)
    (hsquare : ∀ (W : X.Opens) (a a' : I.val.obj (op W)),
      (@id (B.right.obj.obj (op W)) (j.val.app (op W) a)) *
        (@id (B.right.obj.obj (op W)) (j.val.app (op W) a')) = 0)
    {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤) :
    ∃ c : ((CategoryTheory.cechComplexFunctor U).obj I.presheafModuleCat).homology 1 ⟶
        (RingedSpace.moduleCohomology X.toRingedSpace 1).obj I,
      IsModuleCechComparison U I 1 c ∧ Function.Injective c ∧
      ∀ (f : C.right.obj.obj (op ⊤))
        (t : ∀ i : ι, B.right.obj.obj (op (U i))),
        (∀ i : ι, p.right.hom.app (op (U i)) (t i) =
          C.right.obj.map (homOfLE (le_top : U i ≤ ⊤)).op f) →
        ∃ z : ((CategoryTheory.cechComplexFunctor U).obj I.presheafModuleCat).cycles 1,
          (∀ x : Fin 2 → ι,
            j.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (x k)))
              ((Pi.π (fun y : Fin 2 → ι ↦
                I.presheafModuleCat.obj (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))) x)
                (((CategoryTheory.cechComplexFunctor U).obj I.presheafModuleCat).iCycles 1 z)) =
              B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (x k)) 1).op (t (x 1)) -
                B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (x k)) 0).op (t (x 0))) ∧
          c (((CategoryTheory.cechComplexFunctor U).obj I.presheafModuleCat).homologyπ 1 z) =
            RingedSpace.moduleCohomologyBoundary X.toRingedSpace
              (ShortComplex.mk j
                ((commAlgebraSheafModuleFunctor X.sheaf).map p) hzero) hshort 0
              ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
                C.toModule f)
```

## Users

`tools/downstream.py --uses boundary_cech_local_lifts` finds no external declaration
callers. Its two transitive importers are listed below. Both direct importers are
BoundaryDerivationAlgebraicData and BoundaryDerivationSquareZero: their signatures
contain neither cocycles nor this theorem, so the sign correction changes no statement.
Their originals compiled against the corrected module without adaptations.
The derivation proof still works with the reversed differences: simultaneously
reversing alpha, beta and gamma preserves gamma = g alpha + f beta. The older prose
in BoundaryDerivationSquareZero uses the source convention; no forced Lean edit is needed.
All targets' definitions and signatures remain identical, so no target review reopens.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BoundaryCechLocalLifts | F2 | Recorded sign correction; original signature is not claimed proved |
| Sheaf.Paper.BoundaryDerivationAlgebraicData | unclaimed | Signature unchanged; no call of the changed declaration |
| Sheaf.Paper.BoundaryDerivationSquareZero | unclaimed | Signature unchanged; no call of the changed declaration |

## Status

landed 20261013T000044-L-2231247 2026-10-13 (merge of deliver/F2/Sheaf.AlgebraicGeometry.BoundaryCechLocalLifts)
