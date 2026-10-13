# AlgebraicGeometry.affineBaseChangeIntoPullback

## Reason

The two new proof dependencies must refer to the source-only stalk map without
importing the theorem they prove. Relocate the existing definition to
`Sheaf.Algebra.Homology.AffineBaseChangeIntoPullback`, publicly re-exported by the
item. Its name, universes, binders, visibility and value stay the same. Spell out
its previously inferred morphism type to avoid unfolding its composite merely to
infer `Arrow.mk r` and the source carrier. This annotation is definitionally equal
to the old inferred type. No target statement or mathematical definition changes.

## Old

The item declared the following definition directly:

```lean
/-- The localized comparison ending in stalks of the pullback cohomology sheaf,
before any morphism from that pullback is applied. Source: Stacks, Tag 0DJ8.
(blueprint: lem-pc-affine-base-change-source-model). -/
def affineBaseChangeIntoPullback
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (K : schemeDerivedCategory X)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) (p : X') (i : ℤ) :=
  letI := SingleComplexBaseChange.leftAlgebra f g' p
  letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
  letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
  letI := hc
  let T := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) i
  let s := RingedSpace.moduleStalkFunctor X'.toRingedSpace p
  (SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).localizedComparison i ≫
    HomologicalComplex.homologyMap
      (SingleComplexBaseChange.tensorStalkIso f f' g g' sq p P).hom i ≫
    (affineRepresentativeStalkIso X' p T i).inv ≫
    s.map (H.map (inv ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ (derivedPullback g').map e.hom))

```

## New

The item publicly imports `Sheaf.Algebra.Homology.AffineBaseChangeIntoPullback`.
That module now declares:

```lean
/-- The localized comparison ending in stalks of the pullback cohomology sheaf,
before any morphism from that pullback is applied. Source: Stacks, Tag 0DJ8.
(blueprint: def-pc-affine-base-change-into-pullback). -/
def affineBaseChangeIntoPullback
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (K : schemeDerivedCategory X)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) (p : X') (i : ℤ) :
    letI := SingleComplexBaseChange.leftAlgebra f g' p
    letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
    letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
    (ModuleCat.extendScalars (algebraMap
      (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
        SingleComplexBaseChange.B f' p) (SingleComplexBaseChange.C p))).obj
          ((SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).cohomology i) ⟶
      (RingedSpace.moduleStalkFunctor X'.toRingedSpace p).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) i).obj
            ((derivedPullback g').obj K)) :=
  letI := SingleComplexBaseChange.leftAlgebra f g' p
  letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
  letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
  letI := hc
  let T := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) i
  let s := RingedSpace.moduleStalkFunctor X'.toRingedSpace p
  (SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).localizedComparison i ≫
    HomologicalComplex.homologyMap
      (SingleComplexBaseChange.tensorStalkIso f f' g g' sq p P).hom i ≫
    (affineRepresentativeStalkIso X' p T i).inv ≫
    s.map (H.map (inv ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ (derivedPullback g').map e.hom))

```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.AffineBaseChangeSourceModel | V3 | Publicly re-exports the identical construction and uses the two computation lemmas. |
| Sheaf.Algebra.Homology.AffineBaseChangeCohomologyModel | unclaimed | Existing use and unfolding see the same declaration through the public re-export; no adaptation. |

`tools/downstream.py --uses affineBaseChangeIntoPullback` found these two textual
users. All transitive importers retain the same definition and theorem signatures;
no original module is adapted. In particular, targets using this definition have
identical meaning, so no semantic target review is reopened.

## Status

landed 20261013T130037-L-3924354 2026-10-13 (merge of deliver/V3/Sheaf.Algebra.Homology.AffineBaseChangeSourceModel)
