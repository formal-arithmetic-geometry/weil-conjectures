/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap

import WeilConjectures.AlgebraicGeometry.ModulePullbackComparisonTargetAutomorphism
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeCoordinateNaturality
import WeilConjectures.AlgebraicGeometry.ModulePullbackComparisonIsoTransport

/-! # Coordinate compatibility with a prescribed module comparison

## References

* Stacks Project, Tags 06YJ, 08HY, 0D5T and 08IB
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

set_option maxHeartbeats 700000 in
-- Elaborating the coordinate functors repeatedly compares nested chosen pullback objects.
/-- Coordinate-change isomorphisms identify the canonical module base-change maps
(Stacks, Tags 08HY and 0D5T). -/
theorem canonicalModuleBaseChange_iso_comparison_ab
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (G : X.Modules)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (hc : IsDerivedModulePullbackComparison g' G c)
    {A B : Scheme.{u}} (eS : S ≅ A) (eT : S' ≅ B)
    (c0 : (derivedPullback (pullback.fst (f ≫ eS.hom)
      (eT.inv ≫ g ≫ eS.hom))).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback (f ≫ eS.hom)
          (eT.inv ≫ g ≫ eS.hom)).toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback (pullback.fst (f ≫ eS.hom)
          (eT.inv ≫ g ≫ eS.hom))).obj G))
    (hc0 : IsDerivedModulePullbackComparison
      (pullback.fst (f ≫ eS.hom) (eT.inv ≫ g ≫ eS.hom)) G c0) :
  let fA := f ≫ eS.hom
      let gA := eT.inv ≫ g ≫ eS.hom
      let E := (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
      let T := schemeDerivedDirectImage eT.inv
      ∃ a : (derivedPullback g).obj ((schemeDerivedDirectImage f).obj E) ≅
            T.obj ((derivedPullback gA).obj ((schemeDerivedDirectImage fA).obj E)),
        ∃ b : (schemeDerivedDirectImage f').obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
                  ((Scheme.Modules.tensorPullback g').obj G)) ≅
            T.obj ((schemeDerivedDirectImage (pullback.snd fA gA)).obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj G))),
          (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
              (schemeDerivedDirectImage f').map c) ≫ b.hom =
            a.hom ≫ T.map
              (schemeDerivedBaseChangeMap fA (pullback.snd fA gA) gA (pullback.fst fA gA)
                pullback.condition E ≫ (schemeDerivedDirectImage (pullback.snd fA gA)).map c0)
       := by
  classical
  dsimp only
  let fA := f ≫ eS.hom
  let gA := eT.inv ≫ g ≫ eS.hom
  let p := pullback.fst fA gA
  let q := pullback.snd fA gA
  let E := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
  let M := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
      ((Scheme.Modules.tensorPullback g').obj G)
  let S0 := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0
  let R := schemeDerivedDirectImage q
  let T := schemeDerivedDirectImage eT.inv
  obtain ⟨e, hp, _, j, k, a, hβ⟩ :=
    exists_derivedBaseChange_coordinate_naturality f g g' f' sq eS eT
  obtain ⟨cT, hcT, m, hm⟩ :=
    exists_modulePullbackComparison_iso_transport g' p e hp j G c hc
  obtain ⟨α, hα⟩ := modulePullbackComparison_target_automorphism p G c0 cT hc0 hcT
  let b0 := k.app M ≪≫ T.mapIso (R.mapIso m)
  let d := T.mapIso (R.mapIso (S0.mapIso α))
  refine ⟨a.app E, b0 ≪≫ d.symm, ?_⟩
  have hcompat :
      (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
          (schemeDerivedDirectImage f').map c) ≫ b0.hom =
        (a.hom.app E ≫ T.map
          (schemeDerivedBaseChangeMap fA q gA p pullback.condition E ≫ R.map c0)) ≫
            d.hom := by
    have hn : (schemeDerivedDirectImage f').map c ≫ k.hom.app M =
        k.hom.app ((derivedPullback g').obj E) ≫
          T.map (R.map ((schemeDerivedDirectImage e.hom).map c)) := k.hom.naturality c
    calc
      _ = schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
          k.hom.app ((derivedPullback g').obj E) ≫
          T.map (R.map ((schemeDerivedDirectImage e.hom).map c ≫ m.hom)) := by
            dsimp only [b0, Iso.trans_hom, Functor.mapIso_hom]
            simp only [Functor.map_comp, Category.assoc]
            change _ ≫ (schemeDerivedDirectImage f').map c ≫
              k.hom.app M ≫ T.map (R.map m.hom) = _
            rw [← Category.assoc ((schemeDerivedDirectImage f').map c), hn]
            simp only [Category.assoc]
      _ = schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
          k.hom.app ((derivedPullback g').obj E) ≫
          T.map (R.map (j.hom.app E ≫ cT)) := by rw [hm]
      _ = (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
          k.hom.app ((derivedPullback g').obj E) ≫
          T.map (R.map (j.hom.app E))) ≫ T.map (R.map cT) := by
            simp only [Functor.map_comp, Category.assoc]
      _ = (a.hom.app E ≫ T.map
          (schemeDerivedBaseChangeMap fA q gA p pullback.condition E)) ≫
          T.map (R.map cT) := by rw [hβ E]
      _ = _ := by
        rw [hα]
        simp only [Functor.map_comp, Category.assoc]
        rfl
  change (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
    (schemeDerivedDirectImage f').map c) ≫ b0.hom ≫ d.inv = _
  rw [← Category.assoc, hcompat]
  simp
  rfl

end AlgebraicGeometry
