/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Comparison of the canonical injective resolutions

(blueprint: lem-pur-comparison-injective-resolution-homotopy).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits

private theorem kInjective_Q_map_surjective
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Surjective (DerivedCategory.Q.map : (K ⟶ L) → _) := by
  intro f
  let a := (DerivedCategory.quotientCompQhIso C).app K
  let b := (DerivedCategory.quotientCompQhIso C).app L
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj K) L).surjective (a.hom ≫ f ≫ b.inv)
  obtain ⟨t, ht⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨t, ?_⟩
  apply (cancel_epi a.hom).mp
  have he := DerivedCategory.quotientCompQhIso_hom_naturality t
  simpa [a, b, ht, hg] using he.symm

open AlgebraicGeometry
/-- An abelian injective resolution on the etale site is homotopy equivalent to the
comparison direct image of an injective resolution of its inverse image.
Source: Stacks 099W and the comparison acyclicity proof of 099V.
(blueprint: lem-pur-comparison-injective-resolution-homotopy).

Proof: inverse image is exact, so the image of the etale resolution and the chosen
pro-etale resolution are quasi-isomorphic. Lift their derived isomorphism to a chain
map using K-injectivity of the target. The image resolution has direct-image-acyclic
terms, as does the injective target, so direct image preserves this quasi-isomorphism.
Compose with the termwise invertible comparison unit. Both resulting complexes are
K-injective: direct image is right adjoint to an exact functor. A quasi-isomorphism
between K-injective complexes is a homotopy equivalence. -/
theorem AlgebraicGeometry.ProEtale.comparisonInjectiveResolutionHomotopyEquiv
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty (HomotopyEquiv (injectiveResolution F).cochainComplex
      (((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
        (.up ℤ)).obj (injectiveResolution
          ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).obj F)).cochainComplex)) := by
  let L := ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X
  let R := ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X
  let I := injectiveResolution F
  let J := injectiveResolution (L.obj F)
  let LI := (L.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  have : I.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective I.cochainComplex 0
  have : J.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective J.cochainComplex 0
  let a : (CochainComplex.singleFunctor _ 0).obj (L.obj F) ⟶ LI :=
    (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).inv.app F ≫
      (L.mapHomologicalComplex (.up ℤ)).map I.ι'
  have : QuasiIso a := by dsimp [a]; infer_instance
  let f := (asIso (DerivedCategory.Q.map a)).inv ≫ DerivedCategory.Q.map J.ι'
  obtain ⟨t, ht⟩ := kInjective_Q_map_surjective LI J.cochainComplex f
  have : QuasiIso t := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).mp
    rw [ht]
    dsimp [f]
    infer_instance
  have : CochainComplex.IsStrictlyGE LI 0 := by dsimp [LI]; infer_instance
  have : QuasiIso ((R.mapHomologicalComplex (.up ℤ)).map t) :=
    R.quasiIso_map_of_rightAcyclic t 0
      (fun n ↦ ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective
        AddCommGrpCat.{u + 1} X (I.cochainComplex.X n))
      (fun n ↦ Functor.rightAcyclic_of_injective (F := R) (J.cochainComplex.X n))
  let unit := ((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).mapHomologicalComplex
    (.up ℤ)).unit.app I.cochainComplex
  have : IsIso unit := by
    have (n : ℤ) : IsIso (unit.f n) := by
      change IsIso ((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app _)
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components unit
  let c : I.cochainComplex ⟶ (R.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex :=
    unit ≫ (R.mapHomologicalComplex (.up ℤ)).map t
  have : QuasiIso c := by dsimp [c]; infer_instance
  have : R.PreservesKInjectiveComplexes :=
    (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).preservesKInjectiveComplexes
  have : CochainComplex.IsKInjective
      ((R.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex) := inferInstance
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff c).mp inferInstance
  exact ⟨e⟩
