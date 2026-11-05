/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Scalar extension homology is invariant among K-flat derived models

Source: Stacks Project, More on Algebra, Tags 064L and 06Y0.
(blueprint: lem-sc-kflat-scalar-extension-derived-iso).
-/

@[expose] public section

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CochainComplex

private theorem kFlat_of_acyclic_tensor
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ L : CochainComplex (ModuleCat.{u} R) ℤ, L.Acyclic →
      (mapBifunctor L P (curriedTensor _)).Acyclic) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (mapBifunctor N P (curriedTensor _))).2 (hP N hN)
  refine ⟨?_, hr⟩
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr

private theorem scalarExtension_quasiIso_of_kFlat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (a : P ⟶ Q)
    (ha : QuasiIso a)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat Q) :
    QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map a) := by
  let N := (HomologicalComplex.single (ModuleCat.{u} S) (.up ℤ) 0).obj (𝟙_ (ModuleCat S))
  let F := (ModuleCat.mixedTensor f).flip
  have h := (mixedTensor_kFlat_quasiIso f).1 N P Q a ha hP hQ
  let unit : (ModuleCat.mixedTensor f).obj (𝟙_ (ModuleCat S)) ≅
      ModuleCat.extendScalars f :=
    isoWhiskerLeft (ModuleCat.extendScalars f) (leftUnitorNatIso (ModuleCat S)) ≪≫
      Functor.rightUnitor _
  let e (K : CochainComplex (ModuleCat.{u} R) ℤ) :
      ((F.map₂CochainComplex).obj K).obj N ≅
        ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K :=
    mapBifunctorSingle₂Iso F (𝟙_ (ModuleCat S)) K ≪≫
      (NatIso.mapHomologicalComplex unit (.up ℤ)).app K
  apply (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e P) (e Q) (by
      change (e P).hom ≫ _ = _ ≫ (e Q).hom
      change ((mapBifunctorSingle₂Iso F (𝟙_ (ModuleCat S)) P).hom ≫
        ((NatIso.mapHomologicalComplex unit (.up ℤ)).app P).hom) ≫ _ =
        HomologicalComplex.mapBifunctorMap a (𝟙 N) F (.up ℤ) ≫
          ((mapBifunctorSingle₂Iso F (𝟙_ (ModuleCat S)) Q).hom ≫
            ((NatIso.mapHomologicalComplex unit (.up ℤ)).app Q).hom)
      rw [← Category.assoc, mapBifunctorSingle₂Iso_hom_naturality]
      simp only [Category.assoc]
      exact congrArg (fun t ↦ (mapBifunctorSingle₂Iso F (𝟙_ (ModuleCat S)) P).hom ≫ t)
        ((NatIso.mapHomologicalComplex unit (.up ℤ)).hom.naturality a).symm))).1 h

end CochainComplex
