/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SfIdentificationData
public import Mathlib.Algebra.Module.Injective
import WeilConjectures.AlgebraicGeometry.FiniteGeometricPointCohomology
import WeilConjectures.Algebra.Homology.DerivedCategory.HomToInjective
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Category.ModuleCat.Injective
import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective

/-! # Composition duality over a self-injective ring

Source: the finite-coefficient complement to the smooth identification.
(blueprint: lem-sf-scalar-composition-pairing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory

namespace WeilConjectures.SixFunctors

/-- Composition with the regular derived unit gives the perfect evaluation pairing
whenever the zeroth cohomology module is reflexive and the ring is self-injective.
Source: current blueprint sk-thm-sf-identification.proof.md, complement
(blueprint: lem-sf-scalar-composition-pairing).

Proof: projectivity of R identifies Hom(R[0],E) with H0(E). Injectivity of R
identifies Hom(E,R[0]) with the ordinary dual of H0(E). Under these two linear
isomorphisms composition, read through H0 and evaluated at 1, is ordinary
evaluation. Reflexivity makes evaluation perfect. Transport it through the two
linear isomorphisms. The specified single-unit isomorphism is used on both
sides, including when R is the zero ring. -/
theorem scalarCompositionPairing
    (R : Type (u + 1)) [CommRing R] [Module.Injective R R]
    (E : DerivedCategory (ModuleCat.{u + 1} R))
    [Module.IsReflexive R ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) 0).obj E)] :
    ∃ B : (𝟙_ _ ⟶ E) →ₗ[R] (E ⟶ 𝟙_ _) →ₗ[R] R,
      (∀ x f, B x f = identificationScalarValue (x ≫ f)) ∧ B.IsPerfPair := by
  let U := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0).obj
    (ModuleCat.of R R)
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) 0).obj E
  let e := DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u + 1} R)
  let φ : (𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)) ⟶ E) →ₗ[R] H :=
    { toFun := fun x =>
        ((DerivedCategory.homSingleToHomology (ModuleCat.of R R) 0 E
          (e.hom ≫ x)).hom) 1
      map_add' := by
        intro x y
        simp [DerivedCategory.homSingleToHomology]
      map_smul' := by
        intro r x
        simp [DerivedCategory.homSingleToHomology] }
  let ψ : (E ⟶ 𝟙_ (DerivedCategory (ModuleCat.{u + 1} R))) →ₗ[R] Module.Dual R H :=
    { toFun := fun f =>
        ModuleCat.homEquiv (M := H) (N := ModuleCat.of R R)
          (((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) 0).map (f ≫ e.inv)) ≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{u + 1} R) 0).hom.app (ModuleCat.of R R))
      map_add' := by
        intro f g
        ext z
        simp [Preadditive.add_comp, Functor.map_add, ModuleCat.homEquiv]
      map_smul' := by
        intro r f
        ext z
        simp [Linear.smul_comp, Functor.map_smul, ModuleCat.homEquiv] }
  let φ' : (𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)) ⟶ E) ≃ₗ[R] H :=
    LinearEquiv.ofBijective φ (by
    have hpre : Function.Bijective
        (fun x : (𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)) ⟶ E) ↦ e.hom ≫ x) := by
      constructor
      · intro x y h
        exact (cancel_epi e.hom).mp h
      · intro x
        exact ⟨e.inv ≫ x, by simp⟩
    let hRing : (U ⟶ E) ≃ H :=
      (DerivedCategory.homSingleEquivOfProjective (ModuleCat.of R R) 0 E).trans
        (ModuleCat.homEquiv.trans
          (LinearMap.ringLmapEquivSelf R ℕ _).toEquiv)
    have hcomp := hRing.bijective.comp hpre
    convert hcomp using 1
    funext x
    simp [φ, e, H, U, DerivedCategory.homSingleToHomology, hRing,
      ModuleCat.homEquiv])
  let ψ' : (E ⟶ 𝟙_ (DerivedCategory (ModuleCat.{u + 1} R))) ≃ₗ[R] Module.Dual R H :=
    LinearEquiv.ofBijective ψ (by
    have : CategoryTheory.Injective (ModuleCat.of R R) :=
      Module.injective_object_of_injective_module R R
    have hpre : Function.Bijective
        (fun f : (E ⟶ 𝟙_ (DerivedCategory (ModuleCat.{u + 1} R))) ↦ f ≫ e.inv) := by
      constructor
      · intro f g h
        exact (cancel_mono e.inv).mp h
      · intro f
        exact ⟨f ≫ e.hom, by simp⟩
    have hH := DerivedCategory.bijective_homologyFunctor_map_singleFunctor_of_injective
      E (ModuleCat.of R R)
    let q := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u + 1} R) 0).app (ModuleCat.of R R)
    have hq : Function.Bijective (fun g : H ⟶
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) 0).obj U ↦ g ≫ q.hom) := by
      constructor
      · intro g g' h
        exact (cancel_mono q.hom).mp h
      · intro g
        exact ⟨g ≫ q.inv, by simp⟩
    have hcomp := (ModuleCat.homEquiv (M := H) (N := ModuleCat.of R R)).bijective.comp
      (hq.comp (hH.comp hpre))
    convert hcomp using 1
    funext f
    simp [ψ, e, H, q, ModuleCat.homEquiv])
  let B : (𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)) ⟶ E) →ₗ[R]
      (E ⟶ 𝟙_ (DerivedCategory (ModuleCat.{u + 1} R))) →ₗ[R] R :=
    (Module.Dual.eval R H).compl₁₂ φ' ψ'
  refine ⟨B, ?_, ?_⟩
  · intro x f
    change ψ f (φ x) = identificationScalarValue (x ≫ f)
    simp [ψ, φ, identificationScalarValue, DerivedCategory.homSingleToHomology,
      e, Category.assoc, ModuleCat.homEquiv,
      DerivedCategory.singleFunctorCompHomologyFunctorIso,
      MonoidalCategoryStruct.tensorUnit]
    rfl
  · exact inferInstance

end WeilConjectures.SixFunctors
