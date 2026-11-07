/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.Integral.Proper.IntegralProperConstructibleHeartBound
import WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartBoundRational
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralIndConstructibleHeartClosure
import all WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartCanonicalPresentation
import all WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleFilteredColimits
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleExtensions
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartFullFaithfulness
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
import all WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization.NormedCoefficientRealization
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels

set_option linter.privateModule false

/-!
# Uniform proper heart amplitude over a Noetherian base

The finite-amplitude part of the proper heart theorem, independently of coproduct
continuity. Source: Bhatt--Scholze, Section 6.8, and blueprint proper heart bound.
(blueprint: lem-sfb-noetherian-proper-heart-uniform-bound)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Sectionwise postcomposition, with the multiplication fixed as part of the ring object.
private noncomputable def continuousIso
    {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hei : Continuous e.symm) :
    Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} B) := by
  let eR : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := Profinite.continuousMapRingSheafMap e.toRingHom he
      inv := Profinite.continuousMapRingSheafMap e.symm.toRingHom hei
      hom_inv_id := by
        ext S f
        apply ULift.ext
        ext x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        ext x
        exact e.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  exact
    { hom := Mon.ofHom eAb.hom
      inv := Mon.ofHom eAb.inv
      hom_inv_id := Mon.Hom.ext eAb.hom_inv_id
      inv_hom_id := Mon.Hom.ext eAb.inv_hom_id }

-- A small-universe specialization of the normed coefficient realization construction.
private theorem field_model (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      ∃ σ : E ≃ₐ[ℚ_[ℓ]] F, Isometry σ := by
  let i : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsAlgClosed.lift
  let F := i.fieldRange
  let σ := i.equivFieldRange
  have : FiniteDimensional ℚ_[ℓ] F := σ.toLinearEquiv.finiteDimensional
  refine ⟨⟨F, inferInstance⟩, σ, ?_⟩
  exact NormedCoefficientRealization.embedding_isometry ℓ
    (fun x ↦ norm_algebraMap' E x) (fun x ↦ norm_algebraMap' F x) σ.toAlgHom

private theorem unitBall_realization (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (O : Subring E) (hO : ∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1) :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} O) ≅
        Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ F)) := by
  obtain ⟨F, σ, hiso⟩ := field_model ℓ E
  have hmem (x : E) : x ∈ O ↔ σ x ∈ PadicAlgCl.integers ℓ F := by
    rw [hO, PadicAlgCl.mem_integers_iff]
    change ‖x‖ ≤ 1 ↔ ‖σ x‖₊ ≤ 1
    rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm]
    rw [(AddMonoidHomClass.isometry_iff_norm σ).mp hiso x]
  let ei := σ.toRingEquiv.restrict O (PadicAlgCl.integers ℓ F) hmem
  have hi : Isometry ei := fun x y ↦ hiso x.val y.val
  have hii : Isometry ei.symm := fun x y ↦ by
    simpa only [ei.apply_symm_apply] using (hi (ei.symm x) (ei.symm y)).symm
  exact ⟨F, ⟨continuousIso ei hi.continuous hii.continuous⟩⟩

-- Minimality transports all closure operations at once along the exact equivalence.
private theorem coproductClosure_comap {Z : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S] (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R}
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstructibleModuleObject R) M) :
    ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstructibleModuleObject S) ((Mod.comap φ).obj M) := by
  let F : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) S := Mod.comap φ
  let Q := ObjectProperty.weakSerreCoproductClosure.{u + 1}
    (IsConstructibleModuleObject S)
  have : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  exact hM (Q.inverseImage F)
    (fun N hN ↦ ObjectProperty.le_weakSerreCoproductClosure _ _
      (_root_.constructible_comap φ hN))
    inferInstance inferInstance inferInstance inferInstance
    (fun _ ↦ inferInstance)

private theorem bound_transport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (h : ∃ d : ℤ, ∀ M, constructibleCoproductClosure Λ' Z M →
      (R((p)_*⟦Λ'⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d) :
    ∃ d : ℤ, ∀ M, constructibleCoproductClosure Λ Z M →
      (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun M hM ↦ ?_⟩
  let φ := coefficientMap e.inv.hom Z
  let ψ := coefficientMap e.inv.hom Y
  have : IsIso φ := by dsimp [φ, coefficientMap]; infer_instance
  have : IsIso ψ := by dsimp [ψ, coefficientMap]; infer_instance
  have hb : (R((p)_*⟦Λ'⟧).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((Mod.comap φ).obj M))).IsLE d :=
    hd ((Mod.comap φ).obj M) (coproductClosure_comap φ hM)
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  let es := ((Mod.comap φ).mapDerivedCategorySingleFunctor 0).app M
  have hflat (T : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv.hom T)) := by
    have : IsIso (coefficientMap e.inv.hom T) := by
      dsimp [coefficientMap]
      infer_instance
    exact preservesFiniteLimits_of_natIso
      (Mod.extendScalarsIsoComapInv (coefficientMap e.inv.hom T)).symm
  let ep := (derivedComapLowerStarIso e.inv.hom p).app K
  have ht : ((Mod.comap ψ).mapDerivedCategory.obj (R((p)_*⟦Λ⟧).obj K)).IsLE d := by
    rw [DerivedCategory.isLE_iff] at hb ⊢
    intro i hi
    exact (hb i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      (ep ≪≫ (R((p)_*⟦Λ'⟧)).mapIso es))
  exact (NormedCoefficientRealization.bounds_comap ψ _ d).1.mp ht

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference in the internal module category needs a larger search budget.

-- A finite bound for the geometric fibres of a proper morphism to a Noetherian scheme.
private theorem exists_geometricFibre_bound {Z Y : Scheme.{u}} [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p] :
    ∃ d : ℕ, ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := exists_fibre_dimension_bound p
  refine ⟨d, fun y ↦ ?_⟩
  have he := topologicalKrullDim_pullback_eq_of_field
    (k := Y.residueField y) (pullback.snd p (Y.fromSpecResidueField y))
    (Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))))
  have hi := IsHomeomorph.topologicalKrullDim_eq _
    (pullbackLeftPullbackSndIso p (Y.fromSpecResidueField y)
      (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y)
          (AlgebraicClosure (Y.residueField y)))))).hom.homeomorph.isHomeomorph
  exact (hi.symm.trans he).le.trans (hd y)

-- Filtered colimits of constructibles keep a uniform bound, by qcqs continuity.

-- The filtered-colimit closure of finite-field constructibles contains the Serre closure.

-- The filtered-colimit closure of integral constructibles contains the Serre closure.

end AlgebraicGeometry.ProEtale.CondensedRing
