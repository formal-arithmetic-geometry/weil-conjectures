/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperOpenComplementSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Field.ULift

/-! # Boundary vanishing of proper direct image of open extension by zero

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-comp-composition,
det-sf-comp-composition-interchange.proof.md, proof (3), closed-complement calculation
(blueprint: lem-sfb-proper-open-boundary-zero).

All functors act on ordinary unbounded derived categories of internal modules. The
input belongs to the bounded constructible finite-Tor full subcategory. The conclusion
is vanishing of the target object in the ambient derived category on the boundary.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The finite discrete ell-primary rings, ell-adic integers, finite ell-adic fields,
their integer rings, and the finite-subextension condensed algebraic closure, up to
isomorphism of ring objects. The separate rational and integral ground-field clauses
include Q_ell and Z_ell explicitly.

Source: blueprint main-20261015, sk-def-localizing-closure, coefficient list, with the
algebraic-closure convention of sk-def-sfb-qlbar-condensed. This item-owned specialization
is not the dependency's interface: it omits the all-continuous-map algebraic-closure case
of `IsLocalizingAdmissibleCoefficient`, as the item statement requires
(blueprint: lem-sfb-proper-open-boundary-zero). -/
def IsFiniteSubextensionLocalizingAdmissibleCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] : Prop :=
  (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option Elab.async false

attribute [local irreducible] upperStarFromPoint upperStar
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedComapUpperStarIso derivedComapLowerStarIso

private def BoundaryVanishing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {W Ybar Z : Scheme.{u}} (r : W ⟶ Ybar) (c : Z ⟶ Ybar) : Prop :=
  ∀ K : ConstantModelConstructibleFiniteTor Λ W,
    boundedConstructible (condensedRingObj Λ W) K.obj →
    IsZero ((moduleObjectDerivedPullback Λ (pullback.fst r c)).obj K.obj) →
    IsZero ((moduleObjectDerivedPullback Λ c).obj
      ((moduleObjectDerivedPushforward Λ r).obj K.obj))

attribute [local irreducible] BoundaryVanishing

private local instance comap_iso_equivalence {Z : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] :
    (Mod.comap φ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) S ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R).IsEquivalence :=
  (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor

private theorem constructible_comap_iff {Z : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S] (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R) :
    IsConstructibleModuleObject S ((Mod.comap φ).obj M) ↔
      IsConstructibleModuleObject R M := by
  constructor
  · intro h
    exact constructible_of_iso ((Mod.comapEquivalenceOfIsIso φ).unitIso.app M).symm
      (constructible_comap _ h)
  · exact constructible_comap φ

private theorem bounded_comap_iff {Z : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S] (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R)) :
    boundedConstructible S ((Mod.comap φ).mapDerivedCategory.obj K) ↔
      boundedConstructible R K := by
  rw [mem_boundedConstructible_iff, mem_boundedConstructible_iff]
  apply and_congr
  · constructor
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, fun i hi ↦
        (Mod.comap φ).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
          (h i hi)⟩
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, fun i hi ↦
        (Mod.comap φ).isZero_homologyFunctor_mapDerivedCategory_obj (h i hi)⟩
  · apply forall_congr'
    intro n
    let e := ((Mod.comap φ).mapDerivedCategoryHomologyFunctorIso n).app K
    exact ⟨fun h ↦ (constructible_comap_iff φ _).1 (constructible_of_iso e.symm h),
      fun h ↦ constructible_of_iso e ((constructible_comap_iff φ _).2 h)⟩

private theorem boundaryVanishing_transport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ')
    {W Ybar Z : Scheme.{u}} (r : W ⟶ Ybar) (c : Z ⟶ Ybar)
    (h : BoundaryVanishing Λ' r c) : BoundaryVanishing Λ r c := by
  unfold BoundaryVanishing at h ⊢
  intro K hK hz
  let φ := e.inv.hom
  let T (X : Scheme.{u}) :=
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap φ X)).mapDerivedCategory
  have (X : Scheme.{u}) : (T X).IsEquivalence := inferInstance
  have (X : Scheme.{u}) : PreservesFiniteLimits
      (Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (coefficientMap φ X)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  let pull {X Y : Scheme.{u}} (f : X ⟶ Y) :
      moduleObjectDerivedPullback Λ f ⋙ T X ≅ T Y ⋙ moduleObjectDerivedPullback Λ' f :=
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ f) (T X) ≪≫
      derivedComapUpperStarIso φ f ≪≫
      Functor.isoWhiskerLeft (T Y) (leftDerivedUpperStarIsoMapDerivedCategory Λ' f).symm
  let K' : ConstantModelConstructibleFiniteTor Λ' W :=
    ⟨(T W).obj K.obj, constantModelCtf_coefficientIso e W K⟩
  have hb : boundedConstructible (condensedRingObj Λ' W) K'.obj :=
    (bounded_comap_iff (coefficientMap φ W) K.obj).mpr hK
  have hz' : IsZero
      ((moduleObjectDerivedPullback Λ' (pullback.fst r c)).obj K'.obj) :=
    ((T (pullback r c)).map_isZero hz).of_iso ((pull (pullback.fst r c)).app K.obj).symm
  have hv := h K' hb hz'
  let push : moduleObjectDerivedPushforward Λ r ⋙ T Ybar ≅
      T W ⋙ moduleObjectDerivedPushforward Λ' r := derivedComapLowerStarIso φ r
  have hout : IsZero ((T Z).obj ((moduleObjectDerivedPullback Λ c).obj
      ((moduleObjectDerivedPushforward Λ r).obj K.obj))) := by
    apply hv.of_iso
    let e₁ := (pull c).app ((moduleObjectDerivedPushforward Λ r).obj K.obj)
    let e₂ := (moduleObjectDerivedPullback Λ' c).mapIso (push.app K.obj)
    exact e₁ ≪≫ e₂
  exact IsZero.of_full_of_faithful_of_isZero (T Z) _ hout

private theorem boundaryVanishing_rational
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {W Ybar Z : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Ybar.hom] [QuasiCompact Ybar.hom] [IsSeparated Ybar.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (r : W ⟶ Ybar) [IsProper r.left] (c : Z ⟶ Ybar) [IsClosedImmersion c.left]
    (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj R.X]
    (hR : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      R = Mon.mk (Profinite.continuousMapRingObj E)) ∨
        R = Mon.mk (Profinite.padicAlgClRingObj ℓ)) :
    BoundaryVanishing R.X r.left c.left := by
  unfold BoundaryVanishing
  intro K hK hz
  let T : Over (Spec (.of k)) := Over.mk (pullback.fst r.left c.left ≫ W.hom)
  let a : T ⟶ W := Over.homMk (pullback.fst r.left c.left) rfl
  let b : T ⟶ Z := Over.homMk (pullback.snd r.left c.left)
    (by
      change _ = pullback.fst r.left c.left ≫ W.hom
      rw [← Over.w r, ← Over.w c, pullback.condition_assoc])
  have : LocallyOfFiniteType T.hom := by
    dsimp [T]
    infer_instance
  have : QuasiCompact T.hom := by
    dsimp [T]
    infer_instance
  have : IsSeparated T.hom := by
    dsimp [T]
    infer_instance
  have sq : IsPullback a b r c := by
    apply IsPullback.of_map (Over.forget (Spec (.of k)))
      (by ext; exact pullback.condition)
    exact IsPullback.of_hasPullback r.left c.left
  rcases hR with ⟨E, hE⟩ | hQ
  · subst R
    let := isIso_boundedConstructibleBaseChange_of_isProper ℓ E sq
    let β := (ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
      sq.toCommSq).app ⟨K.obj, hK⟩
    have : IsIso β := inferInstance
    exact ((lowerStar (Profinite.continuousMapRingObj E) b.left).isZero_rightDerivedFunctor_obj
      hz).of_iso ((ObjectProperty.ι _).mapIso (asIso β))
  · subst R
    let := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sq
    let β := (boundedConstructibleBaseChange ℓ
      sq.toCommSq).app ⟨K.obj, hK⟩
    have : IsIso β := inferInstance
    exact ((lowerStar (Profinite.padicAlgClRingObj ℓ) b.left).isZero_rightDerivedFunctor_obj
      hz).of_iso ((ObjectProperty.ι _).mapIso (asIso β))

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

private theorem norm_spectral (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (hE : ∀ x : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] E x‖ = ‖x‖) (x : E) :
    ‖x‖ = spectralNorm ℚ_[ℓ] E x :=
  spectralNorm_unique_field_norm_ext (f := NormedField.toAbsoluteValue E) hE x

private theorem embedding_isometry (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : Type u} [NormedField E] [NormedField F]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] [Algebra ℚ_[ℓ] F]
    (hE : ∀ x : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] E x‖ = ‖x‖)
    (hF : ∀ x : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] F x‖ = ‖x‖) (σ : E →ₐ[ℚ_[ℓ]] F) :
    Isometry σ := by
  let v : AbsoluteValue E ℝ :=
    { toFun := fun x ↦ ‖σ x‖
      map_mul' := fun x y ↦ by simp only [map_mul, norm_mul]
      nonneg' := fun x ↦ norm_nonneg _
      eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero]
      add_le' := fun x y ↦ by simpa only [map_add] using norm_add_le (σ x) (σ y) }
  have hv (x : E) : ‖σ x‖ = ‖x‖ := by
    exact (spectralNorm_unique_field_norm_ext (f := v)
      (fun a ↦ by change ‖σ (algebraMap ℚ_[ℓ] E a)‖ = ‖a‖; rw [σ.commutes]; exact hF a)
      x).trans (norm_spectral ℓ E hE x).symm
  exact AddMonoidHomClass.isometry_of_norm σ hv

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
  exact embedding_isometry ℓ
    (fun x ↦ norm_algebraMap' E x) (fun x ↦ norm_algebraMap' F x) σ.toAlgHom

private theorem field_realization (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} E) ≅
        Mon.mk (Profinite.continuousMapRingObj.{u} F)) := by
  obtain ⟨F, σ, hσ⟩ := field_model ℓ E
  have hσi : Isometry σ.symm := fun x y ↦ by
    simpa only [σ.apply_symm_apply] using (hσ (σ.symm x) (σ.symm y)).symm
  exact ⟨F, ⟨continuousIso σ.toRingEquiv hσ.continuous hσi.continuous⟩⟩

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

private theorem spectral_embedded_norm
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] (x : ULift.{u} E.val) :
    Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val) x =
      ‖(x.down : PadicAlgCl ℓ)‖ := by
  let f : ULift.{u} E.val →+* PadicAlgCl ℓ :=
    E.val.val.toRingHom.comp ULift.ringEquiv.toRingHom
  let a : AbsoluteValue (ULift.{u} E.val) ℝ :=
    { toFun := fun x ↦ ‖f x‖
      map_mul' := fun x y ↦ by rw [map_mul, norm_mul]
      nonneg' := fun x ↦ norm_nonneg _
      eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero_iff f f.injective]
      add_le' := fun x y ↦ by rw [map_add]; exact norm_add_le _ _ }
  have ha : ∀ y : ℚ_[ℓ], a (algebraMap ℚ_[ℓ] (ULift.{u} E.val) y) = ‖y‖ := by
    intro y
    change ‖algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) y‖ = ‖y‖
    exact PadicAlgCl.norm_extends ℓ y
  exact (spectralNorm_unique_field_norm_ext ha x).symm
open CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
private theorem mem_lift_integers
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] (x : ULift.{u} E.val) :
    x ∈ Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val) ↔
      x.down ∈ PadicAlgCl.integers ℓ E.val := by
  have h := (Padic.coefficientExtensionIntegers_dvr ℓ (ULift.{u} E.val)).choose_spec.1 x
  exact h.trans (by
    rw [spectral_embedded_norm ℓ E x, PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe]
    rfl)
private noncomputable def integerLiftEquiv
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] :
    PadicAlgCl.integers ℓ E.val ≃+*
      Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val) where
  toFun x := ⟨ULift.up x.val, (mem_lift_integers ℓ E _).2 x.property⟩
  invFun x := ⟨x.val.down, (mem_lift_integers ℓ E _).1 x.property⟩
  left_inv _x := rfl
  right_inv _x := rfl
  map_mul' _x _y := rfl
  map_add' _x _y := rfl
private noncomputable def integerLiftHomeo
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
    letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)).toNormedField
    letI : TopologicalSpace (ULift.{u} E.val) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    PadicAlgCl.integers ℓ E.val ≃ₜ
      Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val) := by
  letI src := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
  letI tgt := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)).toNormedField
  letI : TopologicalSpace (ULift.{u} E.val) :=
    tgt.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let e := integerLiftEquiv ℓ E
  let sm : MetricSpace (PadicAlgCl.integers ℓ E.val) :=
    @Subtype.metricSpace E.val _ src.toMetricSpace
  let tm : MetricSpace (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val)) :=
    @Subtype.metricSpace (ULift.{u} E.val) _ tgt.toMetricSpace
  letI : PseudoEMetricSpace (PadicAlgCl.integers ℓ E.val) :=
    sm.toPseudoMetricSpace.toPseudoEMetricSpace
  letI : PseudoEMetricSpace
      (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val)) :=
    tm.toPseudoMetricSpace.toPseudoEMetricSpace
  have hi : @Isometry _ _ sm.toPseudoMetricSpace.toPseudoEMetricSpace
      tm.toPseudoMetricSpace.toPseudoEMetricSpace e := by
    apply @Isometry.of_dist_eq _ _ sm.toPseudoMetricSpace tm.toPseudoMetricSpace
    intro x y
    change Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)
      (-ULift.up x.val + ULift.up y.val) = dist
        (algebraMap E.val (PadicAlgCl ℓ) x.val)
        (algebraMap E.val (PadicAlgCl ℓ) y.val)
    rw [spectral_embedded_norm ℓ E]
    change ‖-(x.val : PadicAlgCl ℓ) + (y.val : PadicAlgCl ℓ)‖ =
      dist (x.val : PadicAlgCl ℓ) (y.val : PadicAlgCl ℓ)
    exact (dist_eq_norm_neg_add _ _).symm
  exact { e.toEquiv with
    continuous_toFun := hi.continuous
    continuous_invFun := (hi.right_inv e.right_inv).continuous }

open CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
private noncomputable def continuousSheafIso
    {A : Type} {B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (hc : Continuous e) (hci : Continuous e.symm) :
    Profinite.continuousMapRingSheaf.{u} A ≅ Profinite.continuousCoefficientRingSheaf B := by
  let forward (S : Profinite.{u}ᵒᵖ) :
      ULift.{u + 1} C(S.unop, A) →+* ULift.{u + 1} C(S.unop, B) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.toRingHom.compLeftContinuous _ hc).comp ULift.ringEquiv.toRingHom)
  let backward (S : Profinite.{u}ᵒᵖ) :
      ULift.{u + 1} C(S.unop, B) →+* ULift.{u + 1} C(S.unop, A) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.symm.toRingHom.compLeftContinuous _ hci).comp ULift.ringEquiv.toRingHom)
  refine
    { hom := ⟨{ app := fun S ↦ RingCat.ofHom (forward S)
                naturality := by intros; ext x; rfl }⟩
      inv := ⟨{ app := fun S ↦ RingCat.ofHom (backward S)
                naturality := by intros; ext x; rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext S x
    apply ULift.ext
    ext t
    exact e.symm_apply_apply _
  · ext S x
    apply ULift.ext
    ext t
    exact e.apply_symm_apply _

attribute [local irreducible] continuousSheafIso

private noncomputable def integerRingSheafIso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)] :
    Profinite.padicIntegersCondensedRing.{u} ℓ E.val ≅
      DerivedNakayama.integerRingSheaf ℓ (ULift.{u} E.val) := by
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
  letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)).toNormedField
  letI : Norm (ULift.{u} E.val) := nf.toNorm
  letI : MetricSpace (ULift.{u} E.val) := nf.toMetricSpace
  letI : TopologicalSpace (ULift.{u} E.val) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let e := integerLiftEquiv ℓ E
  have hc : Continuous (fun x ↦ e x) := by
    exact (integerLiftHomeo ℓ E).continuous_toFun
  have hci : Continuous (fun x ↦ e.symm x) := by
    exact (integerLiftHomeo ℓ E).continuous_invFun
  exact continuousSheafIso e hc hci

private noncomputable def integerIso (ℓ : ℕ) [Fact ℓ.Prime]
    (F : PadicAlgCl.FiniteIntermediateField ℓ) :
    Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ F) ≅
      Mon.mk (DerivedNakayama.integerRing ℓ (ULift.{u} F.val)) := by
  let eR := integerRingSheafIso.{u} ℓ ⟨F.val, F.property⟩
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom e.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  exact
    { hom := Mon.ofHom e.hom
      inv := Mon.ofHom e.inv
      hom_inv_id := Mon.Hom.ext e.hom_inv_id
      inv_hom_id := Mon.Hom.ext e.inv_hom_id }

private theorem finiteBoundaryCoefficientIso
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] :
    Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (finiteProperCoefficientRing (ULift.{u} A)).X) := by
  let : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
  obtain ⟨e, he⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} A
  let er : ULift.{u + 1} (ULift.{u} A) ≃+* ULift.{u + 1} A :=
    (ULift.ringEquiv.trans ULift.ringEquiv).trans ULift.ringEquiv.symm
  let P := (Functor.const Profinite.{u}ᵒᵖ).obj
    (RingCat.of (ULift.{u + 1} (ULift.{u} A)))
  let Q := (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))
  let i : P ≅ Q := NatIso.ofComponents (fun _ ↦ er.toRingCatIso) (by intros; rfl)
  let iAb := (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapIso
    (Functor.isoWhiskerRight i (forget₂ RingCat.{u + 1} Ab.{u + 1}))
  have : IsMonHom e.hom := he
  have : IsMonHom iAb.hom := by dsimp [iAb, i]; infer_instance
  exact ⟨(Mon.mkIso' e).symm ≪≫ (Mon.mkIso' iAb).symm⟩

/-- Keep the inverse isomorphism abstract while checking the concrete coefficient exchange. -/
private theorem isZero_source_of_isIso
    {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) (hf : IsIso f)
    (hY : IsZero Y) : IsZero X :=
  hY.of_iso (@asIso _ _ _ _ f hf)

private theorem boundaryVanishing_finite
    (A : Type u) [CommRing A] [Finite A]
    (ℓ : ℕ) [Fact ℓ.Prime] (hA : ∃ n : ℕ, (ℓ ^ n) • (1 : A) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {W Ybar : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Ybar.hom] [QuasiCompact Ybar.hom] [IsSeparated Ybar.hom]
    (r : W ⟶ Ybar) [IsProper r.left] (Z : Scheme.{u}) (c : Z ⟶ Ybar.left) :
    BoundaryVanishing (finiteProperCoefficientRing A).X r.left c := by
  unfold BoundaryVanishing
  intro K _ hz
  let sq : ChosenCartesianSquare (pullback.fst r.left c) (pullback.snd r.left c) r.left c :=
    { toCommSq := ⟨pullback.condition⟩
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  let β := (finiteProperAmbientExchange (finiteProperCoefficientRing A).X
    sq.toCommSq).app K.obj
  have hi : IsIso β := (finiteProperBaseChange A ℓ hA k W Ybar r).2.1
    _ Z c (pullback.snd r.left c) (pullback.fst r.left c) sq K
  have hzpush := (lowerStar (finiteProperCoefficientRing A).X
    (pullback.snd r.left c)).isZero_rightDerivedFunctor_obj hz
  exact isZero_source_of_isIso β hi hzpush

private theorem boundaryVanishing_integral
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {W Ybar : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Ybar.hom] [QuasiCompact Ybar.hom] [IsSeparated Ybar.hom]
    (r : W ⟶ Ybar) [IsProper r.left] (Z : Scheme.{u}) (c : Z ⟶ Ybar.left) :
    BoundaryVanishing (DerivedNakayama.integerRing ℓ E) r.left c := by
  unfold BoundaryVanishing
  intro K _ hz
  let : W.left.Over (Spec (.of k)) := ⟨W.hom⟩
  let : Ybar.left.Over (Spec (.of k)) := ⟨Ybar.hom⟩
  let : r.left.IsOver (Spec (.of k)) := ⟨r.w⟩
  have : LocallyOfFiniteType (W.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType W.hom›
  have : QuasiCompact (W.left ↘ Spec (.of k)) := ‹QuasiCompact W.hom›
  have : IsSeparated (W.left ↘ Spec (.of k)) := ‹IsSeparated W.hom›
  have : LocallyOfFiniteType (Ybar.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Ybar.hom›
  have : QuasiCompact (Ybar.left ↘ Spec (.of k)) := ‹QuasiCompact Ybar.hom›
  have : IsSeparated (Ybar.left ↘ Spec (.of k)) := ‹IsSeparated Ybar.hom›
  let sq : ChosenCartesianSquare (pullback.fst r.left c) (pullback.snd r.left c) r.left c :=
    { toCommSq := ⟨pullback.condition⟩
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  have hi := (integralProperDirectImageAndFormulas ℓ E k r.left).2.2.1
    c (pullback.snd r.left c) (pullback.fst r.left c) sq K.obj K.property.1
  let β := (condensedAmbientExchange (DerivedNakayama.integerRing ℓ E) sq).app K.obj
  exact ((lowerStar (DerivedNakayama.integerRing ℓ E)
    (pullback.snd r.left c)).isZero_rightDerivedFunctor_obj hz).of_iso (asIso β)

/-- Proper direct image of extension by zero from the inverse image of an open has zero
restriction to the reduced closed complement.

Source: blueprint main-20261015, det-sf-comp-composition-interchange.proof.md, proof (3)
(blueprint: lem-sfb-proper-open-boundary-zero).

Proof plan (the six steps of this DAG node):
1. Form T = W times_{Ybar} Z, with closed projection a to W and proper projection r_Z
   to Z. Base change of open immersions and quasi-compact maps identifies the other
   open projection with j : U to W. The ranges of a and j are complementary. Closed
   immersions are proper, so Z and T stay separated and finite type over k. T need
   not be reduced. Use lem-weil-pbc-closed-immersion-base-change,
   lem-weil-pbc-open-immersion-base-change, lem-pc-quasi-compact-base-change,
   lem-weil-pbc-proper-fp-permanence and lem-sfb-finite-type-composition-base-change.
2. Mixed restriction vanishing in lem-sfb-condensed-support-derived-localization gives
   a^* j_! A = 0, with no reducedness requirement on T.
3. Exact termwise j_! commutes with cohomology by
   lem-weil-pbc-exact-functor-complex-cohomology. Extend the finite constant-model
   stratification by the zero model on the complement, using
   lem-sf-open-extension-zero-constant-model-constructible. These models are locally
   finitely presented by det-def-sfb-constructible-local-model, so both bounded
   constructibility conventions apply (sk-def-sfb-bounded-constructible and
   sk-def-sfb-constructible). The projection formula of
   lem-sfb-open-immersion-derived-tensor-projection and exact pullback from
   sk-prop-sfb-cartesian-coefficients preserve the Tor interval under j_!.
4. For finite ell-primary coefficients, det-thm-sfb-proper-base-change-finite, clause
   (2), identifies c^* Rr_* j_! A with R(r_Z)_* a^* j_! A.
5. For integer rings use det-thm-sfb-proper-base-change-integral, clause (3); for finite
   fields and the finite-subextension condensed algebraic closure use
   det-thm-sfb-proper-base-change-rational, clause (3). The ground field and its integer
   ring are the degree-one cases. This exhausts sk-def-localizing-closure.
6. Substitute step 2. The adjunction of sk-def-sfb-module-derived-pushpull makes the
   right derived pushforward preserve the terminal, hence zero, object. Thus the
   object on the boundary vanishes. No comparison map or localizing extension is asserted. -/
theorem proper_open_boundary_zero
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsFiniteSubextensionLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (W Ybar Y Z : Over (Spec (.of k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Ybar.hom] [QuasiCompact Ybar.hom] [IsSeparated Ybar.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (r : W ⟶ Ybar) [IsProper r.left]
    (i : Y ⟶ Ybar) [IsOpenImmersion i.left] [QuasiCompact i.left]
    (c : Z ⟶ Ybar) [IsClosedImmersion c.left] [IsReduced Z.left]
    (hc : Set.range c.left.base = (Set.range i.left.base)ᶜ)
    (A : ConstantModelConstructibleFiniteTor Λ (pullback r.left i.left)) :
    IsZero ((moduleObjectDerivedPullback Λ c.left).obj
      ((moduleObjectDerivedPushforward Λ r.left).obj
        ((openImmersionLowerShriek Λ (pullback.fst r.left i.left)).mapDerivedCategory.obj
          A.obj))) := by
  have hv : BoundaryVanishing Λ r.left c.left := by
    rcases hΛ with h | h | h | h | h | h
    · obtain ⟨B, _, _, _, _, hfin, ⟨n, hn⟩, ⟨e⟩⟩ := h
      let : Finite B := hfin
      have hB : ∃ n : ℕ, (ℓ ^ n) • (1 : ULift.{u} B) = 0 := by
        refine ⟨n, ?_⟩
        exact ULift.ext _ _ (hn 1)
      obtain ⟨eB⟩ := finiteBoundaryCoefficientIso.{u} B
      exact boundaryVanishing_transport (e ≪≫ eB) r.left c.left
        (boundaryVanishing_finite (ULift.{u} B) ℓ hB k r Z.left c.left)
    · obtain ⟨e⟩ := h
      obtain ⟨F, ⟨eF⟩⟩ := unitBall_realization.{u} ℓ ℚ_[ℓ]
        (PadicInt.subring ℓ) (fun _ ↦ Iff.rfl)
      exact boundaryVanishing_transport (e ≪≫ eF ≪≫ integerIso ℓ F) r.left c.left
        (boundaryVanishing_integral ℓ (ULift.{u} F.val) k r Z.left c.left)
    · obtain ⟨e⟩ := h
      obtain ⟨F, ⟨eF⟩⟩ := field_realization.{u} ℓ ℚ_[ℓ]
      exact boundaryVanishing_transport (e ≪≫ eF) r.left c.left
        (boundaryVanishing_rational ℓ k r c _ (Or.inl ⟨F, rfl⟩))
    · obtain ⟨F, ⟨e⟩⟩ := h
      exact boundaryVanishing_transport e r.left c.left
        (boundaryVanishing_rational ℓ k r c _ (Or.inl ⟨F, rfl⟩))
    · obtain ⟨F, ⟨e⟩⟩ := h
      exact boundaryVanishing_transport (e ≪≫ integerIso ℓ F) r.left c.left
        (boundaryVanishing_integral ℓ (ULift.{u} F.val) k r Z.left c.left)
    · obtain ⟨e⟩ := h
      exact boundaryVanishing_transport e r.left c.left
        (boundaryVanishing_rational ℓ k r c _ (Or.inr rfl))
  obtain ⟨hU, _, _, _, _, _, _, _, hz⟩ := proper_open_complement_square ℓ r i c hc
  let U : Over (Spec (.of k)) := Over.mk (pullback.fst r.left i.left ≫ W.hom)
  let j : U ⟶ W := Over.homMk (pullback.fst r.left i.left) rfl
  have : LocallyOfFiniteType U.hom := hU.2.1
  have : QuasiCompact U.hom := hU.2.2
  have : IsSeparated U.hom := hU.1
  obtain ⟨m, n, hcoh⟩ :=
    (DerivedCategory.exists_homologyConcentratedIn_iff_bounded A.obj).mpr A.property.1.1
  obtain ⟨a, b, htor⟩ := A.property.2
  have : IsOpenImmersion j.left := inferInstanceAs
    (IsOpenImmersion (pullback.fst r.left i.left))
  have he := openExtension_constructible_finiteTor ℓ k Λ j A m n a b hcoh htor
  let K : ConstantModelConstructibleFiniteTor Λ W.left := ⟨_, he.1⟩
  unfold BoundaryVanishing at hv
  exact hv K he.2.2.2 (hz (Mon.mk Λ) A.obj)

end AlgebraicGeometry.ProEtale.CondensedRing
