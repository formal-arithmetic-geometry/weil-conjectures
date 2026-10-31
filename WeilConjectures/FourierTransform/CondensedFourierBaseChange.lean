/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FourierSetting
public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.FourierTransform.DualBundlePairing
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.FourierTransform.Properties.BaseChange

import WeilConjectures.FourierTransform.CondensedCoefficientIsoBoundedConstructible
import WeilConjectures.FourierTransform.CondensedCompactSupportBaseChange
import WeilConjectures.FourierTransform.CondensedArtinSchreierPullback
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj
import WeilConjectures.FourierTransform.DualBundlePairingFiniteType
import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-! # Base change of the condensed Fourier--Deligne transform

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/lem-fd-base-change.md
and its proof (blueprint: lem-fd-base-change).

Both sides lie in the ordinary unbounded derived category of modules over the pulled-back
condensed coefficient ring. Bounded constructibility is a hypothesis on the input only.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 0 in
-- Derived tensor and compact-support comparisons elaborate large instance terms.
/-- Fourier--Deligne transform commutes with base change of a vector bundle and its dual.
`E` is a small presentation of the fixed finite coefficient extension: `e` identifies it
with the extension of the Fourier setting. `hΛ` selects `E` or the algebraic closure as
condensed rings, allowing an isomorphic presentation. The character over `k₀` uses the
blueprint's degree-`q` Artin--Schreier model (equivalently the prime-field trace model).
The two pullback squares identify `W` and `Wdual` with the base-changed bundles; the
pairing on their product is the literal pullback of evaluation. Any compactifications
may be used on the two sides.

Source: latest blueprint, lem-fd-base-change.md, entire statement
(blueprint: lem-fd-base-change).

Proof.
1. Form the map of bundle products. Pasting and cancellation of the two given
   cartesian squares makes its square over the second projections cartesian.
   The dual frames make all bundle projections separated and of finite type.
2. Derived pullbacks compose and preserve tensor products. Exactness of condensed
   module pullback identifies the degree-zero kernel with the kernel of the
   pulled-back function. These comparisons identify the pulled-back integrand.
3. The original integrand is bounded constructible: pullback preserves bounded
   constructibility, and tensoring with the locally free character kernel does
   too. Transport the canonical E/Qlbar triangulatedness along the given ring
   isomorphism to justify this locally free tensor argument.
4. Compact-support base change applies to this integrand. Restriction along the
   coefficient isomorphism transports the canonical-coefficient theorem and
   compactification independence to the specified coefficient presentation.
   Combine this exchange with the integrand comparison and the pullback-shift
   isomorphism to obtain the claimed isomorphism. -/
theorem nonempty_iso_condensedFourierTransform_baseChange
    (F : WeilConjectures.FourierSetting.{u})
    (E : PadicAlgCl.FiniteIntermediateField F.coefficients.l)
    (e : F.extension ≃ₐ[Padic F.coefficients.l] E)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} F.coefficients.l)))
    {S S' V Vdual W Wdual : Over (Spec (.of F.field.k₀))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType S'.hom] [QuasiCompact S'.hom] [IsSeparated S'.hom]
    (g : S' ⟶ S) (π : V ⟶ S) (πdual : Vdual ⟶ S)
    (ρ : W ⟶ S') (ρdual : Wdual ⟶ S') (gV : W ⟶ V) (gdual : Wdual ⟶ Vdual)
    (sqV : IsPullback gV.left ρ.left π.left g.left)
    (sqDual : IsPullback gdual.left ρdual.left πdual.left g.left)
    (r : ℕ) (b : Γ(pullback π.left πdual.left, ⊤))
    (bundle : DualBundlePairing π.left πdual.left r b)
    (ψ : AddChar F.field.k₀ (MonObj.Γ Λ))
    (c : Compactification (pullback.snd π.left πdual.left))
    (c' : Compactification (pullback.snd ρ.left ρdual.left))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V.left) Ab.{u + 1})
      (condensedRingObj Λ V.left)))
    (hK : boundedConstructible (condensedRingObj Λ V.left) K) :
    letI : Fintype F.field.k₀ := Fintype.ofFinite F.field.k₀
    letI : (pullback π.left πdual.left).Over (Spec (.of F.field.k₀)) :=
      ⟨pullback.fst π.left πdual.left ≫ V.hom⟩
    letI : (pullback ρ.left ρdual.left).Over (Spec (.of F.field.k₀)) :=
      ⟨pullback.fst ρ.left ρdual.left ≫ W.hom⟩
    Nonempty (
      (condensedFourierTransform Λ F.field.k₀ ρ.left ρdual.left ψ
        (Etale.pairingBaseChange π.left πdual.left b g.left ρ.left ρdual.left
          gV.left gdual.left sqV.w sqDual.w) c' (r : ℤ)).obj
          ((moduleObjectDerivedPullback Λ gV.left).obj K) ≅
      (moduleObjectDerivedPullback Λ gdual.left).obj
        ((condensedFourierTransform Λ F.field.k₀ π.left πdual.left ψ b c (r : ℤ)).obj K)) := by
  let : Fintype F.field.k₀ := Fintype.ofFinite F.field.k₀
  let : (pullback π.left πdual.left).Over (Spec (.of F.field.k₀)) :=
    ⟨pullback.fst π.left πdual.left ≫ V.hom⟩
  let : (pullback ρ.left ρdual.left).Over (Spec (.of F.field.k₀)) :=
    ⟨pullback.fst ρ.left ρdual.left ≫ W.hom⟩
  let h : pullback ρ.left ρdual.left ⟶ pullback π.left πdual.left :=
    pullback.map ρ.left ρdual.left π.left πdual.left gV.left gdual.left g.left
      sqV.w.symm sqDual.w.symm
  have hfst : h ≫ pullback.fst π.left πdual.left =
      pullback.fst ρ.left ρdual.left ≫ gV.left := pullback.lift_fst _ _ _
  have hsnd : h ≫ pullback.snd π.left πdual.left =
      pullback.snd ρ.left ρdual.left ≫ gdual.left := pullback.lift_snd _ _ _
  have sqH : IsPullback h (pullback.snd ρ.left ρdual.left)
      (pullback.snd π.left πdual.left) gdual.left := by
    refine IsPullback.of_right ?_ hsnd (IsPullback.of_hasPullback π.left πdual.left)
    rw [hfst, sqDual.w]
    exact (IsPullback.of_hasPullback ρ.left ρdual.left).paste_horiz sqV
  have : h.IsOver (Spec (.of F.field.k₀)) := ⟨by
    change h ≫ pullback.fst π.left πdual.left ≫ V.hom =
      pullback.fst ρ.left ρdual.left ≫ W.hom
    rw [← Category.assoc, hfst, Category.assoc, Over.w gV]⟩
  let A := (upperStar Λ (pullback.fst π.left πdual.left)).leftDerivedFunctor.obj K
  let B := (DerivedCategory.singleFunctor _ 0).obj
    (condensedFourierKernel Λ F.field.k₀ π.left πdual.left ψ b)
  let M := A ⊗ B
  let A' := (upperStar Λ (pullback.fst ρ.left ρdual.left)).leftDerivedFunctor.obj
    ((upperStar Λ gV.left).leftDerivedFunctor.obj K)
  let B' := (DerivedCategory.singleFunctor _ 0).obj
    (condensedFourierKernel Λ F.field.k₀ ρ.left ρdual.left ψ (h.appTop b))
  let M' := A' ⊗ B'
  have eFirst : (upperStar Λ h).leftDerivedFunctor.obj A ≅ A' :=
    ((leftDerivedUpperStarComp Λ h (pullback.fst π.left πdual.left)).symm ≪≫
      eqToIso (congrArg (fun t ↦ (upperStar Λ t).leftDerivedFunctor) hfst) ≪≫
      leftDerivedUpperStarComp Λ (pullback.fst ρ.left ρdual.left) gV.left).app K
  obtain ⟨eKernel⟩ := nonempty_iso_condensedArtinSchreierSheafOf_derivedPullback
    Λ F.field.k₀ h ψ b
  have eIntegrand : (upperStar Λ h).leftDerivedFunctor.obj M ≅ M' :=
    ((leftDerivedUpperStarTensorIso Λ h).app A).app B ≪≫ tensorIso eFirst eKernel
  have eBC : Nonempty ((upperStar Λ gdual.left).leftDerivedFunctor.obj
        ((rightDerivedLowerShriekOfCompactification Λ c).obj M) ≅
      (rightDerivedLowerShriekOfCompactification Λ c').obj
        ((upperStar Λ h).leftDerivedFunctor.obj M)) := by
    obtain ⟨hπ, hπqc, hπsep, hπd, hπdqc, hπdsep⟩ := bundle.finiteType_separated
    have : LocallyOfFiniteType π.left := hπ
    have : QuasiCompact π.left := hπqc
    have : IsSeparated π.left := hπsep
    have : LocallyOfFiniteType πdual.left := hπd
    have : QuasiCompact πdual.left := hπdqc
    have : IsSeparated πdual.left := hπdsep
    have : LocallyOfFiniteType ρ.left :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sqV hπ
    have : QuasiCompact ρ.left :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) sqV hπqc
    have : IsSeparated ρ.left :=
      MorphismProperty.of_isPullback (P := @IsSeparated) sqV hπsep
    have : LocallyOfFiniteType ρdual.left :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sqDual hπd
    have : QuasiCompact ρdual.left :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) sqDual hπdqc
    have : IsSeparated ρdual.left :=
      MorphismProperty.of_isPullback (P := @IsSeparated) sqDual hπdsep
    have : LocallyOfFiniteType V.hom := by rw [← Over.w π]; infer_instance
    have : QuasiCompact V.hom := by rw [← Over.w π]; infer_instance
    have : IsSeparated V.hom := by rw [← Over.w π]; infer_instance
    have : LocallyOfFiniteType Vdual.hom := by rw [← Over.w πdual]; infer_instance
    have : QuasiCompact Vdual.hom := by rw [← Over.w πdual]; infer_instance
    have : IsSeparated Vdual.hom := by rw [← Over.w πdual]; infer_instance
    have : LocallyOfFiniteType W.hom := by rw [← Over.w ρ]; infer_instance
    have : QuasiCompact W.hom := by rw [← Over.w ρ]; infer_instance
    have : IsSeparated W.hom := by rw [← Over.w ρ]; infer_instance
    have : LocallyOfFiniteType Wdual.hom := by rw [← Over.w ρdual]; infer_instance
    have : QuasiCompact Wdual.hom := by rw [← Over.w ρdual]; infer_instance
    have : IsSeparated Wdual.hom := by rw [← Over.w ρdual]; infer_instance
    let P : Over (Spec (.of F.field.k₀)) :=
      Over.mk (pullback.fst π.left πdual.left ≫ V.hom)
    let P' : Over (Spec (.of F.field.k₀)) :=
      Over.mk (pullback.fst ρ.left ρdual.left ≫ W.hom)
    have : LocallyOfFiniteType P.hom := inferInstanceAs
      (LocallyOfFiniteType (pullback.fst π.left πdual.left ≫ V.hom))
    have : QuasiCompact P.hom := inferInstanceAs
      (QuasiCompact (pullback.fst π.left πdual.left ≫ V.hom))
    have : IsSeparated P.hom := inferInstanceAs
      (IsSeparated (pullback.fst π.left πdual.left ≫ V.hom))
    have : LocallyOfFiniteType P'.hom := inferInstanceAs
      (LocallyOfFiniteType (pullback.fst ρ.left ρdual.left ≫ W.hom))
    have : QuasiCompact P'.hom := inferInstanceAs
      (QuasiCompact (pullback.fst ρ.left ρdual.left ≫ W.hom))
    have : IsSeparated P'.hom := inferInstanceAs
      (IsSeparated (pullback.fst ρ.left ρdual.left ≫ W.hom))
    let p₂ : P ⟶ Vdual := Over.homMk (pullback.snd π.left πdual.left) (by
      dsimp [P]
      rw [← Over.w πdual, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w π])
    let p₂' : P' ⟶ Wdual := Over.homMk (pullback.snd ρ.left ρdual.left) (by
      dsimp [P']
      rw [← Over.w ρdual, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w ρ])
    let h' : P' ⟶ P := Over.homMk h (by
      dsimp [P, P']
      rw [← Category.assoc, hfst, Category.assoc, Over.w gV])
    have sqH' : IsPullback h' p₂' p₂ gdual :=
      IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext hsnd) sqH
    have : IsLocallyNoetherian P.left := LocallyOfFiniteType.isLocallyNoetherian P.hom
    have : CompactSpace P.left := QuasiCompact.compactSpace_of_compactSpace P.hom
    have : IsNoetherian P.left := ⟨⟩
    have htri_of_iso
        {R T : Sheaf (Scheme.ProEt.topology P.left) Ab.{u + 1}}
        [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
        (φ : T ⟶ R) [IsMonHom φ] [IsIso φ]
        [(boundedConstructible T).IsTriangulated] :
        (boundedConstructible R).IsTriangulated := by
      have heq : boundedConstructible R =
          (boundedConstructible T).inverseImage (Mod.comap φ).mapDerivedCategory := by
        ext L
        exact (boundedConstructible_comap_iso_iff φ L).symm
      rw [heq]
      infer_instance
    have : (boundedConstructible (condensedRingObj Λ P.left)).IsTriangulated := by
      rcases hΛ with hE | hQ
      · obtain ⟨i⟩ := hE
        have : IsIso i.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map i.inv))
        have : IsIso (coefficientMap i.inv.hom P.left) :=
          inferInstanceAs (IsIso ((upperStarFromPoint P.left).map i.inv.hom))
        let : (boundedConstructible (condensedRingObj
            (Profinite.continuousMapRingObj E) P.left)).IsTriangulated :=
          isTriangulated_boundedConstructible_continuousMapRingObj
            P.left F.coefficients.l E
        exact htri_of_iso (coefficientMap i.inv.hom P.left)
      · obtain ⟨i⟩ := hQ
        have : IsIso i.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map i.inv))
        have : IsIso (coefficientMap i.inv.hom P.left) :=
          inferInstanceAs (IsIso ((upperStarFromPoint P.left).map i.inv.hom))
        let : (boundedConstructible (condensedRingObj
            (Profinite.padicAlgClRingObj F.coefficients.l) P.left)).IsTriangulated :=
          isTriangulated_boundedConstructible_padicAlgClRingObj P.left F.coefficients.l
        exact htri_of_iso (coefficientMap i.inv.hom P.left)
    have hunit (n : ℕ) (hn : n ≠ 0) : IsUnit (n : MonObj.Γ Λ) := by
      rcases hΛ with hE | hQ
      · obtain ⟨i⟩ := hE
        let : CharZero F.extension := ⟨fun m n h ↦ Nat.cast_injective
          (by simpa only [map_natCast] using congrArg e h : (m : E) = (n : E))⟩
        let a := ((MonObj.Γ.map i.inv.hom).comp
          (Profinite.continuousMapConstRingHom E)).comp e.toRingHom
        simpa only [map_natCast] using
          (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn) :
            IsUnit (n : F.extension)).map a
      · obtain ⟨i⟩ := hQ
        let a := (MonObj.Γ.map i.inv.hom).comp
          (Profinite.PadicAlgCl.constRingHom F.coefficients.l)
        simpa only [map_natCast] using
          (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn) :
            IsUnit (n : PadicAlgCl F.coefficients.l)).map a
    have hadm : IsAdmissibleCoefficient Λ := by
      refine ⟨F.coefficients.l, inferInstance, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
      exact hΛ.imp (fun i ↦ ⟨E, i⟩) id
    have hLF : IsLocallyFree (condensedRingObj Λ P.left)
        (condensedFourierKernel Λ F.field.k₀ π.left πdual.left ψ b) :=
      (isLocallyFree_iff _).2
        ((Etale.prop_kernel_lisse.2.2.2 Λ F.field.k₀
          (hunit _ Fintype.card_ne_zero) hadm P.left ψ ψ b).1)
    have hA : boundedConstructible (condensedRingObj Λ P.left) A :=
      boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ _ K hK
    let : BraidedCategory (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (pullback π.left πdual.left)) Ab.{u + 1})
          (condensedRingObj Λ (pullback π.left πdual.left)))) :=
      DerivedCategory.braidedCategory' _
    have hM : boundedConstructible (condensedRingObj Λ P.left) M :=
      (boundedConstructible (condensedRingObj Λ P.left)).prop_of_iso (β_ B A)
        (boundedConstructible_singleFunctor_tensorObj_of_isLocallyFree hLF hA)
    have hp : ringChar F.field.k₀ = F.field.p := by
      let : Fact F.field.p.Prime := ⟨F.field.prime⟩
      let : CharP F.field.k₀ F.field.p := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using
          F.field.card_base.trans F.field.cardinality_eq)
      exact ringChar.eq F.field.k₀ F.field.p
    have : Fact (ringChar F.field.k₀).Prime := ⟨hp.symm ▸ F.field.prime⟩
    have : Fact (ringChar F.field.k₀ ≠ F.coefficients.l) :=
      ⟨by rw [hp]; exact Ne.symm F.coefficients.different⟩
    exact nonempty_iso_compactSupport_baseChange_of_coefficientIso F.coefficients.l E Λ hΛ
      p₂ gdual p₂' h' sqH' c c' M hM
  obtain ⟨eBC⟩ := eBC
  refine ⟨(shiftFunctor _ (r : ℤ)).mapIso
      (((rightDerivedLowerShriekOfCompactification Λ c').mapIso eIntegrand).symm ≪≫
        eBC.symm) ≪≫ ?_⟩
  exact ((upperStar Λ gdual.left).leftDerivedFunctor.commShiftIso (r : ℤ)).symm.app
    ((rightDerivedLowerShriekOfCompactification Λ c).obj M)

end AlgebraicGeometry.ProEtale.CondensedRing
