/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.CategoryTheory.ModuleObjects.MapModIhom
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Signed powers of a native local line
Source: prop-weil-twist-preserves, step 1 (blueprint: lem-twist-native-signed-line).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}}
  (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

private theorem locallyTrivial_isLocallyFree
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hP : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
      Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj P ≅ 𝟙_ _)) :
    IsLocallyFree R P := by
  obtain ⟨𝒰, h𝒰⟩ := hP
  exact ⟨𝒰, fun i ↦ ⟨1, ⟨(h𝒰 i).some ≪≫
    (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular _)).symm⟩⟩⟩

private theorem locallyTrivial_invertible
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hP : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
      Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj P ≅ 𝟙_ _)) :
    IsInvertible P := by
  obtain ⟨𝒰, h𝒰⟩ := hP
  have (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  have := fun i ↦ isIso_ihomComparison_upperStar Ab.{u + 1} (𝒰.f i)
  have hi (i : 𝒰.I₀) : IsIso
      (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).map ((ihom.ev P).app (𝟙_ _))) := by
    let F := (upperStar Ab.{u + 1} (𝒰.f i)).mapMod R
    have h : IsInvertible (F.obj P) :=
      (isInvertible_iff_of_braided _).2
        ⟨𝟙_ _, ⟨whiskerRightIso (h𝒰 i).some _ ≪≫ λ_ _⟩⟩
    have := h.isIso_ev (F.obj (𝟙_ _))
    have hcomp := Functor.LaxMonoidal.ihomComparison_ev F P (𝟙_ _)
    have : IsIso (Functor.LaxMonoidal.μ F P ((ihom P).obj (𝟙_ _)) ≫
        F.map ((ihom.ev P).app (𝟙_ _))) := by
      rw [← hcomp]
      infer_instance
    exact IsIso.of_isIso_comp_left (Functor.LaxMonoidal.μ F P ((ihom P).obj (𝟙_ _))) _
  have : IsIso ((ihom.ev P).app (𝟙_ _)) := by
    suffices IsIso ((Mod.forget R).map ((ihom.ev P).app (𝟙_ _))) from
      isIso_of_reflects_iso _ (Mod.forget R)
    refine isIso_of_isIso_localizationRestriction Ab.{u + 1}
      ((ihom.ev P).app (𝟙_ _)).hom 𝒰.f 𝒰.mem₀ fun i ↦ ?_
    have : IsIso ((upperStar Ab.{u + 1} (𝒰.f i)).map
        ((ihom.ev P).app (𝟙_ _)).hom) :=
      inferInstanceAs (IsIso ((Mod.forget _).map
        (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).map ((ihom.ev P).app (𝟙_ _)))))
    exact (NatIso.isIso_map_iff
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) inferInstance) _).1 this
  exact (isInvertible_iff_of_braided P).2 ⟨_, ⟨asIso ((ihom.ev P).app (𝟙_ _))⟩⟩

/-- All signed powers of a local line are locally free and invertible, and opposite
powers cancel. Source: signed twist paragraph and prop-weil-twist-preserves, step 1
(blueprint: lem-twist-native-signed-line).
Proof: on the original covering, strong monoidal inverse image identifies positive
powers with the unit, by induction. Weakly etale inverse image commutes with internal
Hom, so it also identifies negative powers with the unit. This proves local freeness
and makes the canonical evaluation an isomorphism after each restriction. The
restrictions are jointly conservative, so evaluation is an isomorphism globally.
For a positive power, its negative is its internal dual, and evaluation cancels them.
The zero power cancels by the unitor. -/
theorem nativeSignedLine
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hL : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
      Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj L ≅ 𝟙_ _)) :
    (∀ m : ℤ, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
      Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj
        (coefficientSignedTwist X R L m) ≅ 𝟙_ _)) ∧
    (∀ m : ℤ, IsLocallyFree R (coefficientSignedTwist X R L m)) ∧
    (∀ m : ℤ, IsInvertible (coefficientSignedTwist X R L m)) ∧
    (∀ m : ℤ, Nonempty ((ihom (coefficientSignedTwist X R L m)).obj (𝟙_ _) ≅
      coefficientSignedTwist X R L (-m))) ∧
    ∀ m : ℤ, Nonempty (coefficientSignedTwist X R L m ⊗
      coefficientSignedTwist X R L (-m) ≅ 𝟙_ _) := by
  obtain ⟨𝒰, h𝒰⟩ := hL
  have (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  have := fun i ↦ isIso_ihomComparison_upperStar Ab.{u + 1} (𝒰.f i)
  have hn (n : ℕ) (i : 𝒰.I₀) : Nonempty
      (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj
        (coefficientTwistNat X R L n) ≅ 𝟙_ _) := by
    let F := (upperStar Ab.{u + 1} (𝒰.f i)).mapMod R
    induction n with
    | zero => exact ⟨(Functor.Monoidal.εIso F).symm⟩
    | succ n hn => exact ⟨(Functor.Monoidal.μIso F _ _).symm ≪≫
        tensorIso hn.some (h𝒰 i).some ≪≫ λ_ _⟩
  have hs (m : ℤ) : ∃ 𝒱 : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      ∀ i : 𝒱.I₀, Nonempty (((upperStar Ab.{u + 1} (𝒱.f i)).mapMod R).obj
        (coefficientSignedTwist X R L m) ≅ 𝟙_ _) := by
    refine ⟨𝒰, fun i ↦ ?_⟩
    let F := (upperStar Ab.{u + 1} (𝒰.f i)).mapMod R
    cases m with
    | ofNat n => exact hn n i
    | negSucc n =>
      exact ⟨asIso ((Functor.LaxMonoidal.ihomComparison F
          (coefficientTwistNat X R L (n + 1))).natTrans.app (𝟙_ _)) ≪≫
        asIso ((pre (hn (n + 1) i).some.inv).app _) ≪≫
        (ihom _).mapIso (Functor.Monoidal.εIso F).symm ≪≫ unitIsoSelf _⟩
  have hf (m : ℤ) := locallyTrivial_isLocallyFree R _ (hs m)
  have hv (m : ℤ) := locallyTrivial_invertible R _ (hs m)
  have hp (n : ℕ) : Nonempty (coefficientSignedTwist X R L (n : ℤ) ⊗
      coefficientSignedTwist X R L (-(n : ℤ)) ≅ 𝟙_ _) := by
    cases n with
    | zero => exact ⟨λ_ _⟩
    | succ n =>
      have ht : IsInvertible (coefficientTwistNat X R L (n + 1)) := by
        simpa only [coefficientSignedTwist] using hv (n + 1 : ℕ)
      have := ht.isIso_ev (𝟙_ _)
      exact ⟨asIso ((ihom.ev (coefficientTwistNat X R L (n + 1))).app (𝟙_ _))⟩
  refine ⟨hs, hf, hv, fun m ↦ ?_, fun m ↦ ?_⟩
  · cases m with
    | ofNat n =>
      cases n with
      | zero => exact ⟨unitIsoSelf _⟩
      | succ n => exact ⟨Iso.refl _⟩
    | negSucc n =>
      have ht : IsDualizable (coefficientTwistNat X R L (n + 1)) := by
        simpa only [coefficientSignedTwist] using (hv (n + 1 : ℕ)).isDualizable
      have := isIso_toIhomIhomUnit_of_isDualizable ht
      exact ⟨(asIso (toIhomIhomUnit (coefficientTwistNat X R L (n + 1)))).symm⟩
  · cases m with
    | ofNat n => exact hp n
    | negSucc n => exact ⟨β_ _ _ ≪≫ (hp (n + 1)).some⟩

end AlgebraicGeometry.ProEtale
