/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCoefficientTateTwist
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateLocalLine
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.CategoryTheory.ModuleObjects.MapModIhom
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat

/-! # Invertibility of the native condensed Tate line
Source: the current blueprint dual-perfect proof, invertibility of the Tate line
(blueprint: lem-sf-native-shifted-tate-line-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed MonObj Limits
open scoped CategoryTheory.Obj
attribute [local instance] DerivedCategory.braidedCategory'
namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

private theorem nativeFirstLine_pullback_locally_trivial
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : Γ(X, ⊤)))
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (phi : Profinite.continuousMapRingObj ℤ_[ℓ] ⟶ Λ) [IsMonHom phi]
    {Y : Scheme.{u}} (f : Y ⟶ X) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i : 𝒰.I₀,
      Nonempty
        ((((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          ((upperStar Ab.{u + 1} f).obj
            (condensedRingObj Λ X))).obj
          (((upperStar Ab.{u + 1} f).mapMod
            (condensedRingObj Λ X)).obj
              (sfCondensedTateTwistOne X ℓ Λ phi))) ≅ 𝟙_ _) := by
  obtain ⟨𝒰, h𝒰⟩ := tateModule_pullback_locally_trivial X ℓ hℓ f
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨e⟩ := h𝒰 i
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X
  let S := condensedRingObj Λ X
  let a := coefficientMap phi X
  let F := upperStar Ab.{u + 1} f
  let G := upperStar Ab.{u + 1} (𝒰.f i)
  let E := Mod.extendScalars (G.map (F.map a))
  exact ⟨(G.mapMod (F.obj S)).mapIso ((pullExtendIso f a).symm.app (tateModule X ℓ)) ≪≫
    (pullExtendIso (𝒰.f i) (F.map a)).symm.app ((F.mapMod R).obj (tateModule X ℓ)) ≪≫
    E.mapIso e ≪≫ CategoryTheory.Mod.extendRegularIso (G.map (F.map a))⟩


end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}}
  (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]

/-- A module which is locally the coefficient unit is tensor-invertible.
Source: Stacks Tag 0FFM; current blueprint dual-perfect proof.
Proof: evaluation is an isomorphism on the trivializing cover, because inverse image
preserves the closed structure. The cover detects isomorphisms, so evaluation is an
isomorphism globally and exhibits the internal dual as tensor inverse.
(blueprint: lem-sf-native-shifted-tate-line-invertible). -/
private theorem nativeLocallyTrivialLineInvertible
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
    let : (upperStar Ab.{u + 1} (𝒰.f i)).Braided := {}
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


namespace CondensedRing

attribute [local irreducible] Mod.monoidalClosed

private theorem nonempty_pullback_ihom
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    Nonempty (((ProEtale.upperStar Ab.{u + 1} f).mapMod R).obj ((ihom M).obj N) ≅
      (ihom (((ProEtale.upperStar Ab.{u + 1} f).mapMod R).obj M)).obj
        (((ProEtale.upperStar Ab.{u + 1} f).mapMod R).obj N)) := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let : G.Braided := {}
  have : ∀ Z, IsIso (Functor.LaxMonoidal.ihomComparison G Z).natTrans :=
    ProEtale.isIso_ihomComparison_upperStar Ab.{u + 1} f
  exact ⟨asIso ((Functor.LaxMonoidal.ihomComparison (G.mapMod R) M).natTrans.app N)⟩

private theorem powers_image_regular
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (phi : Profinite.continuousMapRingObj ℤ_[ℓ] ⟶ Λ) [IsMonHom phi]
    {Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    {Z : Scheme.{u}} (g : Z ⟶ Y) [WeaklyEtale g]
    (e : (((ProEtale.upperStar Ab.{u + 1} g).mapMod
      ((ProEtale.upperStar Ab.{u + 1} f).obj
        (condensedRingObj Λ X))).obj
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj Λ X)).obj
          (sfCondensedTateTwistOne X ℓ Λ phi))) ≅ 𝟙_ _) (d : ℤ) :
    Nonempty ((((ProEtale.upperStar Ab.{u + 1} g).mapMod
      ((ProEtale.upperStar Ab.{u + 1} f).obj
        (condensedRingObj Λ X))).obj
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj Λ X)).obj
          (sfCondensedTateTwist X ℓ Λ phi d))) ≅ 𝟙_ _) := by
  let R := condensedRingObj Λ X
  let F := ProEtale.upperStar Ab.{u + 1} f
  let G := ProEtale.upperStar Ab.{u + 1} g
  let : F.Braided := {}
  let : G.Braided := {}
  let H := F.mapMod R ⋙ G.mapMod (F.obj R)
  have hn (n : ℕ) : Nonempty (H.obj (sfCondensedTateTwistNat X ℓ Λ phi n) ≅ 𝟙_ _) := by
    induction n with
    | zero => exact ⟨Functor.Monoidal.εIso H |>.symm⟩
    | succ n hn =>
      exact ⟨(Functor.Monoidal.μIso H _ _).symm ≪≫
        tensorIso hn.some e ≪≫ λ_ _⟩
  cases d with
  | ofNat n => exact hn n
  | negSucc n =>
    obtain ⟨hf⟩ := nonempty_pullback_ihom f R (sfCondensedTateTwistNat X ℓ Λ phi (n + 1)) (𝟙_ _)
    obtain ⟨hg⟩ := nonempty_pullback_ihom g (F.obj R)
      ((F.mapMod R).obj (sfCondensedTateTwistNat X ℓ Λ phi (n + 1))) ((F.mapMod R).obj (𝟙_ _))
    exact ⟨(G.mapMod (F.obj R)).mapIso hf ≪≫ hg ≪≫
      asIso ((pre (hn (n + 1)).some.inv).app _) ≪≫
      (ihom _).mapIso (Functor.Monoidal.εIso H).symm ≪≫
      MonoidalClosed.unitIsoSelf _⟩


/-- Signed native condensed Tate lines are invertible whenever ell is invertible on X.
Source: current blueprint, signed Tate powers and the dual-perfect proof.
Proof: take the compatible-root cover after identity pullback. Positive tensor powers
become the unit by induction; negative powers do too since weakly etale inverse image
preserves internal Hom. Evaluation is invertible on that cover. Identity inverse image
is conservative and closed monoidal, hence reflects invertibility.
(blueprint: lem-sf-native-shifted-tate-line-invertible). -/
private theorem nativeTateTwistInvertible (X : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (phi : Profinite.continuousMapRingObj ℤ_[ell] ⟶ Λ) [IsMonHom phi]
    (hell : IsUnit (ell : Γ(X, ⊤))) (d : ℤ) :
    IsInvertible (sfCondensedTateTwist X ell Λ phi d) := by
  classical
  let R := condensedRingObj Λ X
  let G := ProEtale.upperStar Ab.{u + 1} (𝟙 X)
  let F := G.mapMod R
  let : G.Braided := {}
  have : ∀ Z, IsIso (Functor.LaxMonoidal.ihomComparison G Z).natTrans :=
    ProEtale.isIso_ihomComparison_upperStar Ab.{u + 1} (𝟙 X)
  obtain ⟨U, hU⟩ := nativeFirstLine_pullback_locally_trivial X ell hell Λ phi (𝟙 X)
  have hF : IsInvertible (F.obj (sfCondensedTateTwist X ell Λ phi d)) := by
    apply nativeLocallyTrivialLineInvertible (G.obj R)
    refine ⟨U, fun i ↦ ?_⟩
    have : WeaklyEtale (U.f i) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ U.mem₀ ⟨i⟩
    exact powers_image_regular X ell Λ phi (𝟙 X) (U.f i) (hU i).some d
  apply isInvertible_of_isIso_ihomComparison F (h := hF)
  intro Y Z f hf
  have : IsIso (F.map f) := hf
  suffices IsIso ((Mod.forget R).map f) from isIso_of_reflects_iso f (Mod.forget R)
  have h : IsIso (G.map f.hom) :=
    inferInstanceAs (IsIso ((Mod.forget (G.obj R)).map (F.map f)))
  exact (NatIso.isIso_map_iff (ProEtale.upperStarId Ab.{u + 1} X) f.hom).mp h

/-- Invertibility passes from a flat module to its degree-zero derived object.
Source: the derived tensor formula for flat modules; Stacks Tag 0FFM.
Proof: tensor the module and its internal dual in degree zero. Flatness computes this
derived tensor as the degree-zero ordinary tensor. Evaluation identifies it with the
unit; symmetry gives the other inverse.
(blueprint: lem-sf-native-shifted-tate-line-invertible). -/
private theorem nativeSingleInvertible
    (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hP : IsInvertible P) :
    IsInvertible ((DerivedCategory.singleFunctor _ 0).obj P) := by
  let M := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R
  obtain ⟨Q, ⟨e⟩⟩ := (isInvertible_iff_of_braided P).1 hP
  have hflat := hP.isDualizable.flat
  apply (isInvertible_iff_of_braided _).2
  refine ⟨(DerivedCategory.singleFunctor M 0).obj Q, ⟨?_⟩⟩
  exact tensorIso ((DerivedCategory.singleFunctorIsoCompQ M 0).app P)
      ((DerivedCategory.singleFunctorIsoCompQ M 0).app Q) ≪≫
    DerivedCategory.QObjTensorQObjIsoOfKFlatLeft _ _
      ((CochainComplex.kFlat_single_obj_iff_flat P 0).2 hflat) ≪≫
    DerivedCategory.Q.mapIso
      ((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor M) P).app _ ≪≫
        (HomologicalComplex.singleMapHomologicalComplex (tensorLeft P) (.up ℤ) 0).app Q) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ M 0).app (P ⊗ Q)).symm ≪≫
    (DerivedCategory.singleFunctor M 0).mapIso e ≪≫
    DerivedCategory.singleFunctorObjUnitIso M

/-- The actual shifted native Tate line is invertible.
Source: current blueprint dual-perfect proof.
Proof: the native module Tate line is invertible by the compatible-root cover. Its
flat degree-zero image is invertible. Shift an inverse by the opposite integer and
use the derived tensor-shift comparison; their tensor is the unshifted unit.
(blueprint: lem-sf-native-shifted-tate-line-invertible). -/
theorem nativeShiftedCoefficientTateTwistInvertible (X : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (phi : Profinite.continuousMapRingObj ℤ_[ell] ⟶ Λ) [IsMonHom phi]
    (hell : IsUnit (ell : Γ(X, ⊤))) (d n : ℤ) :
    IsInvertible ((sfCondensedTateTwistDerived X ell Λ phi d) ⟦n⟧) := by
  have h := nativeSingleInvertible X _ _ (nativeTateTwistInvertible X ell Λ phi hell d)
  obtain ⟨Q, ⟨e⟩⟩ := (isInvertible_iff_of_braided (sfCondensedTateTwistDerived X ell Λ phi d)).1 h
  apply (isInvertible_iff_of_braided _).2
  refine ⟨Q⟦-n⟧, ⟨?_⟩⟩
  exact DerivedCategory.shiftTensorShiftIso (X := sfCondensedTateTwistDerived X ell Λ phi d)
      (Y := Q) (a := n) (b := -n) ≪≫
    (shiftFunctor _ _).mapIso e ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫
    (shiftFunctorZero _ ℤ).app _

/-- The Qbar specialization uses the upstream native Tate line.
Source: the current blueprint dual-perfect proof.
Proof: specialize the coefficient-ring theorem to the native inclusion Z_l to Qbar_l;
the signed powers agree with the upstream construction by induction.
(blueprint: lem-sf-native-shifted-tate-line-invertible). -/
theorem nativeShiftedTateTwistInvertible (X : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : IsUnit (ell : Γ(X, ⊤))) (d n : ℤ) :
    IsInvertible ((tateTwistDerived X ell d) ⟦n⟧) := by
  simpa only [sfCondensedTateTwistDerived, sfCondensedTateTwist_qbar, tateTwistDerived] using
    nativeShiftedCoefficientTateTwistInvertible X ell (Profinite.padicAlgClRingObj ell)
      (Profinite.padicIntRingObjToPadicAlgCl ell) hell d n

end CondensedRing
end AlgebraicGeometry.ProEtale
