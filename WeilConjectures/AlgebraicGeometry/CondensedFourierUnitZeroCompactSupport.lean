/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCompactSupportBaseChange
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierPullback
import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierProjectorFacts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
import Mathlib.Algebra.CharP.Algebra

/-! Zero restriction before applying the affine-line trace. -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp
  CondensedRing.lowerStarComp CondensedRing.upperStarLowerStarAdjunction

/-- The inclusion of the affine line as the zero fibre of the second projection.
Source: lem-fd-first-formula.proof.md, constant-sheaf Cartesian square.
(blueprint: lem-fd-unit-zero-compact-support) -/
def unitZeroFibreInclusion (S : Scheme.{u}) : AffineSpace PUnit S ⟶
    pullback (AffineSpace PUnit S ↘ S) (AffineSpace PUnit S ↘ S) :=
  pullback.lift (𝟙 _) ((AffineSpace PUnit S ↘ S) ≫ AffineSpace.zeroSection PUnit S)
    (by rw [Category.id_comp, Category.assoc, AffineSpace.zeroSection_over,
      Category.comp_id])

/-- The zero-fibre square is Cartesian: its first projection is the identity.
Source: lem-fd-first-formula.proof.md, constant-sheaf Cartesian square.
Proof: paste the defining product square with the square of the zero section, which
is a section of the affine-line projection, and cancel the identity square.
(blueprint: lem-fd-unit-zero-compact-support) -/
theorem unitZeroFibreSquare (S : Scheme.{u}) :
    IsPullback (unitZeroFibreInclusion S) (AffineSpace PUnit S ↘ S)
      (pullback.snd (AffineSpace PUnit S ↘ S) (AffineSpace PUnit S ↘ S))
      (AffineSpace.zeroSection PUnit S) := by
  have ht₁ : unitZeroFibreInclusion S ≫
      pullback.fst (AffineSpace PUnit S ↘ S) (AffineSpace PUnit S ↘ S) = 𝟙 _ :=
    pullback.lift_fst _ _ _
  have ht₂ : unitZeroFibreInclusion S ≫
      pullback.snd (AffineSpace PUnit S ↘ S) (AffineSpace PUnit S ↘ S) =
      (AffineSpace PUnit S ↘ S) ≫ AffineSpace.zeroSection PUnit S :=
    pullback.lift_snd _ _ _
  refine IsPullback.of_right ?_ ht₂ (IsPullback.of_hasPullback _ _)
  rw [ht₁, AffineSpace.zeroSection_over]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The compactification induced by restriction to the origin, using the affine line
itself as the Cartesian fibre.
Source: lem-fd-first-formula.proof.md, compact-support exchange along the origin.
(blueprint: lem-fd-unit-zero-compact-support) -/
def unitZeroInducedCompactification (S : Scheme.{u})
    (c : Compactification (pullback.snd
      (AffineSpace PUnit S ↘ S) (AffineSpace PUnit S ↘ S))) :
    Compactification (AffineSpace PUnit S ↘ S) :=
  c.ofIsPullback (unitZeroFibreSquare S)

set_option maxHeartbeats 400000 in
-- Fix the native derived structure before specializing to a concrete scheme.
private def unitZero_singleRegularUnitIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ X)) ≅
      @MonoidalCategory.tensorUnit
        (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))) _ Mod.derivedMonoidalCategory.toMonoidalCategoryStruct :=
  DerivedCategory.singleFunctorObjUnitIso _

set_option maxHeartbeats 400000 in
-- Apply the lisse-kernel criterion while the base scheme is still a variable.
private theorem unitZero_bounded_single_AS
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (K : Type u) [Field K] [Fintype K]
    (hunit : IsUnit (Fintype.card K : MonObj.Γ Λ))
    (hadm : CondensedRing.IsAdmissibleCoefficient Λ)
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    (χ : AddChar K (MonObj.Γ Λ)) (b : Γ(X, ⊤)) :
    boundedConstructible (condensedRingObj Λ X)
      ((DerivedCategory.singleFunctor _ 0).obj
        (condensedArtinSchreierSheafOf Λ K X χ b)) := by
  have hLF : IsLocallyFree (condensedRingObj Λ X)
      (condensedArtinSchreierSheafOf Λ K X χ b) :=
    (AlgebraicGeometry.ProEtale.isLocallyFree_iff _).2
      ((Etale.prop_kernel_lisse.2.2.2 Λ K hunit hadm X χ χ b).1)
  exact CondensedRing.boundedConstructible_singleFunctor_obj Λ X 0 _
    hLF.isConstructibleModuleObject


set_option maxHeartbeats 400000 in
-- Keep the unit comparison generic before specializing the factorization.
private theorem unitZero_pullback_regular_of_factor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S A X : Scheme.{u}}
    (π : X ⟶ S) (z : S ⟶ A) (g : X ⟶ A) (h : g = π ≫ z)
    (M : Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A))
    (e : (CondensedRing.upperStar Λ z).obj M ≅ Mod.regular (condensedRingObj Λ S)) :
    Nonempty ((CondensedRing.upperStar Λ g).obj M ≅
      Mod.regular (condensedRingObj Λ X)) := by
  exact ⟨(CondensedRing.upperStarCongr Λ h).app M ≪≫
    (CondensedRing.upperStarComp Λ π z).app M ≪≫
      (CondensedRing.upperStar Λ π).mapIso e ≪≫
        (Functor.Monoidal.εIso (CondensedRing.upperStar Λ π)).symm⟩

set_option maxHeartbeats 400000 in
-- Package the evaluation before specializing the root map.
private theorem unitZero_cover_trivialization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (K : Type u) [Field K] [Fintype K]
    (χ : AddChar K (MonObj.Γ Λ)) (hunit : IsUnit (Fintype.card K : MonObj.Γ Λ)) :
    Nonempty ((CondensedRing.upperStar Λ
      (AffineSpace.artinSchreierMap PUnit (Spec (.of K)) (Fintype.card K))).obj
        (condensedArtinSchreierSheaf Λ K χ) ≅
      Mod.regular (condensedRingObj Λ (AffineSpace PUnit (Spec (.of K))))) := by
  let := hunit.invertible
  have := condensedArtinSchreierProjector_evaluation Λ K χ
  exact ⟨asIso ((CondensedRing.upperStar Λ
    (AffineSpace.artinSchreierMap PUnit (Spec (.of K)) (Fintype.card K))).map
      (image.ι (condensedArtinSchreierProjector Λ K χ)) ≫
    (CondensedRing.upperStarLowerStarAdjunction Λ
      (AffineSpace.artinSchreierMap PUnit (Spec (.of K)) (Fintype.card K))).counit.app
        (Mod.regular (condensedRingObj Λ (AffineSpace PUnit (Spec (.of K))))))⟩

set_option maxHeartbeats 400000 in
-- The root map is handled through the generic unit comparison.
private theorem unitZero_origin_trivialization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (K : Type u) [Field K] [Fintype K]
    (χ : AddChar K (MonObj.Γ Λ)) (hunit : IsUnit (Fintype.card K : MonObj.Γ Λ)) :
    Nonempty ((CondensedRing.upperStar Λ
      (AffineSpace.zeroSection PUnit (Spec (.of K)))).obj
        (condensedArtinSchreierSheaf Λ K χ) ≅
      Mod.regular (condensedRingObj Λ (Spec (.of K)))) := by
  obtain ⟨ec⟩ := unitZero_cover_trivialization Λ K χ hunit
  let z := AffineSpace.zeroSection PUnit (Spec (.of K))
  exact unitZero_pullback_regular_of_factor Λ z
    (AffineSpace.artinSchreierMap PUnit (Spec (.of K)) (Fintype.card K)) z
    (Etale.zeroSection_comp_artinSchreierMap (k := K)).symm
    (condensedArtinSchreierSheaf Λ K χ) ec

set_option maxHeartbeats 400000 in
-- Keep the origin isomorphism abstract while transporting to an arbitrary base.
private theorem unitZero_zero_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (K : Type u) [Field K] [Fintype K]
    (χ : AddChar K (MonObj.Γ Λ))
    (ez : (CondensedRing.upperStar Λ
      (AffineSpace.zeroSection PUnit (Spec (.of K)))).obj
        (condensedArtinSchreierSheaf Λ K χ) ≅
      Mod.regular (condensedRingObj Λ (Spec (.of K))))
    (X : Scheme.{u}) [X.Over (Spec (.of K))] :
    Nonempty (condensedArtinSchreierSheafOf Λ K X χ 0 ≅
      Mod.regular (condensedRingObj Λ X)) := by
  let π := X ↘ Spec (.of K)
  have hz : AffineSpace.homOfVector π (fun _ : PUnit ↦ (0 : Γ(X, ⊤))) =
      π ≫ AffineSpace.zeroSection PUnit (Spec (.of K)) := by
    rw [AffineSpace.zeroSection, AffineSpace.comp_homOfVector, Category.comp_id]
    congr 1
    ext
    simp
  exact unitZero_pullback_regular_of_factor Λ π
    (AffineSpace.zeroSection PUnit (Spec (.of K)))
    (AffineSpace.homOfVector π (fun _ : PUnit ↦ (0 : Γ(X, ⊤)))) hz
    (condensedArtinSchreierSheaf Λ K χ) ez

private theorem unitZero_zeroSheaf
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (K : Type u) [Field K] [Fintype K]
    (χ : AddChar K (MonObj.Γ Λ)) (hunit : IsUnit (Fintype.card K : MonObj.Γ Λ))
    (X : Scheme.{u}) [X.Over (Spec (.of K))] :
    Nonempty (condensedArtinSchreierSheafOf Λ K X χ 0 ≅
      Mod.regular (condensedRingObj Λ X)) := by
  obtain ⟨ez⟩ := unitZero_origin_trivialization Λ K χ hunit
  exact unitZero_zero_transport Λ K χ ez X

set_option maxHeartbeats 1600000 in
-- Base-change and derived tensor comparisons elaborate large concrete module instances.
/-- Compact-support exchange at the origin before the affine-line trace.
Source: latest blueprint, lem-fd-first-formula.proof.md, constant-sheaf paragraph.
Proof: cancel the pulled-back regular tensor unit, apply compact-support base change
with the induced compactification, restrict the pairing to zero, and trivialize its
Artin–Schreier sheaf by evaluation at the root zero. Commute pullback with shift [1].
(blueprint: lem-fd-unit-zero-compact-support) -/
theorem first_formula_unit_zero_restriction
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (_hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ), ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (_hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k] (_hk : Finite k ∨ IsAlgClosed k)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :
  Nonempty ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).leftDerivedFunctor.obj
      ((condensedFieldFourierTransform (Profinite.continuousMapRingObj E.1) k₀ k
        ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1)
            (AffineSpace PUnit (Spec (.of k))))))) ≅
    (shiftFunctor _ (1 : ℤ)).obj
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.continuousMapRingObj E.1)
        (unitZeroInducedCompactification (Spec (.of k)) c)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1)
              (AffineSpace PUnit (Spec (.of k)))))))) := by
  let Λ := Profinite.continuousMapRingObj.{u} E.1
  let : CharZero E := (algebraMap E (PadicAlgCl ℓ)).charZero
  let S : Scheme.{u} := Spec (.of k)
  let V : Scheme.{u} := AffineSpace PUnit S
  let π : V ⟶ S := V ↘ S
  let z : S ⟶ V := AffineSpace.zeroSection PUnit S
  let P : Scheme.{u} := pullback π π
  let p₁ : P ⟶ V := pullback.fst π π
  let p₂ : P ⟶ V := pullback.snd π π
  let : CharP k p := charP_of_injective_algebraMap (algebraMap k₀ k).injective p
  have hchar : ringChar k = p := ringChar.eq k p
  let : Fact (ringChar k).Prime := ⟨hchar.symm ▸ Fact.out⟩
  let : Fact (ringChar k ≠ ℓ) := ⟨by rw [hchar]; exact hpℓ⟩
  let : S.Over (Spec (.of k₀)) := ⟨Spec.map (CommRingCat.ofHom (algebraMap k₀ k))⟩
  let : V.Over (Spec (.of k₀)) := ⟨π ≫ (S ↘ Spec (.of k₀))⟩
  let : P.Over (Spec (.of k₀)) := ⟨p₁ ≫ π ≫ (S ↘ Spec (.of k₀))⟩
  let : MonoidalCategory (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1}) (condensedRingObj Λ P))) :=
    Mod.derivedMonoidalCategory
  let : MonoidalCategory (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))) :=
    Mod.derivedMonoidalCategory
  have hz : z ≫ π = 𝟙 S := AffineSpace.zeroSection_over PUnit S
  let t : V ⟶ P := unitZeroFibreInclusion S
  have ht₁ : t ≫ p₁ = 𝟙 V := pullback.lift_fst _ _ _
  have ht₂ : t ≫ p₂ = π ≫ z := pullback.lift_snd _ _ _
  have sq : IsPullback t π p₂ z := by
    refine IsPullback.of_right ?_ ht₂ (IsPullback.of_hasPullback π π)
    rw [ht₁, hz]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  let X : Over S := Over.mk (p₁ ≫ π)
  let Y : Over S := Over.mk π
  let X' : Over S := Over.mk π
  let Y' : Over S := Over.mk (𝟙 S)
  let f : X ⟶ Y := Over.homMk p₂ pullback.condition.symm
  let g : Y' ⟶ Y := Over.homMk z hz
  let f' : X' ⟶ Y' := Over.homMk π (Category.comp_id _)
  let g' : X' ⟶ X := Over.homMk t (by
    change t ≫ (p₁ ≫ π) = π
    rw [← Category.assoc, ht₁, Category.id_comp])
  have sq' : IsPullback g' f' f g :=
    IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext ht₂) sq
  have : LocallyOfFiniteType X.hom := inferInstanceAs (LocallyOfFiniteType (p₁ ≫ π))
  have : QuasiCompact X.hom := inferInstanceAs (QuasiCompact (p₁ ≫ π))
  have : IsSeparated X.hom := inferInstanceAs (IsSeparated (p₁ ≫ π))
  have : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType π)
  have : QuasiCompact Y.hom := inferInstanceAs (QuasiCompact π)
  have : IsSeparated Y.hom := inferInstanceAs (IsSeparated π)
  have : LocallyOfFiniteType X'.hom := inferInstanceAs (LocallyOfFiniteType π)
  have : QuasiCompact X'.hom := inferInstanceAs (QuasiCompact π)
  have : IsSeparated X'.hom := inferInstanceAs (IsSeparated π)
  have : LocallyOfFiniteType Y'.hom := inferInstanceAs (LocallyOfFiniteType (𝟙 S))
  have : QuasiCompact Y'.hom := inferInstanceAs (QuasiCompact (𝟙 S))
  have : IsSeparated Y'.hom := inferInstanceAs (IsSeparated (𝟙 S))
  let χ := (Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ
  let b := AffineSpace.stdPairing PUnit S
  let L := condensedFourierKernel Λ k₀ π π χ b
  let B := (DerivedCategory.singleFunctor _ 0).obj L
  have hunit : IsUnit (Fintype.card k₀ : MonObj.Γ Λ) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) :
        IsUnit (Fintype.card k₀ : E)).map (Profinite.continuousMapConstRingHom E)
  have hadm : CondensedRing.IsAdmissibleCoefficient Λ := by
    refine ⟨ℓ, inferInstance, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
    exact Or.inl ⟨E, ⟨Iso.refl _⟩⟩
  have hB : boundedConstructible (condensedRingObj Λ P) B :=
    unitZero_bounded_single_AS Λ k₀ hunit hadm P χ b
  obtain ⟨bc⟩ := CondensedRing.nonempty_iso_compactSupport_baseChange_of_coefficientIso
    ℓ E Λ (Or.inl ⟨Iso.refl _⟩) f g f' g' sq' c
    (unitZeroInducedCompactification S c) B hB
  have hb : t.appTop b = 0 := by
    dsimp [b]
    rw [AffineSpace.stdPairing, map_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have h : t.appTop (p₂.appTop (AffineSpace.coord S i)) = 0 := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ht₂,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.zeroSection_appTop_coord, map_zero]
    rw [map_mul, h, mul_zero]
  have : t.IsOver (Spec (.of k₀)) := ⟨by
    change t ≫ p₁ ≫ π ≫ (S ↘ Spec (.of k₀)) = π ≫ (S ↘ Spec (.of k₀))
    rw [← Category.assoc t p₁, ht₁, Category.id_comp]⟩
  obtain ⟨ek⟩ := nonempty_iso_condensedArtinSchreierSheafOf_derivedPullback Λ k₀ t χ b
  have e0 : condensedArtinSchreierSheafOf Λ k₀ V χ 0 ≅
      Mod.regular (condensedRingObj Λ V) := by
    exact (unitZero_zeroSheaf Λ k₀ χ hunit V).some
  let eK := ek ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso
    (eqToIso (congrArg (condensedArtinSchreierSheafOf Λ k₀ V χ) hb) ≪≫ e0) ≪≫
      unitZero_singleRegularUnitIso Λ V
  let H := CondensedRing.rightDerivedLowerShriekOfCompactification Λ c
  let H' := CondensedRing.rightDerivedLowerShriekOfCompactification Λ
    (unitZeroInducedCompactification S c)
  let F := (CondensedRing.upperStar Λ z).leftDerivedFunctor
  let U := (DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ V))
  let ein : (CondensedRing.upperStar Λ p₁).leftDerivedFunctor.obj U ⊗ B ≅ B :=
    tensorIso ((CondensedRing.upperStar Λ p₁).leftDerivedFunctor.mapIso
      (unitZero_singleRegularUnitIso Λ V) ≪≫
        CondensedRing.leftDerivedUpperStarUnitIso Λ p₁) (Iso.refl _) ≪≫ λ_ B
  let out := F.mapIso ((shiftFunctor _ (1 : ℤ)).mapIso (H.mapIso ein)) ≪≫
    (F.commShiftIso (1 : ℤ)).app (H.obj B) ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso (bc ≪≫ H'.mapIso eK)
  exact ⟨out ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso
    (H'.mapIso (unitZero_singleRegularUnitIso Λ V).symm)⟩

set_option maxHeartbeats 1600000 in
-- Match the concrete native derived endpoints when mapping the restriction isomorphism.
/-- The pushed zero-fibre comparison, before the affine-line trace.
Source: latest blueprint, lem-fd-first-formula.proof.md, constant-sheaf paragraph.
Proof: apply derived closed pushforward to the preceding zero-restriction isomorphism.
(blueprint: lem-fd-unit-zero-compact-support) -/
theorem first_formula_unit_zero_compact_support
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ), ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k] (_hk : Finite k ∨ IsAlgClosed k)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :
  Nonempty (((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor).obj
    ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).leftDerivedFunctor.obj
      ((condensedFieldFourierTransform (Profinite.continuousMapRingObj E.1) k₀ k
        ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1)
            (AffineSpace PUnit (Spec (.of k)))))))) ≅
    ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor).obj
      ((shiftFunctor _ (1 : ℤ)).obj
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.continuousMapRingObj E.1)
        (unitZeroInducedCompactification (Spec (.of k)) c)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1)
              (AffineSpace PUnit (Spec (.of k))))))))) := by
  obtain ⟨e⟩ := first_formula_unit_zero_restriction p ℓ hpℓ k₀ E hμ ψ hψ k _hk c
  exact ⟨((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor).mapIso e⟩

end AlgebraicGeometry.ProEtale
