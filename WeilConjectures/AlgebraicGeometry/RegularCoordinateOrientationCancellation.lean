/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularCoordinatePurityMaps

/-! # Cancellation before evaluating the inverse base Tate line

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md, Step 4(iii), composition of smooth orientations and
exceptional comparisons
(blueprint: lem-pur-regular-coordinate-orientation-cancellation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Cancellation of the absolute base orientation before inverse-Tate evaluation.

Proof: use the normalized smooth-orientation composition law for the projection
followed by the structural map of B. Naturality of its tensor/counit construction
identifies the composite with purity for p at the base Tate line. Conjugate the
associativity and identity laws of the compact-support compositor to exceptional
inverse image, for the triple z,p,a_B. Since z followed by p is the identity, its
composite with the exceptional comparison b is the identity. Naturality of this
section unitor at the orientation of B cancels the two appearances of that
orientation. This yields precisely the displayed identity, without a choice of
basis or an inverse-Tate evaluation. Zero relative dimension uses the same unit
laws; an empty base is allowed throughout.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md, Step 4(iii), and the smooth-purity composition law
(blueprint: lem-pur-regular-coordinate-orientation-cancellation). -/
theorem regular_coordinate_orientation_cancellation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [PerfectField k]
    (ell n : ℕ) [Fact ell.Prime] (hn : 0 < n)
    (hA : ((ell ^ n : ℕ) : A) = 0) (h_ell : IsUnit (ell : k))
    (B : Scheme.{u}) [B.Over (Spec (.of k))]
    [IsSeparated (B ↘ Spec (.of k))]
    [LocallyOfFiniteType (B ↘ Spec (.of k))]
    [QuasiCompact (B ↘ Spec (.of k))]
    (m c : ℕ) [SmoothOfRelativeDimension m (B ↘ Spec (.of k))] :
    letI : NeZero (ringChar A) := ⟨CharP.ringChar_ne_zero_of_finite A⟩
    let N := ell ^ n
    let hN : 0 < N := pow_pos (Fact.out : ell.Prime).pos n
    let S := Spec (.of k)
    let a_B : B ⟶ S := B ↘ S
    let X := 𝔸(ULift.{u} (Fin c); B)
    let p : X ⟶ B := X ↘ B
    let z : B ⟶ X := AffineSpace.zeroSection (ULift.{u} (Fin c)) B
    let a_X : X ⟶ S := p ≫ a_B
    letI : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian a_B
    letI : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace a_B
    letI : IsNoetherian B := {}
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    letI : IsNoetherian X := {}
    letI : SmoothOfRelativeDimension c p := by
      have h := AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin c)) B
      rwa [Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    letI : SmoothOfRelativeDimension (m + c) a_X := by
      simpa only [Nat.add_comm] using
        (inferInstance : SmoothOfRelativeDimension (c + m) (p ≫ a_B))
    let hS : IsUnit (N : Γ(S, ⊤)) := by
      simpa only [N, map_pow, map_natCast, Nat.cast_pow] using
        (h_ell.pow n).map (Scheme.ΓSpecIso (.of k)).inv.hom
    let hB : IsUnit (N : Γ(B, ⊤)) := by
      simpa only [map_natCast] using hS.map a_B.appTop.hom
    let hX : IsUnit (N : Γ(X, ⊤)) := by
      simpa only [map_natCast] using hB.map p.appTop.hom
    letI : HasInvertibleExponent A S := ⟨N, hN, hA, hS⟩
    letI : HasInvertibleExponent A B := ⟨N, hN, hA, hB⟩
    letI : HasInvertibleExponent A X := ⟨N, hN, hA, hX⟩
    let γ_B := regularSmoothUnitPurityIso A N hN hA a_B m hS
    let γ_X := regularSmoothUnitPurityIso A N hN hA a_X (m + c) hS
    let P_B := γ_B.symm
    let P_X := γ_X.symm
    let hza : z ≫ a_X = a_B := by
      dsimp only [a_X]
      rw [← Category.assoc, AffineSpace.zeroSection_comp_over, Category.id_comp]
    let b : dualizingComplex A a_B ≅
        (rightDerivedUpperShriek A z).obj (dualizingComplex A a_X) :=
      (rightDerivedUpperShriekCongr A hza.symm).app (constantComplex A S) ≪≫
      (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition A z a_X).app
        (constantComplex A S)
    let v := regularPurityAtTateIso A N hN hA p c hB m
    let U := regularExceptionalSectionUnitor A p z
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin c)) B)
    P_B.inv ≫ b.hom ≫ (rightDerivedUpperShriek A z).map P_X.hom ≫
      (rightDerivedUpperShriek A z).map v.hom ≫
      U.hom.app (shiftedTateObject A B (m : ℤ)) = 𝟙 _ := by
  sorry

end AlgebraicGeometry.Etale
