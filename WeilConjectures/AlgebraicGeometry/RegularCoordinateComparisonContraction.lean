/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularCoordinatePurityMaps
import WeilConjectures.AlgebraicGeometry.RegularCoordinateOrientationCancellation
import WeilConjectures.AlgebraicGeometry.RegularSectionTateEvaluation

/-! # Canonical contraction on the coordinate zero section

The canonical maps are defined in `RegularCoordinatePurityMaps`.
Source: current blueprint sk-thm-regular, Step 4(iii)
(blueprint: lem-pur-regular-coordinate-comparison-contraction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem cancel_tensor_pairing
    {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {U L X Y Z M : C} (q : X ≅ (T.obj L).obj Y)
    (e : U ≅ (T.obj X).obj M)
    (a : (T.obj ((T.obj L).obj Y)).obj M ≅ (T.obj L).obj Z)
    (D : (T.obj L).obj Y ⟶ X) (r : (T.obj L).obj Z ⟶ U)
    (hq : q.hom ≫ D = 𝟙 X)
    (hr : (T.map D).app M ≫ e.inv = a.hom ≫ r) :
    (e ≪≫ (T.mapIso q).app M ≪≫ a).hom ≫ r = 𝟙 U := by
  have ht : (T.map q.hom).app M ≫ (T.map D).app M = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← T.map_comp, hq, T.map_id, NatTrans.id_app]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [← hr, ← Category.assoc ((T.map q.hom).app M), ht]
  simp

/-- The canonical regular dualizing comparison contracts to smooth purity for the
coordinate projection, over an arbitrary perfect field with invertible ell.

Proof: apply `regular_coordinate_orientation_cancellation` before evaluating the
inverse base Tate line. After composing with inverse co-projection, this says
q followed by the base-line purity pairing D is the identity. Apply
`regular_section_tate_evaluation` to identify tensor(D,1) followed by inverse
Tate evaluation with reassociation followed by the unit purity pairing r.
Functoriality of tensor therefore gives qPrime followed by r equal to the
identity. Invert qPrime and cancel co-projection to get the displayed formula.
The natural section unitor has exactly the unit component used in this statement.
Zero dimensions and empty schemes need no separate argument.
The maps defining Phi_z are independent of the right side: in particular qPrime
is the dependency's actual inverse-m evaluation construction, and copr_c is its
canonical exceptional Tate co-projection, not a map defined from gamma_p or u.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md, Step 4(iii)
(blueprint: lem-pur-regular-coordinate-comparison-contraction). -/
theorem regular_coordinate_comparison_contraction
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
    let γ_p := regularSmoothUnitPurityIso A N hN hA p c hB
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
    let u₀ := ((WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition A z p).app
      (constantComplex A B)).symm
    let u₁ := regularExceptionalIdentityUnitor A B (z ≫ p)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin c)) B)
    let u := u₀ ≪≫ u₁
    let qPrime := regularDualizingQPrimeIso A z (m : ℤ) ((m + c : ℕ) : ℤ) (c : ℤ)
      (by simp only [Nat.cast_add]) (dualizingComplex A a_X) (dualizingComplex A a_B)
      b P_X P_B
    let Φ_z := qPrime ≪≫ (regularCoprojectionIso A z (c : ℤ)).symm
    Φ_z.inv = (rightDerivedUpperShriek A z).map γ_p.hom ≫ u.hom := by
  let : NeZero (ringChar A) := ⟨CharP.ringChar_ne_zero_of_finite A⟩
  let N := ell ^ n
  let hN : 0 < N := pow_pos (Fact.out : ell.Prime).pos n
  let S := Spec (.of k)
  let a_B : B ⟶ S := B ↘ S
  let X := 𝔸(ULift.{u} (Fin c); B)
  let p : X ⟶ B := X ↘ B
  let z : B ⟶ X := AffineSpace.zeroSection (ULift.{u} (Fin c)) B
  let a_X : X ⟶ S := p ≫ a_B
  let : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian a_B
  let : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace a_B
  let : IsNoetherian B := {}
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  let : SmoothOfRelativeDimension c p := by
    have h := AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin c)) B
    rwa [Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  let : SmoothOfRelativeDimension (m + c) a_X := by
    simpa only [Nat.add_comm] using
      (inferInstance : SmoothOfRelativeDimension (c + m) (p ≫ a_B))
  let hS : IsUnit (N : Γ(S, ⊤)) := by
    simpa only [N, map_pow, map_natCast, Nat.cast_pow] using
      (h_ell.pow n).map (Scheme.ΓSpecIso (.of k)).inv.hom
  let hB : IsUnit (N : Γ(B, ⊤)) := by
    simpa only [map_natCast] using hS.map a_B.appTop.hom
  let hX : IsUnit (N : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hB.map p.appTop.hom
  let : HasInvertibleExponent A S := ⟨N, hN, hA, hS⟩
  let : HasInvertibleExponent A B := ⟨N, hN, hA, hB⟩
  let : HasInvertibleExponent A X := ⟨N, hN, hA, hX⟩
  let γ_B := regularSmoothUnitPurityIso A N hN hA a_B m hS
  let γ_X := regularSmoothUnitPurityIso A N hN hA a_X (m + c) hS
  let γ_p := regularSmoothUnitPurityIso A N hN hA p c hB
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
  let u₀ := ((WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition A z p).app
    (constantComplex A B)).symm
  let u₁ := regularExceptionalIdentityUnitor A B (z ≫ p)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin c)) B)
  let u := u₀ ≪≫ u₁
  let qPrime := regularDualizingQPrimeIso A z (m : ℤ) ((m + c : ℕ) : ℤ) (c : ℤ)
    (by simp only [Nat.cast_add]) (dualizingComplex A a_X) (dualizingComplex A a_B)
    b P_X P_B
  let Φ_z := qPrime ≪≫ (regularCoprojectionIso A z (c : ℤ)).symm
  change Φ_z.inv = (rightDerivedUpperShriek A z).map γ_p.hom ≫ u.hom
  let G := rightDerivedUpperShriek A z
  let T := derivedTensor (ModuleCat.{u + 1} A) B
  let v := regularPurityAtTateIso A N hN hA p c hB m
  let U := regularExceptionalSectionUnitor A p z
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin c)) B)
  let q := regularDualizingQIso A z (m : ℤ) ((m + c : ℕ) : ℤ)
    (dualizingComplex A a_X) (dualizingComplex A a_B) b P_X P_B
  let D := (regularCoprojectionIso A z ((m + c : ℕ) : ℤ)).inv ≫
    G.map v.hom ≫ U.hom.app (shiftedTateObject A B (m : ℤ))
  let r := (regularCoprojectionIso A z (c : ℤ)).inv ≫
    G.map γ_p.hom ≫ U.hom.app (constantComplex A B)
  have hU : U.app (constantComplex A B) = u := by
    dsimp only [U, u, u₀, u₁, regularExceptionalSectionUnitor]
    rw [NatIso.trans_app, regularExceptionalIdentityNatIso_unit]
    rfl
  have hraw := regular_coordinate_orientation_cancellation A k ell n hn hA h_ell B m c
  change P_B.inv ≫ b.hom ≫ G.map P_X.hom ≫ G.map v.hom ≫
    U.hom.app (shiftedTateObject A B (m : ℤ)) = 𝟙 _ at hraw
  have hq : q.hom ≫ D = 𝟙 _ := by
    dsimp only [q, D, regularDualizingQIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.symm_hom] using hraw
  have hr := regular_section_tate_evaluation A N hN hA p z c hB m
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin c)) B)
  have hcancel := cancel_tensor_pairing T q (regularInverseTateEvaluation A B (m : ℤ))
    (regularCancelBaseTateIso A B (G.obj (constantComplex A X)) m c) D r hq hr
  have hp : qPrime.hom ≫ r = 𝟙 _ := by
    simpa only [qPrime, regularDualizingQPrimeIso, regularInverseTateEvaluation,
      regularCancelBaseTateIso, Iso.trans_hom, Category.assoc] using hcancel
  have hi : qPrime.inv = r := by
    calc
      qPrime.inv = qPrime.inv ≫ (𝟙 _) := (Category.comp_id _).symm
      _ = qPrime.inv ≫ (qPrime.hom ≫ r) := by rw [hp]
      _ = r := by simp
  dsimp only [Φ_z, Iso.trans_inv, Iso.symm_inv]
  rw [hi]
  dsimp only [r]
  rw [← hU]
  simp only [Iso.hom_inv_id_assoc]
  rfl

end AlgebraicGeometry.Etale
