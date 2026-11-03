/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DualizingComplex

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteComparison
import WeilConjectures.AlgebraicGeometry.FiniteRingGeometricDualityFiniteField
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import all WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport

/-! Finite coefficient part of the biduality assembly. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] DerivedCategory.symmetricCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing
set_option maxHeartbeats 1200000 in
-- The comparison transport elaborates large derived-category instances.
/-- Finite coefficients: transport the finite etale comparison and the canonical
field-extension square to the constructible exceptional adjunction.  The proof uses
finite comparison localizing, the evaluation-transpose normalization, and faithful
exact pullback from an algebraic closure; these data identify the displayed native
map, so no abstract object isomorphism is substituted for it.
Source: latest blueprint, det-pd-biduality-coefficients.proof.md, paragraph (i).
(blueprint: det-pd-biduality-finite-coefficient-case).

Proof: unpack the finite coefficient presentation. The comparison witness supplies a
braided realization F, an etale origin L of K, the dualizing isomorphism w and the two
invertible Hom mates at L and its dual. The annihilation exponent supplies the
invertible-exponent instance over the base. Over an algebraically closed field use the
supplied finite biduality hypothesis; over a finite field use algebraic-closure descent.
The symmetric evaluation comparison formula expresses delta at F(L) as F(delta_L)
composed with two isomorphisms. Thus it is invertible. Naturality of delta transports
invertibility through the isomorphism F(L) ≅ K. -/
theorem isIso_biduality_finite_coefficient_case
    (_finiteBiduality : ∀ (A : Type (u + 1)) [CommRing A] [Finite A]
      (F : Type u) [Field F] [IsAlgClosed F]
      [HasInvertibleExponent A (Spec (.of F))]
      (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F))
      [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
      (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))),
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y L →
        IsIso ((Etale.verdierDualDoubleDual A aY).app L))
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hbase : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (hfinite : ∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
      Finite A ∧ (∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A)))
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ X.left) :
    IsIso (toIhomIhom
      (coefficientCaseDualizingComplex ell k hbase Λ hΛ X) K.obj) := by
  obtain ⟨A, hA, tA, dA, rA, hf, hn, ⟨e⟩⟩ := hfinite
  let := hA
  let := tA
  let := dA
  let := rA
  let := hf
  let : HasCompactification X.hom := (NagataCompactification X.hom).hasCompactification
  obtain ⟨F, hF, L, w, eK, hL, hβ, hβD⟩ :=
    finiteCoefficientComparisonWitness ell k hbase Λ hΛ A hn e X K
  let := hF
  obtain ⟨n, hn⟩ := hn
  have hnil : (ell : ULift.{u + 1} A) ^ n = 0 := by
    apply (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).injective
    simpa only [map_pow, map_natCast, map_zero, nsmul_eq_mul, mul_one, Nat.cast_pow]
      using hn 1
  let : HasInvertibleExponent (ULift.{u + 1} A) (Spec (.of k)) := ⟨ell ^ n,
    pow_pos (Fact.out : ell.Prime).pos n, by simpa only [Nat.cast_pow] using hnil, by
      have hell : (ell : k) ≠ 0 := by
        intro h
        exact (Fact.out : ringChar k ≠ ell)
          (CharP.ringChar_of_prime_eq_zero (Fact.out : ell.Prime) h)
      have hu : IsUnit ((ell ^ n : ℕ) : k) := by
        simpa only [Nat.cast_pow] using (isUnit_iff_ne_zero.mpr hell).pow n
      simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  let hδ : IsIso ((Etale.verdierDualDoubleDual (ULift.{u + 1} A) X.hom).app L) := by
    rcases hbase with hk | hk
    · let := hk
      have hkill : ∃ r : ℕ, 1 ≤ r ∧ ∀ x : ULift.{u + 1} A, (ell ^ r) • x = 0 := by
        refine ⟨n + 1, Nat.succ_pos n, ?_⟩
        intro x
        rw [nsmul_eq_mul, Nat.cast_pow, pow_succ, hnil, zero_mul, zero_mul]
      exact Etale.isIso_verdierDualDoubleDual_app_finiteField
        (ringChar k) ell (Fact.out : ringChar k ≠ ell) k (ULift.{u + 1} A)
        hkill X.hom hL
    · let := hk
      exact _finiteBiduality (ULift.{u + 1} A) k X.left X.hom L hL
  let : SymmetricCategory
      (DerivedCategory (ModuleRingedComparison.internalModules Λ X.left)) :=
    DerivedCategory.symmetricCategory _
  let hδ' : IsIso (toIhomIhom
      (coefficientCaseDualizingComplex ell k hbase Λ hΛ X) (F.obj L)) := by
    rw [CategoryTheory.MonoidalClosed.comparison_bidual F w L hβ hβD]
    change IsIso (F.map ((Etale.verdierDualDoubleDual
      (ULift.{u + 1} A) X.hom).app L) ≫ _ ≫ _)
    infer_instance
  have he : toIhomIhom (coefficientCaseDualizingComplex ell k hbase Λ hΛ X) K.obj =
      eK.inv ≫ toIhomIhom (coefficientCaseDualizingComplex ell k hbase Λ hΛ X)
        (F.obj L) ≫
        (pre ((pre eK.hom).app
          (coefficientCaseDualizingComplex ell k hbase Λ hΛ X))).app
            (coefficientCaseDualizingComplex ell k hbase Λ hΛ X) := by
    rw [← toIhomIhom_naturality, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance
end AlgebraicGeometry.ProEtale.CondensedRing
