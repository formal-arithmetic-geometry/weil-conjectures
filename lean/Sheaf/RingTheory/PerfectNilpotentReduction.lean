/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.RingTheory.NilpotentProjectiveComplexLift
import WeilConjectures.RingTheory.NakayamaNilpotent
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.Pi

/-! # Perfectness is reflected by reduction modulo a nilpotent ideal

Source: Stacks Project, Tag 09C5, first proof paragraph, using Tag 09AR and
nilpotent Nakayama (Tag 00DV).
(blueprint: lem-sfb-perfect-nilpotent-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w w'
open CategoryTheory CategoryTheory.Limits

private theorem finite_of_nilpotent_quotient
    {A : Type u} [CommRing A] (I : Ideal A) (hI : ∃ k : ℕ, 0 < k ∧ I ^ k = ⊥)
    (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A (M ⧸ I • (⊤ : Submodule A M))] : Module.Finite A M := by
  classical
  let N := I • (⊤ : Submodule A M)
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M ⧸ N)
  choose t ht using fun i ↦ N.mkQ_surjective (s i)
  let f : (Fin n → A) →ₗ[A] M := (Pi.basisFun A (Fin n)).constr A t
  have hmap : Function.Surjective (N.mkQ.comp f) := by
    rw [← LinearMap.range_eq_top]
    have hf : N.mkQ.comp f = (Pi.basisFun A (Fin n)).constr A s := by
      apply (Pi.basisFun A (Fin n)).ext
      intro i
      simpa [f] using ht i
    rw [hf, Module.Basis.constr_range]
    exact hs
  have hquot : Function.Surjective
      ((I • ⊤ : Submodule A (Fin n → A)).mapQ N f
        (Submodule.smul_top_le_comap_smul_top I f)) := by
    intro x
    obtain ⟨y, hy⟩ := hmap x
    exact ⟨Submodule.Quotient.mk y, hy⟩
  exact Module.Finite.of_surjective f
    (RingTheory.surjective_of_surjective_mod_nilpotent A _ _ I f hI hquot)

private noncomputable def nilpotentReductionIso
    {A : Type u} [CommRing A] (I : Ideal A) (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M ≅
      ModuleCat.of (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M)) := by
  let e := TensorProduct.quotTensorEquivQuotSMul M I
  let e' : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M ≃ₗ[A ⧸ I]
      (M ⧸ I • (⊤ : Submodule A M)) :=
    { __ := e.toAddEquiv
      map_smul' := by
        intro a x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact e.map_smul a x }
  exact e'.toModuleIso

private theorem zero_of_nilpotent_quotient
    {A : Type u} [CommRing A] (I : Ideal A) (hI : ∃ k : ℕ, 0 < k ∧ I ^ k = ⊥)
    (M : ModuleCat.{u} A)
    (hM : IsZero ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M)) : IsZero M := by
  have := ModuleCat.subsingleton_of_isZero hM
  have : Subsingleton (M ⧸ I • (⊤ : Submodule A M)) :=
    (nilpotentReductionIso I M).toLinearEquiv.symm.injective.subsingleton
  have htop : I • (⊤ : Submodule A M) = ⊤ := by
    apply top_unique
    intro x _
    exact (Submodule.Quotient.mk_eq_zero _).mp (Subsingleton.elim _ _)
  have hp (n : ℕ) : I ^ n • (⊤ : Submodule A M) = ⊤ := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Submodule.mul_smul, htop, ih]
  obtain ⟨k, _, hk⟩ := hI
  have hz : (⊤ : Submodule A M) = ⊥ := by rw [← hp k, hk, Submodule.bot_smul]
  have : Subsingleton M := ⟨fun x y ↦ by
    have hx : x = 0 := hz.le (Submodule.mem_top (x := x))
    have hy : y = 0 := hz.le (Submodule.mem_top (x := y))
    exact hx.trans hy.symm⟩
  exact ModuleCat.isZero_of_subsingleton M

namespace DerivedCategory

/-- A complex whose derived reduction modulo a nilpotent ideal is perfect is perfect.

Source: Stacks Project, Tags 09C5 (first proof paragraph), 09AR and 00DV.
(blueprint: lem-sfb-perfect-nilpotent-reduction).

Proof: represent the perfect reduction by a bounded finite-projective complex E.
Nilpotent projective-complex lifting gives a projective complex P representing C and
an actual isomorphism between its termwise reduction and E. If a term of E vanishes,
its lifted term equals its product by I; iteration to a zero power of I kills the term.
Thus P has the same lower and upper bounds as E. For any other term, lift finitely many
generators of its quotient to obtain a map from a finite free module. The quotient map
is surjective, so nilpotent Nakayama makes the original map surjective. Its target is
therefore finite. This proves boundedness and finite projectivity of the representative.
The argument permits the zero ring, the zero ideal, and zero or contractible complexes. -/
theorem perfect_of_nilpotent_reduction
    {A : Type u} [CommRing A] (I : Ideal A)
    (hI : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = ⊥)
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (A ⧸ I))]
    (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} (A ⧸ I)))
    (ε : Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (Ideal.Quotient.mk I))
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
        (.up ℤ) ⋙ Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))]
    (C : DerivedCategory (ModuleCat.{u} A))
    (hC : IsPerfectRingComplex (L.obj C)) : IsPerfectRingComplex C := by
  obtain ⟨E, a, b, ha, hb, hE, ⟨e⟩⟩ := hC
  obtain ⟨P, _, hP, ⟨eP⟩, ⟨ered⟩⟩ :=
    CochainComplex.exists_projective_lift_of_nilpotent A I hI L ε C E ⟨b, hb⟩
      (fun i ↦ (hE i).1) ⟨e⟩
  let et (i : ℤ) : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj (P.X i) ≅ E.X i :=
    (HomologicalComplex.eval _ _ i).mapIso ered
  refine ⟨P, a, b, ?_, ?_, ?_, ⟨eP.symm⟩⟩
  · apply (P.isStrictlyGE_iff a).2
    intro i hi
    exact zero_of_nilpotent_quotient I hI (P.X i)
      (((E.isStrictlyGE_iff a).1 ha i hi).of_iso (et i))
  · apply (P.isStrictlyLE_iff b).2
    intro i hi
    exact zero_of_nilpotent_quotient I hI (P.X i)
      (((E.isStrictlyLE_iff b).1 hb i hi).of_iso (et i))
  · intro i
    refine ⟨hP i, ?_⟩
    have := (hE i).2
    have : Module.Finite (A ⧸ I) (P.X i ⧸ I • (⊤ : Submodule A (P.X i))) :=
      Module.Finite.equiv ((et i).symm ≪≫ nilpotentReductionIso I (P.X i)).toLinearEquiv
    have : Module.Finite A (P.X i ⧸ I • (⊤ : Submodule A (P.X i))) :=
      Module.Finite.trans (A ⧸ I) _
    exact finite_of_nilpotent_quotient I hI (P.X i)

end DerivedCategory
