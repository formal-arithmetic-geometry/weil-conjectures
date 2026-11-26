/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import WeilConjectures.RingTheory.DerivedModuleScalarAdjunction
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.PseudoCoherentInverseRingReconstruction

/-!
# Effectivity of a normalized algebra tower

Facts about the tower of quotients `C/J^n` of an adically complete ring used to reconstruct
pseudo-coherent objects over it.

## References

* [Stacks, Tags 09AV, 066E, 0CQF]
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- An adically complete ring is the limit of its positive-power quotients. -/
theorem adic_quotient_limit {C : Type u} [CommRing C]
    (J : Ideal C) [IsAdicComplete J C]
    (x : ∀ n : ℕ, C ⧸ J ^ (n + 1))
    (hx : ∀ n : ℕ, Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))) (x (n + 1)) = x n) :
    ∃! a : C, ∀ n, Ideal.Quotient.mk (J ^ (n + 1)) a = x n := by
  classical
  choose y hy using fun n ↦ Ideal.Quotient.mk_surjective (x n)
  have hxy (m n : ℕ) (h : m ≤ n) :
      Ideal.Quotient.mk (J ^ (m + 1)) (y n) = x m := by
    have he := Ideal.Quotient.eq_factor_of_eq_factor_succ
      (I := fun k ↦ J ^ (k + 1))
      (fun i j hij ↦ Ideal.pow_le_pow_right (Nat.add_le_add_right hij 1)) x
      (fun k ↦ (hx k).symm) h
    rw [← hy n] at he
    exact he.symm
  have hc : ∀ {m n : ℕ}, m ≤ n →
      y m ≡ y n [SMOD (J ^ m • ⊤ : Submodule C C)] := by
    intro m n h
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    apply SModEq.of_toAddSubgroup_le
      (U := J ^ (m + 1)) (V := J ^ m)
      (Ideal.pow_le_pow_right (Nat.le_succ m))
    change Ideal.Quotient.mk (J ^ (m + 1)) (y m) =
      Ideal.Quotient.mk (J ^ (m + 1)) (y n)
    rw [hy m, hxy m n h]
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete J C) hc
  have hqa (n : ℕ) : Ideal.Quotient.mk (J ^ (n + 1)) a = x n := by
    have hn := ha (n + 1)
    rw [Ideal.smul_eq_mul, Ideal.mul_top] at hn
    change Ideal.Quotient.mk (J ^ (n + 1)) (y (n + 1)) =
      Ideal.Quotient.mk (J ^ (n + 1)) a at hn
    exact hn.symm.trans (hxy n (n + 1) (Nat.le_succ n))
  refine ⟨a, hqa, ?_⟩
  intro b hb
  have he : (fun _ : Unit ↦ b) = fun _ : Unit ↦ a :=
    IsHausdorff.StrictMono.funext' J (fun i j hij ↦ Nat.add_lt_add_right hij 1)
      (fun n _ ↦ (hb n).trans (hqa n).symm)
  exact congrFun he ()

/-- Each consecutive positive-power quotient map has square-zero kernel. -/
theorem adic_step_nilpotent {C : Type u} [CommRing C] (J : Ideal C) (n : ℕ) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))) := by
  refine ⟨2, ?_⟩
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
  apply le_antisymm _ bot_le
  calc
    Ideal.map (Ideal.Quotient.mk (J ^ (n + 2))) (J ^ ((n + 1) * 2)) ≤
        Ideal.map (Ideal.Quotient.mk (J ^ (n + 2))) (J ^ (n + 2)) :=
      Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
    _ = ⊥ := Ideal.map_quotient_self _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical derived restriction-composition isomorphism agrees with its
normalization on complexes. -/
theorem restrictScalarsComp_derived_factors
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} S)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} T)]
    (f : R →+* S) (g : S →+* T) (gf : R →+* T) (hgf : gf = g.comp f)
    (P : CochainComplex (ModuleCat.{max u v} T) ℤ) :
    ((Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp' f g gf hgf)) ≪≫
      (Functor.mapDerivedCategoryCompIso (ModuleCat.restrictScalars g)
        (ModuleCat.restrictScalars f)).symm).hom.app (Q.obj P) ≫
      (ModuleCat.restrictScalars f).mapDerivedCategory.map
        ((ModuleCat.restrictScalars g).mapDerivedCategoryFactors.hom.app P) ≫
      (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.hom.app
        (((ModuleCat.restrictScalars g).mapHomologicalComplex (.up ℤ)).obj P) =
    (ModuleCat.restrictScalars gf).mapDerivedCategoryFactors.hom.app P ≫
      Q.map ((NatIso.mapHomologicalComplex
        (ModuleCat.restrictScalarsComp' f g gf hgf) (.up ℤ)).hom.app P) := by
  have hc := Functor.mapDerivedCategoryCompIso_fac (ModuleCat.restrictScalars g)
    (ModuleCat.restrictScalars f) P
  have hid : Q.map ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.restrictScalars g ⋙ ModuleCat.restrictScalars f))
        (.up ℤ)).hom.app P) = 𝟙 _ := by
    rw [← Q.map_id]
    congr 1
  erw [hid, Category.comp_id] at hc
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  erw [hc]
  exact Functor.mapDerivedCategoryNatIso_fac
    (ModuleCat.restrictScalarsComp' f g gf hgf) P

end DerivedCategory
