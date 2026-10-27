/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Localization.Away.Basic

import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Elimination of fixed generators by an invertible relation minor

Source: Stacks Project, More on Algebra, Tag 07ZC, lemma-fitting-ideal-generate-locally,
constructive relation-minor refinement of (1) implies (4); Algebra, Tag 07DQ;
Schemes, Tag 01HV (blueprint: lem-trf-invertible-relation-minor-generators).

## Main statements

* `LinearMap.invertible_relation_minor_generators` gives the two adjugate identities,
  generation of the localized module by the last generators, and generation of the
  associated sheaf on the principal open by their canonical restricted sections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace LinearMap

private theorem map_eq_sum_basis {R N : Type*} [CommRing R] [AddCommGroup N]
    [Module R N] {n : ℕ} (f : (Fin n → R) →ₗ[R] N) (v : Fin n → R) :
    f v = ∑ i, v i • f (Pi.single i 1) := by
  have hv : v = ∑ i, v i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul]

private theorem relation_adjugate {R N : Type*} [CommRing R] [AddCommGroup N]
    [Module R N] {a b : ℕ} (C : Matrix (Fin a) (Fin a) R)
    (D : Matrix (Fin a) (Fin b) R) (x : Fin a → N) (y : Fin b → N)
    (hrow : ∀ k, (∑ l, C k l • x l) + ∑ j, D k j • y j = 0) (i : Fin a) :
    C.det • x i + ∑ k, ∑ j, (C.adjugate i k * D k j) • y j = 0 := by
  have hc (l : Fin a) :
      (∑ k, C.adjugate i k * C k l) = if i = l then C.det else 0 := by
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using
      congrArg (fun E : Matrix (Fin a) (Fin a) R ↦ E i l) (Matrix.adjugate_mul C)
  have hx : (∑ k, C.adjugate i k • ∑ l, C k l • x l) = C.det • x i := by
    simp_rw [Finset.smul_sum, ← mul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hc]
    simp
  calc
    _ = ∑ k, C.adjugate i k • ((∑ l, C k l • x l) + ∑ j, D k j • y j) := by
      simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, ← mul_smul] at hx ⊢
      rw [hx]
    _ = 0 := by simp only [hrow, smul_zero, Finset.sum_const_zero]

/-- A square block of relations eliminates its corresponding generators after inverting
its determinant. The adjugate is Mathlib's transposed cofactor matrix: for positive size,
`Matrix.adjugate_fin_succ_eq_det_submatrix` deletes row `j` and column `i` in entry `(i,j)`.
`Fin.castAdd b` indexes the first block and `Fin.natAdd a` the last block. The final
existential merely packages the specified canonical sections as compatible families on
all opens contained in `D(det C)`; its `Epi` clause is generation as a sheaf, rather than
surjectivity on every open. No finiteness of the relation module is required.

Source: Stacks Project, More on Algebra, Tag 07ZC, lemma-fitting-ideal-generate-locally,
constructive refinement of (1) implies (4), with Algebra, Tag 07DQ and Schemes, Tag 01HV
(blueprint: lem-trf-invertible-relation-minor-generators).

Proof plan (the constructive refinement is the node's agent argument):
1. Each row lies in the kernel of the surjection. Apply `LocalizedModule.mkLinearMap`
   to obtain `Cx + Dy = 0`. Multiply the kth equation by `C.adjugate i k`, sum over k,
   and distribute the finite sums. `lem-weil-pbc-matrix-adjugate-identity`, namely
   `Matrix.adjugate_mul`, gives `det C • x + adj(C)Dy = 0` with the stated cofactor
   convention.
2. `IsLocalization.Away.invSelf` is the inverse of the image of `det C`. Multiply by
   it to solve for each first generator. Every localized element is a fraction of an
   element of M; surjectivity writes its numerator in the original generators.
   Substitute the solved first generators to express the fraction in the last b.
   For a = 0 the determinant is 1; for b = 0 the span is zero. A zero determinant
   or the zero ring gives a zero localization and is included.
3. On `D(det C * h)`, `lem-weil-pbc-spec-module-tilde-sections` identifies sections
   with the module localized at `det C * h`. The fraction map sends `m / det(C)^k`
   to `h^k m / (det(C) * h)^k`, and similarly for scalars. Transport step 2 through
   this map and multiply by the denominator inverse to express every section there
   in the specified last sections. For an open V inside `D(det C)` and a point p in V,
   write its complement as V(I) and choose h in I outside p. Then p belongs to
   `D(det C * h)` inside V. These basic opens therefore give local lifts on every
   open. This is exactly the epimorphism in
   `def-weil-pbc-generating-sections`, including the empty open and empty family.
-/
theorem invertible_relation_minor_generators
    (A : CommRingCat.{u}) (M : ModuleCat.{u} A) (a b : ℕ)
    (π : (Fin (a + b) → A) →ₗ[A] M) (hπ : Function.Surjective π)
    (C : Matrix (Fin a) (Fin a) A) (D : Matrix (Fin a) (Fin b) A)
    (hrel : ∀ k : Fin a, π (Fin.append (C k) (D k)) = 0) :
    (∀ i : Fin a,
      C.det • LocalizedModule.mkLinearMap (Submonoid.powers C.det) M
          (π (Pi.single (Fin.castAdd b i) 1)) +
        ∑ k : Fin a, ∑ j : Fin b,
          (C.adjugate i k * D k j) •
            LocalizedModule.mkLinearMap (Submonoid.powers C.det) M
              (π (Pi.single (Fin.natAdd a j) 1)) = 0) ∧
    (∀ i : Fin a,
      LocalizedModule.mkLinearMap (Submonoid.powers C.det) M
          (π (Pi.single (Fin.castAdd b i) 1)) =
        -((IsLocalization.Away.invSelf C.det : Localization.Away C.det) •
          ∑ k : Fin a, ∑ j : Fin b,
            (C.adjugate i k * D k j) •
              LocalizedModule.mkLinearMap (Submonoid.powers C.det) M
                (π (Pi.single (Fin.natAdd a j) 1)))) ∧
    Submodule.span (Localization.Away C.det)
      (Set.range (fun j : Fin b ↦
        LocalizedModule.mkLinearMap (Submonoid.powers C.det) M
          (π (Pi.single (Fin.natAdd a j) 1)))) = ⊤ ∧
    (∃ s : ULift.{u} (Fin b) → ((tilde M).over (PrimeSpectrum.basicOpen C.det)).sections,
      (∀ (j : ULift.{u} (Fin b)) (V : (Over (PrimeSpectrum.basicOpen C.det))ᵒᵖ),
        (s j).val V = tilde.toOpen M V.unop.left
          (π (Pi.single (Fin.natAdd a j.down) 1))) ∧
      Epi (((tilde M).over (PrimeSpectrum.basicOpen C.det)).freeHomEquiv.symm s)) := by
  classical
  let f := (LocalizedModule.mkLinearMap (Submonoid.powers C.det) M).comp π
  let x (i : Fin a) := f (Pi.single (Fin.castAdd b i) 1)
  let y (j : Fin b) := f (Pi.single (Fin.natAdd a j) 1)
  have hrow (k : Fin a) : (∑ l, C k l • x l) + ∑ j, D k j • y j = 0 := by
    have h := map_eq_sum_basis f (Fin.append (C k) (D k))
    rw [Fin.sum_univ_add] at h
    simpa [f, x, y, hrel] using h.symm
  have hfirst := relation_adjugate C D x y hrow
  have hsolve (i : Fin a) : x i =
      -((IsLocalization.Away.invSelf C.det : Localization.Away C.det) •
        ∑ k, ∑ j, (C.adjugate i k * D k j) • y j) := by
    have h := congrArg
      ((IsLocalization.Away.invSelf C.det : Localization.Away C.det) • ·) (hfirst i)
    rw [smul_add, smul_zero, ← algebraMap_smul (Localization.Away C.det) C.det,
      ← mul_smul, mul_comm (IsLocalization.Away.invSelf C.det),
      IsLocalization.Away.mul_invSelf, one_smul] at h
    exact eq_neg_of_add_eq_zero_left h
  refine ⟨hfirst, hsolve, ?_, ?_⟩
  · let P := Submodule.span (Localization.Away C.det) (Set.range y)
    have hy (j : Fin b) : y j ∈ P := Submodule.subset_span ⟨j, rfl⟩
    have hx (i : Fin a) : x i ∈ P := by
      rw [hsolve]
      exact P.neg_mem (P.smul_mem _ (P.sum_mem fun k _ ↦ P.sum_mem fun j _ ↦
        P.smul_of_tower_mem _ (hy j)))
    apply top_unique
    intro z _
    induction z using LocalizedModule.induction_on with
    | _ m s =>
      obtain ⟨v, rfl⟩ := hπ m
      have hv : f v ∈ P := by
        rw [map_eq_sum_basis f v, Fin.sum_univ_add]
        exact P.add_mem (P.sum_mem fun i _ ↦ P.smul_of_tower_mem _ (hx i))
          (P.sum_mem fun j _ ↦ P.smul_of_tower_mem _ (hy j))
      have he : LocalizedModule.mk (π v) s =
          (Localization.mk (1 : A) s : Localization.Away C.det) • f v := by
        dsimp [f, LocalizedModule.mkLinearMap]
        rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
      rw [he]
      exact P.smul_mem _ hv
  · let U := PrimeSpectrum.basicOpen C.det
    let s : ULift.{u} (Fin b) → ((tilde M).over U).sections := fun j ↦
      ⟨fun V ↦ tilde.toOpen M V.unop.left (π (Pi.single (Fin.natAdd a j.down) 1)),
        fun v ↦ rfl⟩
    refine ⟨s, fun _ _ ↦ rfl, ?_⟩
    constructor
    intro N p q hpq
    have hlast (j : Fin b) (V : (Over U)ᵒᵖ) :
        p.val.app V (tilde.toOpen M V.unop.left (π (Pi.single (Fin.natAdd a j) 1))) =
        q.val.app V (tilde.toOpen M V.unop.left (π (Pi.single (Fin.natAdd a j) 1))) := by
      have h := congrArg (fun e ↦ (N.freeHomEquiv e (ULift.up j)).val V) hpq
      simpa only [SheafOfModules.freeHomEquiv_comp_apply,
        Equiv.apply_symm_apply, SheafOfModules.sectionsMap,
        PresheafOfModules.sectionsMap, PresheafOfModules.sectionsMk, s] using h
    have hrowM (k : Fin a) :
        (∑ l, C k l • π (Pi.single (Fin.castAdd b l) 1)) +
          ∑ j, D k j • π (Pi.single (Fin.natAdd a j) 1) = 0 := by
      have h := map_eq_sum_basis π (Fin.append (C k) (D k))
      rw [Fin.sum_univ_add] at h
      simpa [hrel] using h.symm
    have hall (i : Fin (a + b)) (V : (Over U)ᵒᵖ) :
        p.val.app V (tilde.toOpen M V.unop.left (π (Pi.single i 1))) =
        q.val.app V (tilde.toOpen M V.unop.left (π (Pi.single i 1))) := by
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ hlast j V) i
      have hm := relation_adjugate C D
        (fun l ↦ π (Pi.single (Fin.castAdd b l) 1))
        (fun j ↦ π (Pi.single (Fin.natAdd a j) 1)) hrowM i
      have ht := congrArg (tilde.toOpen M V.unop.left) hm
      simp only [map_add, map_sum, map_smul, map_zero] at ht
      let r : Γ(Spec A, V.unop.left) := algebraMap A _ C.det
      have hu : IsUnit r := by
        exact (IsLocalization.Away.algebraMap_isUnit (S := Γ(Spec A, U)) C.det).map
          ((Spec A).presheaf.map V.unop.hom.op).hom
      have hsm (c : A) (z : Γ(tilde M, V.unop.left)) :
          c • z = (algebraMap A Γ(Spec A, V.unop.left) c) • z :=
        (algebraMap_smul _ c z).symm
      simp_rw [hsm] at ht
      have hp := congrArg (p.val.app V) ht
      have hq := congrArg (q.val.app V) ht
      simp only [map_add, map_sum, map_smul, map_zero] at hp hq
      apply hu.smul_left_cancel.mp
      dsimp [r]
      have hs :
          (∑ k, ∑ j, algebraMap A Γ(Spec A, V.unop.left)
              (C.adjugate i k * D k j) •
            p.val.app V (tilde.toOpen M V.unop.left
              (π (Pi.single (Fin.natAdd a j) 1)))) =
          ∑ k, ∑ j, algebraMap A Γ(Spec A, V.unop.left)
              (C.adjugate i k * D k j) •
            q.val.app V (tilde.toOpen M V.unop.left
              (π (Pi.single (Fin.natAdd a j) 1))) := by
        exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦
          congrArg ((algebraMap A Γ(Spec A, V.unop.left)
            (C.adjugate i k * D k j)) • ·) (hlast j V)
      rw [hs] at hp
      exact add_right_cancel (hp.trans hq.symm)
    have : (SheafOfModules.overFunctor (Spec A).ringCatSheaf U).Additive :=
      { map_add := by intros; rfl }
    let F := tilde.functor A ⋙ SheafOfModules.overFunctor (Spec A).ringCatSheaf U
    have hπepi : Epi (ModuleCat.ofHom π) := (ModuleCat.epi_iff_surjective _).mpr hπ
    have : F.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_adjunction
      ((tilde.adjunction (R := A)).comp
        (SheafOfModules.overPushforwardOverAdj (R := (Spec A).ringCatSheaf) U))
    have hFepi : Epi (F.map (ModuleCat.ofHom π)) := F.map_epi _
    apply (cancel_epi (F.map (ModuleCat.ofHom π))).mp
    have hdecomp : ModuleCat.ofHom π =
        ∑ i : Fin (a + b),
          ModuleCat.ofHom (LinearMap.proj i) ≫
            ModuleCat.ofHom ((LinearMap.id : A →ₗ[A] A).smulRight
              (π (Pi.single i 1))) := by
      ext v
      simp
    rw [hdecomp, F.map_sum]
    simp only [Preadditive.sum_comp, F.map_comp, Category.assoc]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Γ(Spec A, V.unop.left) at r
    let g := (F.map (ModuleCat.ofHom ((LinearMap.id : A →ₗ[A] A).smulRight
      (π (Pi.single i 1))))).val.app V
    have hc : g (1 : Γ(Spec A, V.unop.left)) =
        tilde.toOpen M V.unop.left (π (Pi.single i 1)) := by
      change (tilde.map (ModuleCat.ofHom
        ((LinearMap.id : A →ₗ[A] A).smulRight (π (Pi.single i 1))))).val.app
          (Opposite.op V.unop.left) (1 : Γ(Spec A, V.unop.left)) = _
      have h := congrArg (fun t ↦ t (1 : A))
        (tilde.toOpen_map_app (ModuleCat.ofHom
          ((LinearMap.id : A →ₗ[A] A).smulRight (π (Pi.single i 1)))) V.unop.left)
      change (tilde.map (ModuleCat.ofHom
        ((LinearMap.id : A →ₗ[A] A).smulRight (π (Pi.single i 1))))).val.app
          (Opposite.op V.unop.left)
          (tilde.toOpen (ModuleCat.of A A) V.unop.left (1 : A)) =
        tilde.toOpen M V.unop.left ((1 : A) • π (Pi.single i 1)) at h
      have hone : tilde.toOpen (ModuleCat.of A A) V.unop.left (1 : A) =
          (1 : Γ(Spec A, V.unop.left)) := by
        change algebraMap A Γ(Spec A, V.unop.left) (1 : A) = 1
        exact map_one _
      rw [hone, one_smul] at h
      exact h
    have hh := hall i V
    rw [← hc] at hh
    change p.val.app V (g r) = q.val.app V (g r)
    have hg : g r = r • g (1 : Γ(Spec A, V.unop.left)) := by
      simpa only [smul_eq_mul, mul_one] using
        g.hom.map_smul r (1 : Γ(Spec A, V.unop.left))
    rw [hg, map_smul, map_smul, hh]

end LinearMap
