/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.Sites.FiniteDisjointCover
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.CategoryTheory.Sites.IsDisjointCover.DisjointSheafSections

/-! # Flat sections over objects admitting finite disjoint refinements

Source: Stacks Project, Tags 08FC and 00HK.
(blueprint: lem-zl-partition-flat-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

attribute [local instance 2000] cochainModulesMonoidal

/-- Sections of flat sheaves remain flat at an object with finite disjoint refinements.

Source: Stacks Project, Tags 08FC and 00HK
(blueprint: lem-zl-partition-flat-sections).

Proof: a finite scalar relation in sections has local flatness witnesses by the
local equational criterion. Refine the covering sieve to a finite disjoint cover.
For each piece choose its finite witness. Index the global witness by the disjoint
union of those finite index sets. Extend each coefficient and each witness section
by zero to the other pieces and glue. On a fixed piece only the summands indexed by
that piece survive, so both required identities hold there. Separatedness gives
them globally. Reindex the finite disjoint union by Fin and apply the equational
criterion for flatness of modules over a ring. The empty cover and empty witness
sets are included in the same sums. -/
theorem evaluation_preservesFlat_of_finiteDisjointRefinements
    (W : C) (hW : J.HasFiniteDisjointRefinements W) :
    (evaluation.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) (op
        W)).PreservesFlat := by
  classical
  constructor
  intro M hM
  let : CommRing (((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj.obj (op W)) :=
    inferInstanceAs (CommRing (R.obj.obj (op W)))
  apply (ModuleCat.flat_iff_flat _).2
  change Module.Flat (R.obj.obj (op W)) (M.val.obj (op W))
  apply Module.Flat.iff_forall_isTrivialRelation.mpr
  intro n a s hs
  have hMsite : IsFlatOnSite.{c, v, max c v r, max c v r} (R := R) M := by
    have e := siteSheafTensorRightIso.{c, v, max c v r} R M
    exact (exactFunctor _ _).prop_of_iso e.symm hM.2
  obtain ⟨S, hS, hlocal⟩ :=
    local_equationalCriterion_of_isFlatOnSite.{c, v, max c v r, 0} R M hMsite
      W n a s hs
  obtain ⟨q, Y, f, hf, hmem⟩ := hW S hS
  choose l b t hst hat using fun i : Fin q ↦ hlocal (Y i) (f i) (hmem i)
  let FR := (sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).obj R
  let FM := (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max c v r})).obj
    ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)).obj M)
  let K := Σ i : Fin q, Fin (l i)
  obtain ⟨B, hB⟩ : ∃ B : Fin n → K → R.obj.obj (op W),
      ∀ p j i, R.obj.map (f i).op (B p j) =
        Pi.single (M := fun i ↦ R.obj.obj (op (Y i))) j.1 (b j.1 p j.2) i := by
    choose B hB using fun (p : Fin n) (j : K) ↦
      GrothendieckTopology.IsDisjointCover.exists_type_map_eq hf FR (Pi.single (M := fun i ↦
        R.obj.obj (op (Y i))) j.1 (b j.1 p j.2))
    exact ⟨B, hB⟩
  obtain ⟨z, hz⟩ : ∃ z : K → M.val.obj (op W),
      ∀ j i, M.val.restrictₛₗ (f i).op (z j) = Pi.single (M := fun i ↦ M.val.obj (op (Y i))) j.1 (t
        j.1 j.2) i := by
    choose z hz using fun j : K ↦
      GrothendieckTopology.IsDisjointCover.exists_type_map_eq hf FM (Pi.single (M := fun i ↦
        M.val.obj (op (Y i))) j.1 (t j.1 j.2))
    exact ⟨z, hz⟩
  have hres (i : Fin q) (a : R.obj.obj (op W)) (x : M.val.obj (op W)) :
      M.val.restrictₛₗ (f i).op (a • x) =
        R.obj.map (f i).op a • M.val.restrictₛₗ (f i).op x :=
    M.val.map_smul (f i).op a x
  have hst' (p : Fin n) : s p = ∑ j : K, B p j • z j := by
    apply GrothendieckTopology.IsDisjointCover.type_ext hf FM
    intro i
    change M.val.restrictₛₗ (f i).op (s p) = M.val.restrictₛₗ (f i).op (∑ j : K, B p j • z j)
    simp only [map_sum, hres, hB, hz]
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single i]
    · have hh : M.val.restrictₛₗ (f i).op (s p) =
          ∑ j, b i p j • t i j := hst i p
      simpa only [Pi.single_eq_same] using hh
    · intro k hk hki
      simp only [Pi.single_eq_of_ne hki.symm, zero_smul, Finset.sum_const_zero]
    · exact fun hi ↦ (hi (Finset.mem_univ i)).elim
  have hat' (j : K) : ∑ p : Fin n, a p * B p j = 0 := by
    apply GrothendieckTopology.IsDisjointCover.type_ext hf FR
    intro i
    change R.obj.map (f i).op (∑ p : Fin n, a p * B p j) = R.obj.map (f i).op 0
    simp only [map_sum, map_mul, hB, map_zero]
    by_cases h : j.1 = i
    · subst i
      simpa only [Pi.single_eq_same] using hat j.1 j.2
    · simp only [Pi.single_eq_of_ne (Ne.symm h), mul_zero, Finset.sum_const_zero]
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, (fun p j ↦ B p (e.symm j)), (fun j ↦ z (e.symm j)), ?_, ?_⟩
  · intro p
    rw [e.symm.sum_comp (fun j : K ↦ B p j • z j)]
    exact hst' p
  · intro j
    exact hat' (e.symm j)

end SheafOfModules
