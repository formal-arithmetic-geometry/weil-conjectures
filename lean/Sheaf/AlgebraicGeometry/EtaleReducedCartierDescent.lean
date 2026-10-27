/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.AlgebraicGeometry.FpqcCartierIdealReflection
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étale descent of reduced Cartier divisors

Source: literature/stacks-project/spaces-divisors.tex, Tag 083C, with reduced pullback
from literature/stacks-project/descent.tex, Tag 034E, and literature/stacks-project/schemes.tex,
Tag 01J3 (blueprint: lem-trf-etale-reduced-cartier-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/--
Étale pullback preserves the reduced induced closed subscheme, and the effective Cartier
condition descends along a jointly surjective étale family.

Source: Stacks Project, spaces-divisors.tex Tag 083C, conditions (1)--(3), together with
Descent Tag 034E and Schemes Tag 01J3 for the reduced pullback identification. The covering
family is indexed by a type in an arbitrary universe.
(blueprint: lem-trf-etale-reduced-cartier-descent)

Proof:
1. The pullback of the reduced induced closed immersion is a closed immersion with the
   pulled-back ideal. The projection to the reduced induced subscheme is étale by base
   change, hence the pullback is reduced; its image is the inverse image of the closed
   subset, so uniqueness of the reduced induced structure gives the displayed isomorphism.
2. An effective Cartier ideal pulls back along an étale (hence flat) morphism, so the
   forward implication holds for every member of the family.
3. A jointly surjective étale family is an fpqc cover. The ideals of the pulled-back
   reduced subschemes are the pullbacks of the original ideal. Effective Cartier ideals
   are invertible, and fpqc descent of finite locally free rank one reflects invertibility;
   the invertible-ideal/effective-Cartier equivalence gives the converse. The empty
   divisor is covered by the unit ideal.
-/
theorem etale_reduced_cartier_descent
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (Z : TopologicalSpace.Closeds X) :
    (∀ (W : Scheme.{u}) (v : W ⟶ X) [Etale v],
      ∃ e : pullback v (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≅
          (Scheme.IdealSheafData.vanishingIdeal
            (Z.preimage v.continuous)).subscheme,
        e.hom ≫ (Scheme.IdealSheafData.vanishingIdeal
            (Z.preimage v.continuous)).subschemeι =
          pullback.fst v (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) ∧
    (∀ {ι : Type*} (W : ι → Scheme.{u}) (v : ∀ i, W i ⟶ X)
        [∀ i, Etale (v i)],
      (⋃ i, Set.range (v i).base = Set.univ) →
      ((Scheme.IdealSheafData.vanishingIdeal Z).IsInvertible ↔
        ∀ i, (Scheme.IdealSheafData.vanishingIdeal
          (Z.preimage (v i).continuous)).IsInvertible)) := by
  have : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    (Scheme.IdealSheafData.reduced_induced_closed_subscheme X Z).2.2.2.1
  have hlocal (W : Scheme.{u}) (v : W ⟶ X) [Etale v] :
      (pullback.fst v (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).ker =
          Scheme.IdealSheafData.vanishingIdeal (Z.preimage v.continuous) ∧
      ∃ e : pullback v (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≅
          (Scheme.IdealSheafData.vanishingIdeal (Z.preimage v.continuous)).subscheme,
        e.hom ≫ (Scheme.IdealSheafData.vanishingIdeal
          (Z.preimage v.continuous)).subschemeι =
            pullback.fst v (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
    have : IsReduced (pullback v (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
      isReduced_of_etale (pullback.snd v _)
    obtain ⟨_, _, _, _, _, _, _, huniq⟩ :=
      Scheme.IdealSheafData.reduced_induced_closed_subscheme W (Z.preimage v.continuous)
    have hrange : Set.range
        (pullback.fst v (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) =
          (Z.preimage v.continuous : Set W) := by
      rw [Scheme.Pullback.range_fst]
      simp
    obtain ⟨hk, e, he, _⟩ := huniq _ (pullback.fst v _) hrange
    exact ⟨hk, e, he⟩
  refine ⟨fun W v _ ↦ (hlocal W v).2, ?_⟩
  intro ι W v _ hcover
  constructor
  · intro h i
    have hflat := h.comap_of_flat (v i)
    change (pullback.fst (v i)
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).ker.IsInvertible at hflat
    rwa [(hlocal (W i) (v i)).1] at hflat
  · intro h
    have hfpqc : Presieve.ofArrows W v ∈ Scheme.fpqcPrecoverage X := by
      apply Scheme.fppfPrecoverage_le_fpqcPrecoverage
      apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
      refine ⟨?_, fun i ↦ ⟨inferInstance, inferInstance⟩⟩
      intro x
      have hx : x ∈ (Set.univ : Set X) := Set.mem_univ x
      rw [← hcover] at hx
      exact Set.mem_iUnion.mp hx
    have hJ (i : ι) :
        (pullback.snd (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
          (v i)).ker.IsInvertible := by
      rw [← Scheme.Hom.ker_comp_of_isIso
        (pullbackSymmetry (v i)
          (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).hom]
      simpa only [pullbackSymmetry_hom_comp_snd, (hlocal (W i) (v i)).1] using h i
    have hdesc := (fpqc_cartier_ideal_reflection
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι W v hfpqc hJ).2.2
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using hdesc

end AlgebraicGeometry
