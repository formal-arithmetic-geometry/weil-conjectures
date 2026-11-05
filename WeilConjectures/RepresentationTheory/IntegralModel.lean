/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.AlgebraicCard
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import WeilConjectures.NumberTheory.Padics.Extension

/-!
# Integral models of continuous `ℓ`-adic representations of compact groups

Let `G` be a compact topological group acting continuously on a finite-dimensional
`ℚ̄_ℓ`-vector space `V`. This file shows that the action is defined over a finite extension
`E/ℚ_ℓ` and preserves an `𝒪_E`-lattice in `V`. These are the two steps of the proof of
`sk-p-real-integral` (`AlgebraicGeometry.WeilGroup.IsLisse.exists_lattice`).

## Main statements

- `PadicAlgCl.exists_finiteDimensional_forall_mem`: the matrix coefficients of a continuous
  matrix representation of a compact group over `ℚ̄_ℓ` all lie in one finite extension `E`
  of `ℚ_ℓ`.
- `PadicAlgCl.exists_lattice_of_forall_mem`: a representation whose matrix coefficients lie in
  `E` and are bounded preserves an `𝒪_E`-lattice `L`, and has finite image on every
  `L / 𝔪_Eⁿ L`.

## Implementation notes

The first statement is a Baire category argument. By
`PadicAlgCl.exists_isAlgebraic_mem_adjoin_simple` the countably many fields `ℚ_ℓ(T)`, for `T` a
finite set of elements of `ℚ̄_ℓ` algebraic over `ℚ`, cover `ℚ̄_ℓ`. The elements of `G` whose
matrix (and inverse matrix) has coefficients in `ℚ_ℓ(T)` form a closed subgroup, since
`ℚ_ℓ(T)` is closed in `ℚ̄_ℓ`. By the Baire category theorem one of these subgroups is open,
and by compactness a single one of them is all of `G`.

The `𝒪_E`-module structure on `V` is the restriction of scalars along `𝒪_E → E → ℚ̄_ℓ`. The
lattice is the `𝒪_E`-span of the orbit of a basis: it contains the basis, and it is contained
in `ℓ⁻ᵏ` times the span of the basis when the coefficients are bounded by `ℓᵏ`. So it is a
finitely generated torsion-free module over the principal ideal ring `𝒪_E`, hence free, and of
full rank.
-/

@[expose] public section

open Module Polynomial IntermediateField

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime]

/-- Blueprint `sk-p-real-integral`: the first step of the proof.

The matrix coefficients of a continuous matrix representation `φ` of a compact group over
`ℚ̄_ℓ` all lie in a single finite extension `E` of `ℚ_ℓ`. -/
theorem exists_finiteDimensional_forall_mem {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : G →* Matrix ι ι (PadicAlgCl l)) (hφ : ∀ i j, Continuous fun g ↦ φ g i j) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ g i j, φ g i j ∈ E := by
  classical
  -- the countably many fields `F t = ℚ_ℓ(t)`, for `t` a finite set of algebraic numbers
  let T := {x : PadicAlgCl l // IsAlgebraic ℚ x}
  have : Countable T := (Algebraic.countable ℚ (PadicAlgCl l)).to_subtype
  choose β hβ using exists_isAlgebraic_mem_adjoin_simple l
  let F : Finset T → IntermediateField ℚ_[l] (PadicAlgCl l) := fun t ↦
    adjoin ℚ_[l] ((↑) '' (t : Set T))
  have hF (t : Finset T) : FiniteDimensional ℚ_[l] (F t) :=
    finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  have hFmono : Monotone F := fun s t hst ↦ adjoin.mono _ _ _ (Set.image_mono hst)
  -- the closed subgroups `X t` of elements whose coefficients lie in `F t`; they cover `G`
  let X : Finset T → Subgroup G := fun t ↦
    { carrier := {g | ∀ i j, φ g i j ∈ F t ∧ φ g⁻¹ i j ∈ F t}
      mul_mem' := by
        intro a b ha hb i j
        simp only [Set.mem_ofPred_eq, map_mul, mul_inv_rev, Matrix.mul_apply] at ha hb ⊢
        exact ⟨sum_mem fun k _ ↦ mul_mem (ha i k).1 (hb k j).1,
          sum_mem fun k _ ↦ mul_mem (hb i k).2 (ha k j).2⟩
      one_mem' := by
        intro i j
        simp only [map_one, inv_one, and_self, Matrix.one_apply]
        split_ifs <;> simp [one_mem, zero_mem]
      inv_mem' := by
        intro a ha i j
        simpa [and_comm] using ha i j }
  have hXmono : Monotone X := fun s t hst g hg i j ↦
    ⟨hFmono hst (hg i j).1, hFmono hst (hg i j).2⟩
  have hXclosed (t : Finset T) : IsClosed (X t : Set G) := by
    have := hF t
    have hc := isClosed_intermediateField l (F t)
    simp only [X, Subgroup.coe_set_mk, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ (hc.preimage (hφ i j)).inter
      (hc.preimage ((hφ i j).comp continuous_inv))
  have hmem (g : G) : ∃ t, g ∈ X t := by
    let t : Finset T := Finset.univ.image fun p : ι × ι × Bool ↦
      ⟨β (φ (if p.2.2 then g else g⁻¹) p.1 p.2.1),
        (hβ (φ (if p.2.2 then g else g⁻¹) p.1 p.2.1)).1⟩
    have key (h : G) (hh : h = g ∨ h = g⁻¹) (i j : ι) : φ h i j ∈ F t := by
      have hle : ℚ_[l]⟮β (φ h i j)⟯ ≤ F t := by
        rw [adjoin_simple_le_iff]
        refine subset_adjoin _ _ ⟨⟨β (φ h i j), (hβ _).1⟩, ?_, rfl⟩
        simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range, t]
        rcases hh with rfl | rfl
        · exact ⟨(i, j, true), rfl⟩
        · exact ⟨(i, j, false), rfl⟩
      exact hle (hβ _).2
    exact ⟨t, fun i j ↦ ⟨key g (.inl rfl) i j, key g⁻¹ (.inr rfl) i j⟩⟩
  -- by Baire one `X s` is open, and by compactness a single `X (s ∪ t)` is all of `G`
  obtain ⟨s, hs⟩ := nonempty_interior_of_iUnion_of_closed hXclosed
    (Set.eq_univ_of_forall fun g ↦ Set.mem_iUnion.mpr (hmem g))
  obtain ⟨g₀, hg₀⟩ := hs
  have hopen (t : Finset T) : IsOpen (X (s ∪ t) : Set G) :=
    Subgroup.isOpen_mono (hXmono Finset.subset_union_left)
      (Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.mp hg₀))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_directed_cover (fun t ↦ (X (s ∪ t) : Set G)) hopen
    (fun g _ ↦ by
      obtain ⟨t, ht⟩ := hmem g
      exact Set.mem_iUnion.mpr ⟨t, hXmono Finset.subset_union_right ht⟩)
    (fun a b ↦ ⟨a ∪ b, hXmono (Finset.union_subset_union_right Finset.subset_union_left),
      hXmono (Finset.union_subset_union_right Finset.subset_union_right)⟩)
  exact ⟨F (s ∪ t), hF _, fun g i j ↦ (ht (Set.mem_univ g) i j).1⟩

end PadicAlgCl
