/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyFilteredColimit
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProfiniteCoefficientCohomology
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology

/-!
# Cohomological dimension of the constant `ℓ`-adic sheaf

Let `S` be a quasi-compact quasi-separated scheme of finite type and of dimension at most `d`
over a separably closed field. Then the pro-étale cohomology `Hᵠ(S_proét, ℚ̄_ℓ)` of the constant
`ℓ`-adic sheaf `ℚ̄_ℓ,S = AlgebraicGeometry.ProEtale.adicConstantSheaf l S` (of locally finite
continuous functions to `ℚ̄_ℓ`) vanishes for `q > 2d`.

Indeed `ℚ̄_ℓ,S` is the filtered union of the subsheaves `U ↦ C(U, L)` of continuous functions
with values in the compact subgroups `L = V ∩ {‖x‖ ≤ ℓⁿ}`, for `V ⊆ ℚ̄_ℓ` a finite-dimensional
`ℚ_ℓ`-subspace: a locally finite function is, on an affine open, a continuous function with
compact image in a finite-dimensional subspace. Each `L` is profinite, the limit of the finite
discrete groups `L/(L ∩ {‖x‖ ≤ ℓ⁻ᵐ})`, so its cohomology vanishes above `2d`
(`AlgebraicGeometry.ProEtale.subsingleton_H_continuousSheaf_of_two_mul_lt_of_compact`), and
cohomology commutes with filtered colimits on a qcqs scheme
(`AlgebraicGeometry.Scheme.ProEt.subsingleton_H_of_isColimit_of_isFiltered`).

## Main statements

- `AlgebraicGeometry.ProEtale.subsingleton_H_adicConstantSheaf_of_two_mul_lt`:
  `Hᵠ(S_proét, ℚ̄_ℓ) = 0` for `q > 2d`, for the underlying abelian sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

section Lattice

/-- The compact subgroup `span_{ℚ_ℓ}(s) ∩ {‖x‖ ≤ ℓⁿ}` of `ℚ̄_ℓ`, for `k = (s, n)`. -/
noncomputable def adicLattice (k : Finset (PadicAlgCl l) × ℕ) : AddSubgroup (PadicAlgCl l) :=
  (Submodule.span ℚ_[l] (k.1 : Set (PadicAlgCl l))).toAddSubgroup ⊓
    (IsUltrametricDist.closedBall_openAddSubgroup (PadicAlgCl l)
      (r := (l : ℝ) ^ k.2) (by have := (Fact.out : l.Prime).pos; positivity)).toAddSubgroup

variable {l}

lemma mem_adicLattice {k : Finset (PadicAlgCl l) × ℕ} {x : PadicAlgCl l} :
    x ∈ adicLattice l k ↔
      x ∈ Submodule.span ℚ_[l] (k.1 : Set (PadicAlgCl l)) ∧ ‖x‖ ≤ (l : ℝ) ^ k.2 := by
  simp [adicLattice, IsUltrametricDist.closedBall_openAddSubgroup]

lemma one_le_l : (1 : ℝ) ≤ l := by
  exact_mod_cast (Fact.out : l.Prime).one_lt.le

lemma adicLattice_mono {k k' : Finset (PadicAlgCl l) × ℕ} (h : k ≤ k') :
    adicLattice l k ≤ adicLattice l k' := fun x hx ↦ by
  rw [mem_adicLattice] at hx ⊢
  exact ⟨Submodule.span_mono (Finset.coe_subset.2 h.1) hx.1,
    hx.2.trans (pow_le_pow_right₀ one_le_l h.2)⟩

instance (k : Finset (PadicAlgCl l) × ℕ) : CompactSpace (adicLattice l k) := by
  refine (isCompact_iff_compactSpace (s := (adicLattice l k : Set (PadicAlgCl l)))).mp ?_
  let V := Submodule.span ℚ_[l] (k.1 : Set (PadicAlgCl l))
  have : FiniteDimensional ℚ_[l] V := FiniteDimensional.span_finset _ _
  have : ProperSpace V := FiniteDimensional.proper ℚ_[l] V
  convert (isCompact_closedBall (0 : V) ((l : ℝ) ^ k.2)).image continuous_subtype_val using 1
  ext x
  simp only [SetLike.mem_coe, mem_adicLattice, Set.mem_image, Metric.mem_closedBall,
    dist_zero_right]
  exact ⟨fun h ↦ ⟨⟨x, h.1⟩, h.2, rfl⟩, by rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩⟩

/-- The open subgroups `L ∩ {‖x‖ ≤ ℓ⁻ᵐ}` of the lattice `L`. -/
noncomputable def adicLatticeNbhd (k : Finset (PadicAlgCl l) × ℕ) (m : ℕ) :
    AddSubgroup (adicLattice l k) :=
  (IsUltrametricDist.closedBall_openAddSubgroup (PadicAlgCl l)
    (r := ((l : ℝ) ^ m)⁻¹) (by have := (Fact.out : l.Prime).pos; positivity)).toAddSubgroup.comap
      (adicLattice l k).subtype

lemma mem_adicLatticeNbhd {k : Finset (PadicAlgCl l) × ℕ} {m : ℕ} {x : adicLattice l k} :
    x ∈ adicLatticeNbhd k m ↔ ‖(x : PadicAlgCl l)‖ ≤ ((l : ℝ) ^ m)⁻¹ := by
  change (x : PadicAlgCl l) ∈ Metric.closedBall 0 _ ↔ _
  simp

lemma antitone_adicLatticeNbhd (k : Finset (PadicAlgCl l) × ℕ) :
    Antitone (adicLatticeNbhd k) := fun m m' h x hx ↦ by
  rw [mem_adicLatticeNbhd] at hx ⊢
  exact hx.trans (inv_anti₀ (by have := (Fact.out : l.Prime).pos; positivity)
    (pow_le_pow_right₀ one_le_l h))

lemma isOpen_adicLatticeNbhd (k : Finset (PadicAlgCl l) × ℕ) (m : ℕ) :
    IsOpen (adicLatticeNbhd k m : Set (adicLattice l k)) :=
  (IsUltrametricDist.closedBall_openAddSubgroup (PadicAlgCl l)
    (r := ((l : ℝ) ^ m)⁻¹) (by have := (Fact.out : l.Prime).pos; positivity)).isOpen.preimage
      continuous_subtype_val

lemma eq_zero_of_forall_mem_adicLatticeNbhd {k : Finset (PadicAlgCl l) × ℕ}
    (x : adicLattice l k) (hx : ∀ m, x ∈ adicLatticeNbhd k m) : x = 0 := by
  by_contra h
  have hpos : 0 < ‖(x : PadicAlgCl l)‖ :=
    norm_pos_iff.2 fun h' ↦ h (Subtype.ext h')
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos
    (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt :
      (1 : ℝ) < l))
  have := mem_adicLatticeNbhd.1 (hx m)
  rw [inv_pow] at hm
  linarith

end Lattice

end AlgebraicGeometry.ProEtale
