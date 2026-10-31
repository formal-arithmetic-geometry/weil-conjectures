/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Finite-index enlargement of a lattice through a divisible subgroup

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVI, Lemma 3.6.4,
printed pages 252--253 (blueprint: lem-per-divisible-unit-lattice-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AddCommGroup

/-- A map from a finite free abelian group extends to a finite free enlargement that
surjects onto the torsion-free quotient by an `n`-divisible subgroup.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVI, Lemma 3.6.4,
printed pages 252--253 (blueprint: lem-per-divisible-unit-lattice-extension).

Proof: write `C = B / D`, `f = p.comp φ`, and `Q = C / f.range`. Induct strongly
on the positive finite cardinality of `Q`. If `Q` is trivial, take `G = L`, the identity
inclusion and `h = φ`; exponent zero suffices. Otherwise choose a nonzero class `q`
represented by `c = p b`. Its order `d` is at least two and divides `n`. Choose `a`
with `f a = d • c`, so `d • b - φ a` lies in `D`. Divisibility by `n`, and hence by
`d`, lets us adjust `b` inside its `D`-coset so that `d • b = φ a`.

If `d • x + k • a = 0`, torsion-freeness of `C` first implies `f x + k • c = 0`.
The order of `q` gives `k = d * t`; torsion-freeness of `L` then gives `x = -t • a`.
Conversely these pairs give all relations. Form the subgroup `L₁ = dL + ℤa` of `L`.
It is finite free by `lem-weil-subgroup-finite-free-abelian-group-free`, namely
`Submodule.basisOfPid` after choosing a finite basis of `L`. The map `j x = d • x`
is injective. Define `φ₁ (d • x + k • a) = φ x + k • b`; the relation calculation
and `d • b = φ a` prove well-definedness and additivity. Then `φ₁.comp j = φ`, and
`L₁ / j(L)` is killed by `d`, hence by `n`.

The image in `C` is `f(L) + ℤc`, so the new cokernel is `Q / ⟨q⟩`, of cardinality
`|Q| / d < |Q|`, still killed by `n`. Apply induction to `L₁, φ₁`. Compose its
injection `i₁` with `j`. If `n^s • g = i₁ y`, then `n • y` belongs to `j(L)`, so
`n^(s+1) • g` belongs to the composite image. The composite is injective, extends
`φ`, and still surjects onto `C`, as required. -/
theorem divisible_unit_lattice_extension
    (n : ℕ) (hn : 1 ≤ n)
    (L : Type u) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : Type v) [AddCommGroup B] (D : AddSubgroup B) (φ : L →+ B)
    (hD : ∀ d : D, ∃ e : D, n • e = d)
    [IsAddTorsionFree (B ⧸ D)]
    [Finite ((B ⧸ D) ⧸ ((QuotientAddGroup.mk' D).comp φ).range)]
    (hQ : ∀ q : (B ⧸ D) ⧸ ((QuotientAddGroup.mk' D).comp φ).range, n • q = 0) :
    ∃ (G : Type u) (_ : AddCommGroup G),
      Module.Free ℤ G ∧ Module.Finite ℤ G ∧
      ∃ (i : L →+ G) (h : G →+ B),
        Function.Injective i ∧
        (∃ s : ℕ, ∀ q : G ⧸ i.range, n ^ s • q = 0) ∧
        h.comp i = φ ∧ Function.Surjective ((QuotientAddGroup.mk' D).comp h) := by
  -- Use the full-rank subgroup f⁻¹(nC) and diagonal bases instead of cyclic induction.
  classical
  have hn0 : n ≠ 0 := by omega
  have hnZ : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn0
  let C := B ⧸ D
  let p := QuotientAddGroup.mk' D
  let f := (p.comp φ).toIntLinearMap
  let m : C →ₗ[ℤ] C := (n : ℤ) • LinearMap.id
  let S : Submodule ℤ L := m.range.comap f
  let i : L →ₗ[ℤ] S :=
    { toFun := fun x ↦ ⟨(n : ℤ) • x, ⟨f x, by simp [m]⟩⟩
      map_add' := fun x y ↦ Subtype.ext (smul_add _ _ _)
      map_smul' := fun a x ↦ Subtype.ext (smul_comm _ _ _) }
  have hi : Function.Injective i := by
    intro x y h
    exact smul_right_injective L hnZ (congrArg Subtype.val h)
  have hrank : Module.finrank ℤ S = Module.finrank ℤ L := by
    exact le_antisymm
      (S.subtype.finrank_le_finrank_of_injective S.subtype_injective)
      (i.finrank_le_finrank_of_injective hi)
  let b := Module.Free.chooseBasis ℤ L
  let bL := S.smithNormalFormTopBasis b hrank
  let bS := S.smithNormalFormBotBasis b hrank
  let a := S.smithNormalFormCoeffs b hrank
  have hab (j) : (bS j : L) = a j • bL j :=
    S.smithNormalFormBotBasis_def b hrank j
  have ha0 (j) : a j ≠ 0 := S.smithNormalFormCoeffs_ne_zero b hrank j
  let t := fun j ↦ bS.repr (i (bL j)) j
  have ht (j) : a j * t j = (n : ℤ) := by
    let coord : S →ₗ[ℤ] ℤ := (Finsupp.lapply j).comp (bL.repr.toLinearMap.comp S.subtype)
    have hc : coord = a j • (Finsupp.lapply j).comp bS.repr.toLinearMap := by
      apply bS.ext
      intro k
      change bL.repr (bS k : L) j = a j * bS.repr (bS k) j
      rw [hab, map_smul]
      by_cases h : k = j
      · subst k
        simp
      · simp [Module.Basis.repr_self, Ne.symm h]
    have hh := LinearMap.congr_fun hc (i (bL j))
    simpa [coord, i, t] using hh.symm
  have roots (j) : ∃ z : B, t j • z = φ (bL j) := by
    obtain ⟨c, hc⟩ := (bS j).property
    change (n : ℤ) • c = f (bS j) at hc
    obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_surjective D c
    have hf : f (bL j) = t j • c := by
      apply zsmul_right_injective (ha0 j)
      calc
        a j • f (bL j) = f (bS j) := by rw [hab, map_smul]
        _ = (n : ℤ) • c := hc.symm
        _ = a j • (t j • c) := by rw [← mul_smul, ht]
    have hu : t j • z - φ (bL j) ∈ D := by
      apply (QuotientAddGroup.eq_zero_iff _).mp
      change p (t j • z - φ (bL j)) = 0
      simp only [map_sub, map_zsmul]
      change t j • p z - f (bL j) = 0
      rw [hz, hf, sub_self]
    obtain ⟨e, he⟩ := hD ⟨_, hu⟩
    have he' : (n : ℤ) • (e : B) = t j • z - φ (bL j) := by
      simpa using congrArg Subtype.val he
    refine ⟨z - a j • (e : B), ?_⟩
    rw [smul_sub, smul_smul, mul_comm (t j), ht, he']
    abel
  choose z hz using roots
  let h := (bS.constr ℤ z).toAddMonoidHom
  have hext : h.comp i.toAddMonoidHom = φ := by
    apply AddMonoidHom.toIntLinearMap_injective
    apply bL.ext
    intro j
    have hij : i (bL j) = t j • bS j := by
      apply Subtype.ext
      change (n : ℤ) • bL j = t j • (bS j : L)
      rw [hab, smul_smul, mul_comm (t j), ht]
    change h (i (bL j)) = φ (bL j)
    rw [hij, map_zsmul]
    simpa [h] using hz j
  refine ⟨S, inferInstance, inferInstance, inferInstance, i.toAddMonoidHom, h, hi, ?_, hext, ?_⟩
  · refine ⟨1, ?_⟩
    intro q
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective i.toAddMonoidHom.range q
    rw [pow_one, ← map_nsmul]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    refine ⟨(y : L), ?_⟩
    apply Subtype.ext
    simp [i]
  · intro c
    have hc : n • c ∈ (p.comp φ).range := by
      apply (QuotientAddGroup.eq_zero_iff _).mp
      change (QuotientAddGroup.mk' (p.comp φ).range) (n • c) = 0
      rw [map_nsmul]
      exact hQ _
    obtain ⟨x, hx⟩ := hc
    let y : S := ⟨x, c, by simpa [m, f] using hx.symm⟩
    refine ⟨y, ?_⟩
    apply nsmul_right_injective hn0
    have hy : n • y = i x := by apply Subtype.ext; simp [i, y]
    change n • p (h y) = n • c
    rw [← map_nsmul, ← map_nsmul, hy]
    exact (congrArg p (DFunLike.congr_fun hext x)).trans hx

end AddCommGroup
