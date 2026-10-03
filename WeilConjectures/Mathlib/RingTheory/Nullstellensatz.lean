/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Nullstellensatz

/-!
# The Nullstellensatz for finitely generated algebras

Let `A` be a finitely generated algebra over an algebraically closed field `k`. Every maximal ideal
of `A` is the kernel of a `k`-algebra map `A →ₐ[k] k`, i.e. closed points of `Spec A` have residue
field `k`; and an element of `A` vanishing at every `k`-point is nilpotent.

## Main results

- `exists_algHom_ker_eq_of_isMaximal`: maximal ideals are kernels of `k`-points.
- `iInf_ker_algHom_eq_nilradical`: the vanishing principle.
- `eq_zero_of_forall_algHom_apply_eq_zero`: the vanishing principle on a reduced algebra.
- `existsUnique_comp_mkₐ_eq_of_forall_algHom`: a regular map sending `k`-points into a closed
  subvariety factors through it.

## Blueprint

- `sk-i-geometry`: the Nullstellensatz and the vanishing principle.
- `lem-wf-affine-nullstellensatz-vanishing`: residue fields of closed points and the vanishing
  principle.
-/

@[expose] public section

variable (k A : Type*) [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- Over an algebraically closed field `k`, every maximal ideal of a finitely generated
`k`-algebra is the kernel of a `k`-algebra map to `k`: closed points have residue field `k`.
(blueprint: `sk-i-geometry`) -/
theorem exists_algHom_ker_eq_of_isMaximal (𝔪 : Ideal A) [𝔪.IsMaximal] :
    ∃ φ : A →ₐ[k] k, RingHom.ker φ = 𝔪 := by
  let : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have : Module.Finite k (A ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing k _
  refine ⟨(IsAlgClosed.lift : (A ⧸ 𝔪) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k 𝔪), ?_⟩
  ext a
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- The vanishing principle: over an algebraically closed field `k`, an element of a finitely
generated `k`-algebra vanishing at every `k`-point is nilpotent.
(blueprint: `sk-i-geometry`) -/
theorem iInf_ker_algHom_eq_nilradical :
    (⨅ φ : A →ₐ[k] k, RingHom.ker φ) = nilradical A := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  refine le_antisymm ?_ ?_
  · rw [nilradical, Ideal.radical_eq_jacobson, Ideal.jacobson]
    refine le_sInf ?_
    rintro 𝔪 ⟨-, h𝔪⟩
    obtain ⟨φ, rfl⟩ := exists_algHom_ker_eq_of_isMaximal k A 𝔪
    exact iInf_le _ φ
  · exact le_iInf fun φ ↦ @nilradical_le_prime _ _ _ (RingHom.ker_isPrime φ)

/-- Blueprint `lem-wf-affine-nullstellensatz-vanishing`, clause (2) (the vanishing principle): over
an algebraically closed field `k`, an element of a reduced finitely generated `k`-algebra vanishing
at every `k`-point is zero.

By `iInf_ker_algHom_eq_nilradical` such an element is nilpotent, hence zero. Clause (1), that the
closed points are the `k`-points, is `exists_algHom_ker_eq_of_isMaximal`. -/
theorem eq_zero_of_forall_algHom_apply_eq_zero [IsReduced A] {a : A}
    (h : ∀ φ : A →ₐ[k] k, φ a = 0) : a = 0 := by
  have : a ∈ nilradical A := by
    rw [← iInf_ker_algHom_eq_nilradical k A, Ideal.mem_iInf]
    exact fun φ ↦ h φ
  rwa [nilradical_eq_zero, Submodule.zero_eq_bot, Ideal.mem_bot] at this

/-- Blueprint `lem-wf-affine-nullstellensatz-vanishing`, clause (3): let `f : B →ₐ[k] A` be the
coordinate map of a regular map `X → Y` of affine varieties over an algebraically closed field `k`,
with `A` reduced and finitely generated, and let `J` be an ideal of `B` (cutting out `Z ⊆ Y`). If
every `k`-point of `X` maps into `Z`, i.e. `φ (f b) = 0` for every `k`-point `φ` of `X` and
`b ∈ J`, then `f` factors uniquely through `B ⧸ J`.

Each `f b` with `b ∈ J` vanishes at every `k`-point, so it is zero by the vanishing principle
`eq_zero_of_forall_algHom_apply_eq_zero`; uniqueness holds as `B → B ⧸ J` is surjective. -/
theorem existsUnique_comp_mkₐ_eq_of_forall_algHom {B : Type*} [CommRing B] [Algebra k B]
    [IsReduced A] (f : B →ₐ[k] A) (J : Ideal B) (h : ∀ φ : A →ₐ[k] k, ∀ b ∈ J, φ (f b) = 0) :
    ∃! g : B ⧸ J →ₐ[k] A, g.comp (Ideal.Quotient.mkₐ k J) = f := by
  have hJ (b : B) (hb : b ∈ J) : f b = 0 :=
    eq_zero_of_forall_algHom_apply_eq_zero k A fun φ ↦ h φ b hb
  refine ⟨Ideal.Quotient.liftₐ J f hJ, by ext; simp, fun g hg ↦ ?_⟩
  exact Ideal.Quotient.algHom_ext k (by rw [hg]; ext; simp)
