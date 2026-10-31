/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.GroupTheory.Congruence.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.GroupTheory.Congruence.Hom
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int

/-! # Finite presentations of finitely generated commutative monoids

Source: Stacks Project, Algebra, Tag 00FN (blueprint:
`lem-trf-fg-commutative-monoid-finite-presentation`).

The source supplies the Noetherian input for the binomial-ideal argument; the
finite-presentation consequence is stated here in the additive commutative
monoid notation of the blueprint.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

/- The finite-presentation consequence for a finite generating tuple. -/
/--
Source: Stacks Project, Algebra, Tag 00FN, lemma-Noetherian-permanence
(blueprint: lem-trf-fg-commutative-monoid-finite-presentation).

Proof: write `M = Fin n →₀ ℕ` and let `S` consist of the binomials `[a] - [b]`
with `π a = π b` in `ℤ[M]`. This is the finite-variable polynomial ring over
`ℤ`, so its ideal `Ideal.span S` is finitely generated. Extract a finite subset
of `S` with the same ideal span and select a pair for each of its binomials.
For any additive congruence `c` containing those pairs, the map
`ℤ[M] → ℤ[c.Quotient]` kills each selected binomial, hence all of `Ideal.span S`.
Consequently `π a = π b` implies equality of the basis vectors indexed by the
classes of `a` and `b`, so `c a b`. Conversely the kernel congruence of `π`
contains all the selected pairs. This proves the smallest-congruence assertion
without needing a formula for the kernel ideal. Finally the free homomorphism
`τ` determined by a tuple `t` is constant on the fibres of `π` precisely when
it respects the selected pairs. A right inverse of the surjection `π` then
defines the descended homomorphism; fibre constancy proves additivity and the
values on generators. Every extension composed with `π` equals `τ`, which
also proves uniqueness.
-/
theorem fg_commutative_monoid_finite_presentation
    (R : Type u) [AddCommMonoid R] (n : ℕ) (r : Fin n → R)
    (π : (Fin n →₀ ℕ) →+ R) (hπ : Function.Surjective π)
    (hπ_formula : ∀ a : Fin n →₀ ℕ, π a = a.sum (fun i k => k • r i)) :
    ∃ (m : ℕ) (ab : Fin m → (Fin n →₀ ℕ) × (Fin n →₀ ℕ)),
      (∀ j : Fin m, π (ab j).1 = π (ab j).2) ∧
      (∀ a b : Fin n →₀ ℕ,
        π a = π b ↔
          ∀ c : AddCon (Fin n →₀ ℕ),
            (∀ j : Fin m, c (ab j).1 (ab j).2) → c a b) ∧
      (∀ (T : Type v) [AddCommMonoid T] (t : Fin n → T),
        (∃! f : R →+ T, ∀ i : Fin n, f (r i) = t i) ↔
          ∀ j : Fin m,
            (ab j).1.sum (fun i k => k • t i) =
              (ab j).2.sum (fun i k => k • t i)) := by
  classical
  -- Encode all equal-fibre relations as binomials in a Noetherian ring.
  let M := Fin n →₀ ℕ
  let A := AddMonoidAlgebra ℤ M
  let δ : M → M → A := fun a b ↦
    AddMonoidAlgebra.of' ℤ M a - AddMonoidAlgebra.of' ℤ M b
  let S : Set A := {x | ∃ a b : M, π a = π b ∧ x = δ a b}
  let : IsNoetherianRing A := MvPolynomial.isNoetherianRing_fin
  have hfg : (Ideal.span S).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset S).mp hfg
  change Ideal.span S = Ideal.span (s : Set A) at hspan
  have hrepr : ∀ x : s, ∃ a b : M, π a = π b ∧ (x : A) = δ a b :=
    fun x ↦ hs x.property
  choose a b hab hx using hrepr
  let e := (Fintype.equivFin s).symm
  let ab : Fin (Fintype.card s) → M × M := fun j ↦ (a (e j), b (e j))
  -- Every congruence containing the selected pairs identifies all equal fibres.
  have hrel : ∀ x y : M, π x = π y ↔
      ∀ c : AddCon M, (∀ j, c (ab j).1 (ab j).2) → c x y := by
    intro x y
    constructor
    · intro hxy c hc
      let φ := AddMonoidAlgebra.mapDomainRingHom ℤ c.mk'
      have hle : Ideal.span S ≤ RingHom.ker φ := by
        rw [hspan]
        apply Ideal.span_le.mpr
        intro z hz
        let z' : s := ⟨z, hz⟩
        have hz' := hc (e.symm z')
        have he : e (e.symm z') = z' := e.apply_symm_apply z'
        change c (a (e (e.symm z'))) (b (e (e.symm z'))) at hz'
        rw [he] at hz'
        change (z' : A) ∈ RingHom.ker φ
        rw [hx z']
        change φ (δ (a z') (b z')) = 0
        dsimp only [δ]
        rw [map_sub]
        simp [φ, c.eq.mpr hz']
      have hd : δ x y ∈ Ideal.span S := Ideal.subset_span ⟨x, y, hxy, rfl⟩
      have hz := hle hd
      change φ (δ x y) = 0 at hz
      have heq : AddMonoidAlgebra.single (c.mk' x) (1 : ℤ) =
          AddMonoidAlgebra.single (c.mk' y) (1 : ℤ) := by
        dsimp only [δ] at hz
        rw [map_sub] at hz
        simpa [φ, sub_eq_zero] using hz
      exact c.eq.mp ((AddMonoidAlgebra.single_left_injective (by decide : (1 : ℤ) ≠ 0))
        heq)
    · intro h
      exact h (AddCon.ker π) (fun j ↦ hab (e j))
  refine ⟨Fintype.card s, ab, (fun j ↦ hab (e j)), hrel, ?_⟩
  -- Descend the free homomorphism and prove its universal property.
  intro T _ t
  let τ : M →+ T := Finsupp.liftAddHom fun i ↦
    { toFun := fun k ↦ k • t i
      map_zero' := zero_nsmul _
      map_add' := fun k l ↦ add_nsmul _ _ _ }
  have hτ_formula (x : M) : τ x = x.sum (fun i k ↦ k • t i) := rfl
  have heval (f : R →+ T) (hf : ∀ i, f (r i) = t i) (x : M) :
      f (π x) = τ x := by
    rw [hπ_formula, hτ_formula]
    simp [Finsupp.sum, map_sum, hf]
  constructor
  · rintro ⟨f, hf, _⟩ j
    rw [← hτ_formula, ← hτ_formula, ← heval f hf, ← heval f hf, hab (e j)]
  · intro ht
    have hτ : ∀ x y : M, π x = π y → τ x = τ y := by
      intro x y hxy
      exact (hrel x y).mp hxy (AddCon.ker τ) ht
    let g : R → M := Function.surjInv hπ
    have hg : ∀ x, π (g x) = x := Function.rightInverse_surjInv hπ
    have hcomp (x : M) : τ (g (π x)) = τ x := hτ _ _ (hg (π x))
    let f : R →+ T :=
      { toFun := fun x ↦ τ (g x)
        map_zero' := by
          rw [← π.map_zero, hcomp, τ.map_zero]
        map_add' := fun x y ↦ by
          have h : π (g (x + y)) = π (g x + g y) := by simp [hg]
          exact (hτ _ _ h).trans (τ.map_add _ _) }
    have hf : ∀ i, f (r i) = t i := by
      intro i
      have hsingle : π (Finsupp.single i 1) = r i := by
        simp [hπ_formula]
      change τ (g (r i)) = t i
      rw [← hsingle, hcomp, hτ_formula]
      simp
    refine ⟨f, hf, ?_⟩
    intro f' hf'
    ext x
    obtain ⟨a', rfl⟩ := hπ x
    exact (heval f' hf' a').trans (heval f hf a').symm

end
