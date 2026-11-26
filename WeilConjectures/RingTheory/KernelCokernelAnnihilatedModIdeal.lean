/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Scalar quasi-inverses and reduction modulo an ideal

If the kernel and cokernel of a linear map `u` are killed by `K^t`, then for `f, g ∈ K^t` there
is a quasi-inverse `h` with `h ∘ u = fg` and `u ∘ h = fg`, natural in `u`, and the kernel and
cokernel of `u` modulo any ideal `J` are killed by `K^(2t)`.

## References

* [Stacks, Tag 0888]
-/

@[expose] public section

universe u v v' w w' z z'

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

namespace LinearMap

/-- The kernel and cokernel of `u` are killed by `K^t` if and only if there is an exact
sequence `0 → T → M → N → Q → 0` through `u` with `T` and `Q` killed by `K^t`. -/
theorem ker_coker_annihilated_iff_exists_exact_sequence
    {A : Type u} [CommRing A]
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (K : Ideal A) (t : ℕ) (u : M →ₗ[A] N) :
    (K ^ t ≤ Module.annihilator A (ker u) ∧
      K ^ t ≤ Module.annihilator A (N ⧸ range u)) ↔
    ∃ (T Q : ModuleCat.{v} A) (i : T ⟶ ModuleCat.of A M)
      (p : ModuleCat.of A N ⟶ Q),
      (ComposableArrows.mk₅ (0 : (0 : ModuleCat.{v} A) ⟶ T) i
        (ModuleCat.ofHom u) p (0 : Q ⟶ (0 : ModuleCat.{v} A))).Exact ∧
      K ^ t ≤ Module.annihilator A T ∧ K ^ t ≤ Module.annihilator A Q := by
  constructor
  · rintro ⟨hker, hcoker⟩
    refine ⟨ModuleCat.of A (ker u), ModuleCat.of A (N ⧸ range u),
      ModuleCat.ofHom (ker u).subtype, ModuleCat.ofHom (range u).mkQ, ?_, hker, hcoker⟩
    refine ⟨⟨?zero⟩, ?exact⟩
    case zero =>
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · simp
      · exact ModuleCat.hom_ext (comp_ker_subtype u)
      · exact ModuleCat.hom_ext (range_mkQ_comp u)
      · change ModuleCat.ofHom (range u).mkQ ≫ (0 : _ ⟶ _) = 0
        simp
    case exact =>
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · apply (ShortComplex.moduleCat_exact_iff _).mpr
        intro x hx
        refine ⟨0, ?_⟩
        change 0 = x
        apply Subtype.ext
        exact hx.symm
      · apply (ShortComplex.moduleCat_exact_iff _).mpr
        intro x hx
        exact ⟨⟨x, hx⟩, rfl⟩
      · apply (ShortComplex.moduleCat_exact_iff _).mpr
        intro x hx
        exact (Submodule.Quotient.mk_eq_zero _).mp hx
      · apply (ShortComplex.moduleCat_exact_iff _).mpr
        intro x _
        exact (range u).mkQ_surjective x
  · rintro ⟨T, Q, i, p, hex, hT, hQ⟩
    have atM := (ShortComplex.moduleCat_exact_iff _).mp (hex.exact 1)
    have atN := (ShortComplex.moduleCat_exact_iff _).mp (hex.exact 2)
    change ∀ x : M, u x = 0 → ∃ y : T, i y = x at atM
    change ∀ y : N, p y = 0 → ∃ x : M, u x = y at atN
    constructor
    · intro f hf
      apply Module.mem_annihilator.mpr
      intro x
      obtain ⟨y, hy⟩ := atM (x : M) (LinearMap.mem_ker.mp x.property)
      apply Subtype.ext
      change f • (x : M) = 0
      rw [← hy, ← i.hom.map_smul, Module.mem_annihilator.mp (hT hf) y, map_zero]
    · intro f hf
      apply Module.mem_annihilator.mpr
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ y =>
        change (range u).mkQ (f • y) = 0
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        apply LinearMap.mem_range.mpr
        apply atN
        rw [p.hom.map_smul, Module.mem_annihilator.mp (hQ hf) (p y)]


/-- If for all `f, g ∈ K^t` a map `v` has a quasi-inverse `k` with both composites equal to
`f * g`, then the kernel and cokernel of `v` are killed by `K^(2t)`. -/
private theorem annihilated_of_scalar_composites
    {A : Type u} [CommRing A] (K : Ideal A) (t : ℕ)
    {P : Type z} {R : Type z'} [AddCommGroup P] [Module A P]
    [AddCommGroup R] [Module A R] (v : P →ₗ[A] R)
    (hv : ∀ (f g : A), f ∈ K ^ t → g ∈ K ^ t →
      ∃ k : R →ₗ[A] P,
        k.comp v = (f * g) • LinearMap.id ∧ v.comp k = (f * g) • LinearMap.id) :
    K ^ (2 * t) ≤ Module.annihilator A (ker v) ∧
    K ^ (2 * t) ≤ Module.annihilator A (R ⧸ range v) := by
  rw [two_mul, pow_add]
  constructor
  · refine Ideal.mul_le.mpr fun f hf g hg ↦ ?_
    obtain ⟨k, hk, _⟩ := hv f g hf hg
    apply Module.mem_annihilator.mpr
    intro x
    apply Subtype.ext
    have h := congrArg (fun l : P →ₗ[A] P ↦ l x) hk
    simpa [LinearMap.mem_ker.mp x.property] using h.symm
  · refine Ideal.mul_le.mpr fun f hf g hg ↦ ?_
    obtain ⟨k, _, hk⟩ := hv f g hf hg
    apply Module.mem_annihilator.mpr
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      change (range v).mkQ ((f * g) • y) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨k y, ?_⟩
      exact congrArg (fun l : R →ₗ[A] R ↦ l y) hk

/-- Let the kernel and cokernel of `u : M → N` be killed by `K^t`. For `f, g ∈ K^t`, every
`f • y` lifts along `u`, the element `g • x` does not depend on the lift `x`, and the resulting
map `h : N → M` satisfies `h ∘ u = fg` and `u ∘ h = fg` and is natural in `u`. Moreover the
reduced map `M/JM → N/JN` has kernel and cokernel killed by `K^(2t)` for every ideal `J`, and so
does any map admitting such quasi-inverses. -/
theorem ker_coker_annihilated_mod_ideal
    {A : Type u} [CommRing A]
    {M : Type v} {N : Type v'}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (K : Ideal A) (t : ℕ) (ht : 1 ≤ t) (u : M →ₗ[A] N)
    (hker : K ^ t ≤ Module.annihilator A (ker u))
    (hcoker : K ^ t ≤ Module.annihilator A (N ⧸ range u)) :
    (∀ (f g : A), f ∈ K ^ t → g ∈ K ^ t →
      (∀ y : N, ∃ x : M, u x = f • y) ∧
      (∀ (y : N) (x x' : M), u x = f • y → u x' = f • y → g • x = g • x') ∧
      ∃ h : N →ₗ[A] M,
        (∀ (y : N) (x : M), u x = f • y → h y = g • x) ∧
        h.comp u = (f * g) • LinearMap.id ∧
        u.comp h = (f * g) • LinearMap.id ∧
        ∀ (M' : Type w) (N' : Type w') [AddCommGroup M'] [Module A M']
          [AddCommGroup N'] [Module A N'] (u' : M' →ₗ[A] N'),
          K ^ t ≤ Module.annihilator A (ker u') →
          K ^ t ≤ Module.annihilator A (N' ⧸ range u') →
          ∀ (a : M →ₗ[A] M') (b : N →ₗ[A] N') (h' : N' →ₗ[A] M'),
            u'.comp a = b.comp u →
            (∀ (y : N') (x : M'), u' x = f • y → h' y = g • x) →
            a.comp h = h'.comp b) ∧
    (∀ J : Ideal A,
      let ū := (J • ⊤ : Submodule A M).mapQ (J • ⊤ : Submodule A N) u
        (Submodule.smul_top_le_comap_smul_top J u)
      K ^ (2 * t) ≤ Module.annihilator A (ker ū) ∧
      K ^ (2 * t) ≤ Module.annihilator A ((N ⧸ (J • ⊤ : Submodule A N)) ⧸ range ū)) ∧
    (∀ (P : Type z) (R : Type z') [AddCommGroup P] [Module A P] [AddCommGroup R] [Module A R]
      (v : P →ₗ[A] R),
      (∀ (f g : A), f ∈ K ^ t → g ∈ K ^ t →
        ∃ k : R →ₗ[A] P,
          k.comp v = (f * g) • LinearMap.id ∧ v.comp k = (f * g) • LinearMap.id) →
      K ^ (2 * t) ≤ Module.annihilator A (ker v) ∧
      K ^ (2 * t) ≤ Module.annihilator A (R ⧸ range v)) := by
  classical
  -- The scalar argument also works for t = 0; retain the stated hypothesis.
  have _ht := ht
  have maps : ∀ (f g : A), f ∈ K ^ t → g ∈ K ^ t →
      (∀ y : N, ∃ x : M, u x = f • y) ∧
      (∀ (y : N) (x x' : M), u x = f • y → u x' = f • y → g • x = g • x') ∧
      ∃ h : N →ₗ[A] M,
        (∀ (y : N) (x : M), u x = f • y → h y = g • x) ∧
        h.comp u = (f * g) • LinearMap.id ∧
        u.comp h = (f * g) • LinearMap.id ∧
        ∀ (M' : Type w) (N' : Type w') [AddCommGroup M'] [Module A M']
          [AddCommGroup N'] [Module A N'] (u' : M' →ₗ[A] N'),
          K ^ t ≤ Module.annihilator A (ker u') →
          K ^ t ≤ Module.annihilator A (N' ⧸ range u') →
          ∀ (a : M →ₗ[A] M') (b : N →ₗ[A] N') (h' : N' →ₗ[A] M'),
            u'.comp a = b.comp u →
            (∀ (y : N') (x : M'), u' x = f • y → h' y = g • x) →
            a.comp h = h'.comp b := by
    intro f g hf hg
    have lifts (y : N) : ∃ x : M, u x = f • y := by
      apply LinearMap.mem_range.mp
      apply (Submodule.Quotient.mk_eq_zero _).mp
      exact Module.mem_annihilator.mp (hcoker hf) ((range u).mkQ y)
    have independent (y : N) (x x' : M)
        (hx : u x = f • y) (hx' : u x' = f • y) : g • x = g • x' := by
      have hxker : x - x' ∈ ker u := by simp [LinearMap.mem_ker, hx, hx']
      have hz := Module.mem_annihilator.mp (hker hg) (⟨x - x', hxker⟩ : ker u)
      have hz' : g • (x - x') = 0 := congrArg Subtype.val hz
      exact sub_eq_zero.mp (by simpa [smul_sub] using hz')
    let lift (y : N) : M := Classical.choose (lifts y)
    have hlift (y : N) : u (lift y) = f • y := Classical.choose_spec (lifts y)
    have formula (y : N) (x : M) (hx : u x = f • y) :
        g • lift y = g • x := independent y (lift y) x (hlift y) hx
    let h : N →ₗ[A] M :=
      { toFun := fun y ↦ g • lift y
        map_add' := fun y y' ↦ by
          rw [formula (y + y') (lift y + lift y') (by simp [hlift, smul_add])]
          exact smul_add g (lift y) (lift y')
        map_smul' := fun c y ↦ by
          rw [formula (c • y) (c • lift y) (by simp [hlift, smul_comm f c])]
          exact smul_comm g c (lift y) }
    refine ⟨lifts, independent, h, formula, ?_, ?_, ?_⟩
    · ext x
      change g • lift (u x) = (f * g) • x
      rw [formula (u x) (f • x) (u.map_smul f x), smul_smul, mul_comm g f]
    · ext y
      change u (g • lift y) = (f * g) • y
      rw [u.map_smul, hlift, smul_smul, mul_comm g f]
    · intro M' N' _ _ _ _ u' _ _ a b h' square formula'
      ext y
      obtain ⟨x, hx⟩ := lifts y
      change a (g • lift y) = h' (b y)
      rw [formula y x hx, a.map_smul]
      symm
      apply formula'
      have hs := congrArg (fun l : M →ₗ[A] N' ↦ l x) square
      simpa [hx] using hs
  refine ⟨maps, ?_, fun P R _ _ _ _ v hv ↦ annihilated_of_scalar_composites K t v hv⟩
  intro J
  apply annihilated_of_scalar_composites K t
  intro f g hf hg
  obtain ⟨h, _, hhu, huh, _⟩ := (maps f g hf hg).2.2
  let hbar := (J • ⊤ : Submodule A N).mapQ (J • ⊤ : Submodule A M) h
    (Submodule.smul_top_le_comap_smul_top J h)
  refine ⟨hbar, ?_, ?_⟩
  · ext x
    change (J • ⊤ : Submodule A M).mkQ (h (u x)) =
      (J • ⊤ : Submodule A M).mkQ ((f * g) • x)
    exact congrArg (fun y ↦ (J • ⊤ : Submodule A M).mkQ y)
      (congrArg (fun l : M →ₗ[A] M ↦ l x) hhu)
  · ext y
    change (J • ⊤ : Submodule A N).mkQ (u (h y)) =
      (J • ⊤ : Submodule A N).mkQ ((f * g) • y)
    exact congrArg (fun x ↦ (J • ⊤ : Submodule A N).mkQ x)
      (congrArg (fun l : N →ₗ[A] N ↦ l y) huh)

end LinearMap
