/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Sheaf.Algebra.Module.LocalizedHomogeneousPiece
import Mathlib.Tactic.Ring

/-! # Splitting the inclusion of a homogeneous localized piece

Source: the graded fraction argument of Stacks Tag 01N2, using Tag 07JZ.
(blueprint: lem-sfb-homogeneous-localization-retraction)
-/

@[expose] public section

universe u w t

namespace LocalizedModule

section Projection

variable {R A M : Type*} [CommRing R] [CommRing A] [AddCommGroup M]
  [Algebra R A] [Module R M] [Module A M] [IsScalarTower R A M]
  (𝓜 : ℤ → Submodule R M) [DirectSum.Decomposition 𝓜]

private noncomputable def degreeProjection (i : ℤ) : M →ₗ[R] M :=
  (𝓜 i).subtype.comp ((DirectSum.component R ℤ (fun i ↦ 𝓜 i) i).comp
    (DirectSum.decomposeLinearEquiv 𝓜).toLinearMap)

private theorem degreeProjection_same (i : ℤ) (x : M) (hx : x ∈ 𝓜 i) :
    degreeProjection 𝓜 i x = x := by
  change (DirectSum.decompose 𝓜 x i : M) = x
  exact DirectSum.decompose_of_mem_same 𝓜 hx

private theorem degreeProjection_ne (i k : ℤ) (x : M) (hx : x ∈ 𝓜 k) (hki : k ≠ i) :
    degreeProjection 𝓜 i x = 0 := by
  change (DirectSum.decompose 𝓜 x i : M) = 0
  exact DirectSum.decompose_of_mem_ne 𝓜 hx hki

private theorem degreeProjection_shift (f : A) (d : ℤ)
    (hshift : ∀ i x, x ∈ 𝓜 i → f • x ∈ 𝓜 (d + i)) (i : ℤ) (x : M) :
    degreeProjection 𝓜 (i + d) (f • x) = f • degreeProjection 𝓜 i x := by
  let μ : M →ₗ[R] M := Algebra.lsmul R R M f
  have h : (degreeProjection 𝓜 (i + d)).comp μ = μ.comp (degreeProjection 𝓜 i) := by
    apply DirectSum.decompose_lhom_ext 𝓜
    intro k
    ext x
    change degreeProjection 𝓜 (i + d) (f • (x : M)) = f • degreeProjection 𝓜 i x
    by_cases hki : k = i
    · subst k
      rw [degreeProjection_same 𝓜 i x x.property]
      apply degreeProjection_same 𝓜 (i + d)
      simpa only [add_comm i d] using hshift i x x.property
    · rw [degreeProjection_ne 𝓜 i k x x.property hki,
        degreeProjection_ne 𝓜 (i + d) (d + k) (f • (x : M))
          (hshift k x x.property) (by
            intro h
            apply hki
            exact add_right_cancel (by simpa only [add_comm d k] using h)), smul_zero]
  exact LinearMap.congr_fun h x

private theorem degreeProjection_pow (f : A) (d : ℤ)
    (hshift : ∀ i x, x ∈ 𝓜 i → f • x ∈ 𝓜 (d + i)) (n : ℕ) (i : ℤ) (x : M) :
    degreeProjection 𝓜 (i + (n : ℤ) * d) (f ^ n • x) =
      f ^ n • degreeProjection 𝓜 i x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi : i + ((n + 1 : ℕ) : ℤ) * d = (i + (n : ℤ) * d) + d := by
      push_cast
      ring
    simp only [hi, pow_succ', mul_smul, degreeProjection_shift 𝓜 f d hshift, ih]

end Projection

/-- Every homogeneous localized piece is a direct summand over the coefficient ring.

Source: Stacks, constructions.tex, Tag 01N2, standard-open calculation, with the
agent-supplied graded module refinement of
`lem-sfb-graded-module-localization-scalar-extension`, and algebra.tex, Tag 07JZ.
(blueprint: lem-sfb-homogeneous-localization-retraction)

Proof: Let π_i : M → M_i be the projections of the internal direct sum. On x/f^m
set p_j(x/f^m) = π_(j+md)(x)/f^m. Multiplication by f^n shifts all degrees by nd,
so π_(i+nd)(f^n x) = f^n π_i(x). To prove this identity, decompose x into its
finite sum of homogeneous components and apply the grading compatibility to each;
translation of integer indices is injective. If x/f^m = y/f^n, choose k with
f^(k+n)x = f^(k+m)y. Project this equality to degree j+(k+m+n)d and use the
identity to show the proposed images have equal fractions. Thus p_j is well-defined.
A common denominator proves additivity; coefficient linearity follows from that
of every π_i. The values belong to H by its carrier equality. Finally π_(j+md)
fixes a numerator in M_(j+md), so p_j fixes every fraction in H. This uses no
cancellation, boundedness, or assumption that f is regular. -/
theorem exists_homogeneousPieceAway_retraction
    {R : Type u} {A : Type w} {M : Type t}
    [CommRing R] [CommRing A] [AddCommGroup M]
    [Algebra R A] [Module R M] [Module A M] [IsScalarTower R A M]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule R M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (i : ℤ) (a : A) (x : M),
      a ∈ 𝒜 n → x ∈ 𝓜 i → a • x ∈ 𝓜 ((n : ℤ) + i))
    {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) (j : ℤ)
    (H : Submodule R (LocalizedModule.Away f M))
    (hH : (H : Set (LocalizedModule.Away f M)) =
      homogeneousPieceAway (fun i ↦ (𝓜 i).toAddSubgroup) f (d : ℤ) j) :
    ∃ p : LocalizedModule.Away f M →ₗ[R] H, p.comp H.subtype = LinearMap.id := by
  classical
  let : DirectSum.Decomposition 𝓜 := h𝓜.chooseDecomposition
  have hshift : ∀ i x, x ∈ 𝓜 i → f • x ∈ 𝓜 ((d : ℤ) + i) :=
    fun i x hx ↦ hsmul d i f x hf hx
  let q (x : M) (m : ℕ) : LocalizedModule.Away f M :=
    mk (degreeProjection 𝓜 (j + (m : ℤ) * (d : ℤ)) x)
      (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)
  have hqrel (x y : M) (m n : ℕ)
      (h : mk x (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) =
        mk y (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f)) : q x m = q y n := by
    obtain ⟨s, hs⟩ := mk_eq.mp h
    obtain ⟨k, hk⟩ := s.property
    change (s : A) • f ^ n • x = (s : A) • f ^ m • y at hs
    rw [← hk, ← mul_smul, ← mul_smul, ← pow_add, ← pow_add] at hs
    have heq := congrArg (degreeProjection 𝓜 (j + ((k + m + n : ℕ) : ℤ) * (d : ℤ))) hs
    have hleft : j + ((k + m + n : ℕ) : ℤ) * (d : ℤ) =
        (j + (m : ℤ) * (d : ℤ)) + ((k + n : ℕ) : ℤ) * (d : ℤ) := by
      push_cast
      ring
    have hright : j + ((k + m + n : ℕ) : ℤ) * (d : ℤ) =
        (j + (n : ℤ) * (d : ℤ)) + ((k + m : ℕ) : ℤ) * (d : ℤ) := by
      push_cast
      ring
    have hleft' := degreeProjection_pow 𝓜 f (d : ℤ) hshift (k + n)
      (j + (m : ℤ) * (d : ℤ)) x
    have hright' := degreeProjection_pow 𝓜 f (d : ℤ) hshift (k + m)
      (j + (n : ℤ) * (d : ℤ)) y
    rw [← hleft] at hleft'
    rw [← hright] at hright'
    rw [hleft', hright'] at heq
    apply mk_eq.mpr
    refine ⟨⟨f ^ k, ⟨k, rfl⟩⟩, ?_⟩
    change f ^ k • f ^ n • degreeProjection 𝓜 (j + (m : ℤ) * (d : ℤ)) x =
      f ^ k • f ^ m • degreeProjection 𝓜 (j + (n : ℤ) * (d : ℤ)) y
    simpa only [← mul_smul, ← pow_add] using heq
  let exponent (s : Submonoid.powers f) : ℕ := Classical.choose s.property
  have hexponent (s : Submonoid.powers f) : f ^ exponent s = (s : A) :=
    Classical.choose_spec s.property
  let praw (z : LocalizedModule.Away f M) : LocalizedModule.Away f M :=
    z.liftOn (fun a ↦ q a.1 (exponent a.2)) (by
      rintro ⟨x, s⟩ ⟨y, t⟩ h
      apply hqrel
      have hs : (⟨f ^ exponent s, ⟨exponent s, rfl⟩⟩ : Submonoid.powers f) = s :=
        Subtype.ext (hexponent s)
      have ht : (⟨f ^ exponent t, ⟨exponent t, rfl⟩⟩ : Submonoid.powers f) = t :=
        Subtype.ext (hexponent t)
      rw [hs, ht]
      exact mk_eq.mpr h)
  have hpraw (x : M) (m : ℕ) :
      praw (mk x (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) = q x m := by
    dsimp only [praw]
    rw [liftOn_mk]
    apply hqrel
    congr 1
    exact Subtype.ext (hexponent _)
  have hmem (z : LocalizedModule.Away f M) : praw z ∈ H := by
    induction z using LocalizedModule.induction_on with
    | h x s =>
      obtain ⟨m, hm⟩ := s.property
      have hs : s = (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext hm.symm
      subst s
      rw [hpraw]
      change q x m ∈ (H : Set (LocalizedModule.Away f M))
      rw [hH]
      refine ⟨m, degreeProjection 𝓜 (j + (m : ℤ) * (d : ℤ)) x, ?_, rfl⟩
      exact (DirectSum.decompose 𝓜 x (j + (m : ℤ) * (d : ℤ))).property
  have hadd (x y : LocalizedModule.Away f M) : praw (x + y) = praw x + praw y := by
    induction x, y using LocalizedModule.induction_on₂ with
    | h x y s t =>
      obtain ⟨m, hm⟩ := s.property
      obtain ⟨n, hn⟩ := t.property
      have hs : s = (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext hm.symm
      have ht : t = (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext hn.symm
      subst s
      subst t
      have hden : (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) *
          ⟨f ^ n, ⟨n, rfl⟩⟩ = ⟨f ^ (m + n), ⟨m + n, rfl⟩⟩ :=
        Subtype.ext (pow_add f m n).symm
      rw [mk_add_mk, hden, hpraw, hpraw, hpraw]
      have hl : j + ((m + n : ℕ) : ℤ) * (d : ℤ) =
          (j + (m : ℤ) * (d : ℤ)) + (n : ℤ) * (d : ℤ) := by
        push_cast
        ring
      have hr : j + ((m + n : ℕ) : ℤ) * (d : ℤ) =
          (j + (n : ℤ) * (d : ℤ)) + (m : ℤ) * (d : ℤ) := by
        push_cast
        ring
      have hl' := degreeProjection_pow 𝓜 f (d : ℤ) hshift n
        (j + (m : ℤ) * (d : ℤ)) x
      have hr' := degreeProjection_pow 𝓜 f (d : ℤ) hshift m
        (j + (n : ℤ) * (d : ℤ)) y
      rw [← hl] at hl'
      rw [← hr] at hr'
      dsimp only [q]
      change mk (degreeProjection 𝓜 _ (f ^ n • x + f ^ m • y)) _ = _
      rw [map_add, hl', hr', mk_add_mk]
      congr 1
      exact hden.symm
  have hscalar (r : R) (z : LocalizedModule.Away f M) : praw (r • z) = r • praw z := by
    induction z using LocalizedModule.induction_on with
    | h x s =>
      obtain ⟨m, hm⟩ := s.property
      have hs : s = (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext hm.symm
      subst s
      rw [smul'_mk, hpraw, hpraw]
      dsimp only [q]
      rw [map_smul, smul'_mk]
  let p : LocalizedModule.Away f M →ₗ[R] H :=
    { toFun := fun z ↦ ⟨praw z, hmem z⟩
      map_add' := fun x y ↦ Subtype.ext (hadd x y)
      map_smul' := fun r z ↦ Subtype.ext (hscalar r z) }
  refine ⟨p, ?_⟩
  ext z
  have hz : (z : LocalizedModule.Away f M) ∈
      homogeneousPieceAway (fun i ↦ (𝓜 i).toAddSubgroup) f (d : ℤ) j := by
    rw [← hH]
    exact z.property
  obtain ⟨m, x, hx, hz⟩ := hz
  change praw (z : LocalizedModule.Away f M) = (z : LocalizedModule.Away f M)
  rw [← hz, hpraw]
  change mk (degreeProjection 𝓜 (j + (m : ℤ) * (d : ℤ)) x) _ = _
  rw [degreeProjection_same 𝓜 _ x hx]

end LocalizedModule
