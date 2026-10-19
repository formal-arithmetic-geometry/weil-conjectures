/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Sheaf.Algebra.Homology.SingleSupportTorAcyclicTensor
import Sheaf.Algebra.Homology.TensorComparisonStupidTail

/-!
# Termwise Tor acyclicity computes derived tensor

Source: Stacks Project, `perfect.tex`, Tag 08IB, `lemma-compare-base-change`
(blueprint: lem-pc-termwise-tor-acyclic-derived-tensor).

The derived tensor is represented by an arbitrary K-flat resolution `f : P.obj ⟶ Q`.
The canonical comparison is represented by `f ⊗ B`, with `B` in degree zero. Applying
`tensoringRight B` termwise gives exactly this tensor complex and comparison map, as
complexes of R-modules, as in the node. The choice of resolution is universally quantified.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

namespace CochainComplex

private lemma quasiIso_tensor_of_tor_acyclic_interval
    {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]
    (d : ℕ) (Q : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (hbounded : ∀ n : ℤ, n < a ∨ a + (d : ℤ) < n → IsZero (Q.X n))
    (hTor : ∀ (n : ℤ) (i : ℕ), 0 < i →
      IsZero (((Tor' (ModuleCat.{u} R) i).obj (Q.X n)).obj (ModuleCat.of R B)))
    (P : CochainComplex.KFlat (ModuleCat.{u} R)) (f : P.obj ⟶ Q)
    (hf : QuasiIso f) :
    QuasiIso ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by
  induction d generalizing Q a P with
  | zero =>
    apply quasiIso_tensor_of_single_support_tor_acyclic Q a _ (hTor a) P f hf
    intro n hn
    apply hbounded n
    simp only [Nat.cast_zero, add_zero]
    omega
  | succ d ih =>
    let T := Q.stupidTrunc (ComplexShape.embeddingUpIntGE (a + 1))
    have hTbound : ∀ n : ℤ, n < a + 1 ∨ a + 1 + (d : ℤ) < n →
        IsZero (T.X n) := by
      intro n hn
      by_cases hlow : n < a + 1
      · exact Q.isZero_stupidTrunc_X _ n
          ((ComplexShape.notMem_range_embeddingUpIntGE_iff (a + 1) n).2 hlow)
      · obtain ⟨j, hj⟩ := Int.le.dest (show a + 1 ≤ n by omega)
        have heq : (ComplexShape.embeddingUpIntGE (a + 1)).f j = n := by
          simpa using hj
        exact (hbounded n (Or.inr (by omega))).of_iso (Q.stupidTruncXIso _ heq)
    have hTTor : ∀ (n : ℤ) (i : ℕ), 0 < i →
        IsZero (((Tor' (ModuleCat.{u} R) i).obj (T.X n)).obj (ModuleCat.of R B)) := by
      intro n i hi
      by_cases hlow : n < a + 1
      · have hz : IsZero (T.X n) := Q.isZero_stupidTrunc_X _ n
          ((ComplexShape.notMem_range_embeddingUpIntGE_iff (a + 1) n).2 hlow)
        have : Projective (T.X n) := hz.projective
        cases i with
        | zero => omega
        | succ j =>
          exact isZero_Tor'_succ_of_projective _ (T.X n) (ModuleCat.of R B) j
      · obtain ⟨j, hj⟩ := Int.le.dest (show a + 1 ≤ n by omega)
        have heq : (ComplexShape.embeddingUpIntGE (a + 1)).f j = n := by
          simpa using hj
        exact (hTor n i hi).of_iso
          (Functor.mapIso
            (((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).leftDerived i)
            (Q.stupidTruncXIso _ heq))
    apply quasiIso_tensor_of_stupid_tail Q a
      (fun n hn ↦ hbounded n (Or.inl hn)) _ _ P f hf
    · intro P' f' hf'
      apply quasiIso_tensor_of_single_support_tor_acyclic _ a _ _ P' f' hf'
      · intro n hn
        exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
      · intro i hi
        exact (hTor a i hi).of_iso
          (Functor.mapIso
            (((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).leftDerived i)
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a (Q.X a)))
    · intro P' f' hf'
      exact ih T (a + 1) hTbound hTTor P' f' hf'

/-- (blueprint: lem-pc-termwise-tor-acyclic-derived-tensor) For a bounded complex `Q`
of modules over a commutative ring `R`, if every term has vanishing positive Tor with
an `R`-algebra `B`, the canonical derived-to-ordinary tensor comparison is a
quasi-isomorphism and induces an isomorphism in every cohomological degree.
Source: Stacks Project, Tag 08IB, `lemma-compare-base-change`, the Tor-independent
comparison. The comparison is expressed on every K-flat resolution of `Q`.

Proof: Choose d = (b-a).toNat, so the support is contained in [a,a+d], also
when b<a. Induct on d, universally quantifying over the complex and its K-flat
resolution. For d=0 use the one-term calculation
(lem-pc-single-support-tor-acyclic-tensor). For a successor use the stupid tail
starting at a+1. Outside the tail its terms are zero and therefore projective,
so their positive Tor vanishes. Inside the tail its terms are isomorphic to
those of Q; apply the left-derived tensor functor to these isomorphisms to
transport the Tor hypothesis. The tail has width d and satisfies the induction
hypothesis for every resolution. The single complex on Q.X a has the one-term
comparison, after transporting Tor through its degree-a isomorphism. Apply the
truncation gluing lemma (lem-pc-tensor-comparison-stupid-tail) to these two
comparisons. The resulting quasi-isomorphism induces isomorphisms on homology
in every degree by Mathlib's QuasiIso instances. -/
theorem quasiIso_tensor_of_termwise_tor_acyclic
    {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]
    (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Q.X n))
    (hTor : ∀ (n : ℤ) (i : ℕ), 0 < i →
      IsZero (((Tor' (ModuleCat.{u} R) i).obj (Q.X n)).obj (ModuleCat.of R B)))
    (P : CochainComplex.KFlat (ModuleCat.{u} R)) (f : P.obj ⟶ Q)
    (hf : QuasiIso f) :
    QuasiIso ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) ∧
    ∀ i : ℤ, IsIso (homologyMap
      ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f) i) := by
  obtain ⟨a, b, hb⟩ := hbounded
  have hq := quasiIso_tensor_of_tor_acyclic_interval (b - a).toNat Q a
    (fun n hn ↦ hb n (by
      rcases hn with hn | hn
      · exact Or.inl hn
      · exact Or.inr (by omega))) hTor P f hf
  refine ⟨hq, ?_⟩
  intro i
  have := hq
  infer_instance

end CochainComplex
