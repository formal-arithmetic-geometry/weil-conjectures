/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Models of finitely presented algebras over a union of subfields

A finitely presented algebra over a field `k` that is a directed union of subfields `K i` is the
scalar extension of an algebra over some `K i`.

## Implementation details

The finitely many coefficients of a presentation `k[X₁, …, Xₙ] / (f₁, …, fₘ)` lie in a single
`K i`; the model is the quotient of `(K i)[X₁, …, Xₙ]` by the lifted relations.

## References

* [Stacks Project, Tag 07QG](https://stacks.math.columbia.edu/tag/07QG)
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- A finitely presented algebra over a directed union of subfields is a scalar
extension of an algebra over one member of the family. -/
theorem exists_subfield_model
    (k : Type u) [Field k] (I : Type v) [Nonempty I] (K : I → Subfield k)
    (hdir : ∀ i j : I, ∃ l : I, K i ≤ K l ∧ K j ≤ K l)
    (hUnion : ∀ x : k, ∃ i : I, x ∈ K i)
    (E : Type w) [CommRing E] [Algebra k E] [FinitePresentation k E] :
    ∃ (i : I) (B : Type (max u w)) (_ : CommRing B) (_ : Algebra (K i) B),
      Nonempty (TensorProduct (K i) k B ≃ₐ[k] E) := by
  classical
  obtain ⟨n, J, e, hJ⟩ := Algebra.FinitePresentation.iff.mp
    (inferInstance : Algebra.FinitePresentation k E)
  obtain ⟨s, hs⟩ := hJ
  have hfinite : ∀ t : Finset k, ∃ i : I, ∀ c ∈ t, c ∈ K i := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨Classical.arbitrary I, by simp⟩
    | @insert c t hc ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨j, hj⟩ := hUnion c
      obtain ⟨l, hil, hjl⟩ := hdir i j
      refine ⟨l, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hjl hj
      · exact hil (hi x hx)
  obtain ⟨i, hi⟩ := hfinite (s.biUnion MvPolynomial.coeffs)
  have hlift : ∀ p : s, ∃ q : MvPolynomial (Fin n) (K i),
      MvPolynomial.map (algebraMap (K i) k) q = p.1 := by
    intro p
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    exact ⟨⟨c, hi c (Finset.mem_biUnion.mpr ⟨p.1, p.2, hc⟩)⟩, rfl⟩
  choose f hf using hlift
  let J₀ : Ideal (MvPolynomial (Fin n) (K i)) := Ideal.span (Set.range f)
  let Q := MvPolynomial (Fin n) (K i) ⧸ J₀
  let B := ULift.{w} Q
  refine ⟨i, B, inferInstance, inferInstance, ?_⟩
  let ep := MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) (K i) k
  have hmap : J = (J₀.map (Algebra.TensorProduct.includeRight
      (A := k) (R := K i))).map ep.toRingHom := by
    change J = (J₀.map (Algebra.TensorProduct.includeRight
      (A := k) (R := K i)).toRingHom).map ep.toRingHom
    rw [Ideal.map_map]
    simp only [J₀, Ideal.map_span]
    have himage : (ep.toRingHom.comp (Algebra.TensorProduct.includeRight
        (A := k) (R := K i)).toRingHom) '' Set.range f = (s : Set _) := by
      ext p
      constructor
      · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
        simp [ep, Algebra.TensorProduct.includeRight_apply, hf]
      · intro hp
        refine ⟨f ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, ?_⟩
        simpa [ep, Algebra.TensorProduct.includeRight_apply] using hf ⟨p, hp⟩
    rw [himage, hs]
  refine ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k)
      (ULift.algEquiv (R := K i) (A := Q))).trans
    ((Algebra.TensorProduct.tensorQuotientEquiv k _ k J₀).trans
      ((Ideal.quotientEquivAlg _ J ep hmap).trans e))⟩

end Algebra
