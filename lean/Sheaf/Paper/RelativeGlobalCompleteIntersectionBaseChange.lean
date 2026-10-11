import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation

/-!
# Base change of a relative global complete intersection

Source: Stacks Project, Algebra, Lemma Tag 00SS, part (1)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-base-change).
-/

universe u v

open scoped TensorProduct
namespace Algebra

/-- Let `R → R'` be a ring map and `f₁, …, f_c ∈ R[x₁, …, xₙ]`, with images `f'ᵢ` in
`R'[x₁, …, xₙ]`. (a) The `R'`-algebra map `R'[x]/(f') → R' ⊗_R R[x]/(f)` with
`xⱼ ↦ 1 ⊗ xⱼ` is an isomorphism; (b) if `R[x]/(f)` is a relative global complete
intersection over `R`, so is `R'[x]/(f')` over `R'`.
Proof: (a) both sides corepresent the same functor on `R'`-algebras (tuples in the zero
locus of the `f'ᵢ`), by right exactness of the tensor product. (b) By (a), the fibre ring of
`R'[x]/(f')` at a prime `𝔮` of `R'` lying over `𝔭` is `κ(𝔮) ⊗_{κ(𝔭)}` the fibre ring of
`R[x]/(f)` at `𝔭`; it is nonzero exactly when the latter is, and its dimension is the same
because dimension of finite type algebras over a field is preserved under field extension
(Tag 00P3).
Source: Stacks Project, Algebra, Lemma Tag 00SS, part (1)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-base-change).
-/
theorem relativeGlobalCompleteIntersection_baseChange
    (R : Type u) (R' : Type v) [CommRing R] [CommRing R'] [Algebra R R']
    (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R) :
    (∃ e :
        (MvPolynomial (Fin n) R' ⧸
            Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap R R') (f i))))
          ≃ₐ[R']
          (R' ⊗[R] (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))),
      ∀ j : Fin n,
        e (Ideal.Quotient.mk (Ideal.span (Set.range
          (fun i => MvPolynomial.map (algebraMap R R') (f i)))) (MvPolynomial.X j)) =
          (1 : R') ⊗ₜ[R] (Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.X j))) ∧
      (IsRelativeGlobalCompleteIntersectionPresentation f →
        IsRelativeGlobalCompleteIntersectionPresentation
          (fun i => MvPolynomial.map (algebraMap R R') (f i))) := by
  sorry

end Algebra
