module

public import Sheaf.RingTheory.StrictlyStandardElement
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Sheaf.LinearAlgebra.Matrix.LeftInverseMinors

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra.Presentation

/-- The two strictly standard conditions split the localized conormal differential.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma Tag 07CA, first paragraph,
using the matrix identity of Lemma Tag 07ET.
(blueprint: lem-weil-pbc-strictly-standard-localized-conormal-split).

Proof: let E be the map from A^c to I/I² sending each basis vector to the class of the
corresponding initial relation, and D the conormal differential. In the polynomial
cotangent-space basis, D E has the evaluated Jacobian matrix M. The displayed minor
combination and the adjugate identity give a matrix B with B M = a times the identity;
transposing the row convention of the displayed determinants does not change them.
After scalar extension to A_a, a is a unit, so a⁻¹ B is a left inverse of D E.
The relation condition says that a times every remaining relation class lies in the
span of the initial classes, since I² vanishes in I/I². Thus E becomes surjective after
localization: all relation classes generate I/I² and the remaining ones are now in
its image. The left inverse of D E also makes E injective. Consequently E is an
isomorphism after localization. Composing its inverse, the left inverse of D E, and E
in the appropriate order gives a left inverse of D itself: explicitly E a⁻¹ B.
For c = 0 the relation condition makes the localized conormal module zero, so its
unique map back is a left inverse. The same argument covers the zero localization. -/
theorem strictlyStandard_localized_conormal_split
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {n m c : ℕ} (P : Presentation R A (Fin n) (Fin m))
    (hc : c ≤ min n m) (a : A)
    (a' : {s : Finset (Fin n) // s.card = c} → A)
    (hminor : a = ∑ s : {s : Finset (Fin n) // s.card = c}, a' s *
      Matrix.det (fun j i : Fin c =>
        MvPolynomial.aeval P.val (MvPolynomial.pderiv (s.val.orderEmbOfFin s.property i)
          (P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j)))))
    (hrelations : ∀ j : Fin m, c ≤ j.val →
      P.σ a * P.relation j ∈
        Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = P.relation k} +
          (Ideal.span (Set.range P.relation)) ^ 2) :
    ∃ l : (Localization.Away a ⊗[A] P.toExtension.CotangentSpace) →ₗ[Localization.Away a]
        (Localization.Away a ⊗[A] P.toExtension.Cotangent),
      l.comp (P.toExtension.cotangentComplex.baseChange (Localization.Away a)) =
        LinearMap.id := by
  sorry

end Algebra.Presentation
