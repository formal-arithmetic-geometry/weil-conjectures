module

public import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] public section
universe u
namespace Algebra

/-- The quotient presentation obtained by adjoining an inverse is isomorphic to the
principal localization. The isomorphism sends each old variable to its localization
image and the new variable to `Away.invSelf`; the relation `h * Away.invSelf = 1`
makes this map factor through the quotient, and the universal property of localization
gives the inverse map. These maps are inverse by the quotient and localization
induction principles, and the formulas follow on polynomial generators. Source:
Stacks Project, Algebra, Lemma Tag 00SS, part (2).
(blueprint: new-principal-localization-alg-equiv) -/
theorem principalLocalization_algEquiv
    (R : Type u) [CommRing R] (n c : ℕ)
    (f : Fin c → MvPolynomial (Fin n) R)
    (h : MvPolynomial (Fin n) R) :
      ∃ e :
          (MvPolynomial (Fin (n + 1)) R ⧸
              Ideal.span (Set.range
                (Fin.snoc (α := fun _ ↦ MvPolynomial (Fin (n + 1)) R)
                  (fun i ↦ MvPolynomial.rename Fin.castSucc (f i))
                  (MvPolynomial.rename Fin.castSucc h * MvPolynomial.X (Fin.last n) - 1)))) ≃ₐ[R]
            Localization.Away
              (Ideal.Quotient.mk (Ideal.span (Set.range f)) h),
        (∀ i : Fin n,
          e (Ideal.Quotient.mk _ (MvPolynomial.X (Fin.castSucc i))) =
            algebraMap
              (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
              (Localization.Away
                (Ideal.Quotient.mk (Ideal.span (Set.range f)) h))
              (Ideal.Quotient.mk _ (MvPolynomial.X i))) ∧
        e (Ideal.Quotient.mk _ (MvPolynomial.X (Fin.last n))) =
          IsLocalization.Away.invSelf
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) h) := by
  sorry

end Algebra
