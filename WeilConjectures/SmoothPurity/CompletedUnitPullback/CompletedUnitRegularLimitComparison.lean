/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRegularSequenceNormalized
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRegularSequenceLimit
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients

/-! # The regular completed unit and its coefficient-system limit comparison

Source: Bhatt--Scholze, Sections 3.5 and 6.5, Lemma 6.8.2(1), together with
the normalized coefficient-system evaluation calculus.

The theorem records the geometric part of the strict comparison separately from
the adjunction transport.  Its proof constructs the compatible finite quotient
maps from the normalized strict scalar unit, assembles them into the derived
coefficient-system limit, and proves the Roos completeness and normalization
properties of the regular completed object.
(blueprint: lem-pur-completed-unit-regular-limit-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback

universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The pulled-back condensed integer ring is the limit of its finite constant
quotient rings, with its specified reductions and a unique normalized comparison.

Source: latest blueprint, `sk-prop-sfb-qlbar-colimit-x`, first display.
Proof: the integral condensed comparison supplies a limiting cone and natural finite
constant identifications. Their transition equations give an isomorphism of the
quotient diagrams. Postcompose the limiting cone with that isomorphism. Its legs
are the old legs followed by the finite identifications, so associativity gives
the prescribed reduction equations. Limit extensionality makes any two normalized
comparisons equal. This works for the empty scheme and starts at positive exponent one.
(blueprint: lem-pur-completed-unit-regular-limit-comparison). -/
theorem regularLimitComparisonData (W : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) :
    ∃ k : ∀ n : ℕ, completedCoefficient W
        (Profinite.continuousMapRingSheaf (completedResidue l E π n)) ≅
          completedConstantRing W (completedResidue l E π n),
      (∀ n, completedCoefficientMap W (completedResidueTransition l E π n) ≫ (k n).hom =
        (k (n + 1)).hom ≫ completedConstantMap W
          (Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_succ (n + 1)))) ∧
      ∃ (c : Cone (Functor.ofOpSequence
          (X := fun n ↦ completedConstantRing W (completedResidue l E π n))
          (fun n ↦ completedConstantMap W
            (Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_succ (n + 1))))))
        (e : completedCoefficient W (Profinite.padicIntegersCondensedRing l E) ≅ c.pt),
        Nonempty (IsLimit c) ∧
        (∀ n, e.hom ≫ c.π.app (op n) =
          completedCoefficientMap W (completedReduction l E π n) ≫ (k n).hom) ∧
        ∀ e' : completedCoefficient W (Profinite.padicIntegersCondensedRing l E) ≅ c.pt,
          (∀ n, e'.hom ≫ c.π.app (op n) =
            completedCoefficientMap W (completedReduction l E π n) ≫ (k n).hom) → e' = e := by
  obtain ⟨⟨c, e, he, ⟨hc⟩⟩, _, k, hk⟩ := completedCondensedIntegral W l E π hπ
  let F := Functor.ofOpSequence
    (X := fun n ↦ completedCoefficient W
      (Profinite.continuousMapRingSheaf (completedResidue l E π n)))
    (fun n ↦ completedCoefficientMap W (completedResidueTransition l E π n))
  let G := Functor.ofOpSequence
    (X := fun n ↦ completedConstantRing W (completedResidue l E π n))
    (fun n ↦ completedConstantMap W
      (Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_succ (n + 1))))
  let β : F ⟶ G := NatTrans.ofOpSequence (fun n ↦ (k n).hom) (fun n ↦ by
    simpa only [F, G, Functor.ofOpSequence_map_homOfLE_succ] using hk n)
  have hβ : ∀ n, IsIso (β.app n) := fun n ↦ by
    change IsIso ((k n.unop).hom)
    infer_instance
  have : IsIso β := NatIso.isIso_of_isIso_app β
  let c' := (Cone.postcompose β).obj c
  have hc' : IsLimit c' := (IsLimit.postcomposeHomEquiv (asIso β) c).symm hc
  have hnorm (n : ℕ) : e.hom ≫ c'.π.app (op n) =
      completedCoefficientMap W (completedReduction l E π n) ≫ (k n).hom := by
    change e.hom ≫ (c.π.app (op n) ≫ (k n).hom) = _
    rw [← Category.assoc, he n]
  refine ⟨k, hk, c', e, ⟨hc'⟩, hnorm, ?_⟩
  intro e' he'
  apply Iso.ext
  apply hc'.hom_ext
  intro n
  exact (he' n.unop).trans (hnorm n.unop).symm

end WeilConjectures.CompletedUnitPullback
