/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AdicSites.Morphism.CompletionMateComparison
import WeilConjectures.CategoryTheory.AdicSites.PerfectReductionProjectionEvaluation
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Perfect coefficients in the strict reduction projection

Source: Stacks Project, Cohomology on Sites, Tag 0944.
(blueprint: lem-pur-perfect-strict-reduction-projection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace CategoryTheory.AdicSites

variable {Y X : Site.{u}} (f : Morphism Y X) (A : Type u) [CommRing A] (I : Ideal A)

/-- The strict counit projection for perfect positive coefficient quotients is invertible.

Source: Stacks Project, sites-cohomology.tex, Tag 0944, lemma-projection-formula,
and equation 0B56, with Tags 0940 and 0941 for strict coefficient systems
(blueprint: lem-pur-perfect-strict-reduction-projection).

Proof:
1. For each n choose a bounded finite-projective A-complex representing A/I^(n+1).
Each term is a retract of a finite free module: finite generation gives a finite free
surjection, and projectivity splits it. Exact constant module realization preserves the
splitting and the quasi-isomorphism. Thus the constant quotient coefficient on the site
is perfect, with no uniform bound on n required.
2. The normalized reduction/pullback comparison on a flat-term K-flat representative
identifies evaluation of towerProjection with the ordinary counit projection for this
constant coefficient, with the specified evaluation/direct-image comparison at the
target. Apply the ringed-site perfect projection formula to make this evaluation an
isomorphism, for an arbitrary unbounded derived input.
3. Exact evaluation commutes with derived cohomology. The cohomology of towerProjection
is therefore an isomorphism at every tower level. Ordinary strict tower morphisms are
isomorphisms componentwise. The unbounded derived cohomology criterion now proves that
towerProjection itself is an isomorphism. This includes zero quotients, the zero input
and empty sites; it does not assert faithfulness of derived evaluation. -/
theorem perfectStrictReductionProjection [IsNoetherianRing A]
    (hperfect : PerfectQuotients A I) (F : X.derived A) :
    IsIso (f.towerProjection A I F) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  have h (n : ℕ) : IsIso
      (((CategoryTheory.evaluation ℕᵒᵖ (Y.modules A)).obj (op n)).map
        ((DerivedCategory.homologyFunctor (Y.towers A) q).map
          (f.towerProjection A I F))) := by
    have he := perfectReductionProjectionEvaluation f A I n (hperfect n) F
    have hi : IsIso ((DerivedCategory.homologyFunctor (Y.modules A) q).map
        ((Y.evaluate A n).map (f.towerProjection A I F))) := inferInstance
    exact (NatIso.isIso_map_iff
      ((Y.evaluateModule A n).mapDerivedCategoryHomologyFunctorIso q)
      (f.towerProjection A I F)).2 hi
  have hlevel (n : ℕᵒᵖ) : IsIso
      (((DerivedCategory.homologyFunctor (Y.towers A) q).map
        (f.towerProjection A I F)).app n) := h n.unop
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun n ↦ hlevel n)

end CategoryTheory.AdicSites
