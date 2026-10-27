/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompleteCompactificationLimitSupport

/-! # Open extension and fixed-coefficient strict limits
Source: blueprint direct-image proof, paragraph (2); Stacks 09BP.
(blueprint: lem-sp-compactification-open-limit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual constant-diagram open mate is invertible and preserves projections.

Proof. Identify the small pro-etale site of the open with the slice over its open
object. The coefficient pullback identifies the module functor openOrd with extension
by zero on that slice. It is exact and its canonical countable-product comparison is
invertible by proEtaleRingedExtensionByZero_products. Countable products of modules
are exact on both pro-etale sites. Apply exactProductFunctorStrictLimit to these
functors and the fixed-ring total derived limits. Its signed Roos comparison is induced
by the canonical product map on both summands. On strict augmentations this is the
ordinary limit comparison; transposition across const/limit identifies it with the
specified constant-diagram mate openLimit (not merely some isomorphism). The Roos
projection equation, transported by the standard exact localization composition
isomorphisms, is the displayed equality with fixedOpenEvaluation. Invertibility and
the projection identity hold on the whole unbounded category. The empty open, identity
open, zero module and constant tower cases are the same product and mate formulas.
Source: current blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction,
sk-prop-sp-integral-adjunction-direct-image.proof.md, paragraph (2);
parent node step 3; Stacks 09BP, lemma-j-shriek-limits, and 0941.
(blueprint: lem-sp-compactification-open-limit). -/
theorem compactificationOpenLimit {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] [QuasiCompact j] :
    IsIso (openLimit l E j) ∧
    ∀ (K : DerivedCategory (Fixed l E X)) (n : ℕ),
      (openLimit l E j).app K ≫
          (coefficientConstantTowerProjection l E Z n).app
            (((fixedOpenOrd l E j).mapDerivedCategory).obj K) =
        (openOrd l E j).mapDerivedCategory.map
          ((coefficientConstantTowerProjection l E X n).app K) ≫
            (fixedOpenEvaluation l E j n).inv.app K := by sorry

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
