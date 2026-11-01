/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarFiniteEvaluationTransport

/-! # Reindexing of constant image evaluation

Source: Stacks 0D6E, 0E8I and 0940.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluation at an arithmetic subsequence commutes with the constant proper/open
image comparison.
Source: Stacks 0D6E, 0E8I, 0940.
(blueprint: lem-pur-constant-image-reindex-evaluation).
Proof: for proper image the ordinary selection/evaluation square is the identity.
Both derived comparisons are characterized by the same right-derived unit, so
right-derived uniqueness identifies their composites. For open extension all
functors are exact and the two ordinary squares are identities; localization of
these equal squares is equal. Whisker the proper equality by the open functor,
whisker the open equality by proper image, and use naturality to compose them.
The retained index is e(n+1)-1, with no boundedness assumption. -/
theorem constantImage_reindexEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (e : ℕ) (hepos : 1 ≤ e) (n : ℕ)
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n).map
        ((reindexImage l E c e hepos).inv.app N) ≫
      (subsequenceEvaluation l E Y e n).hom.app ((image l E c).obj N) ≫
      (constantImageEvaluation l E c (e * (n + 1) - 1)).hom.app N =
      (constantImageEvaluation l E c n).hom.app ((subsequence l E X e).obj N) ≫
        (PurCompactSupport.image (constants l E) c).map
          ((subsequenceEvaluation l E X e n).hom.app N) := by sorry

end WeilConjectures.PurStrictScalar
