module

public import Sheaf.Paper.StrictScalarMateEvaluationData

import Sheaf.Paper.GeometricScalarFiniteEvaluation
import Sheaf.Paper.RamifiedImageBalancingEvaluation

/-! # Finite evaluation of the strict compact-support scalar mate

Source: Stacks 07A6, 0B56, 0940, 0E8I; Step 7 of the strict scalar mate argument.
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
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Evaluation of the specified strict scalar arrow is the finite proper/open arrow.
Source: Stacks 07A6 (lemma-adjoint), 0B56 (equation-projection-formula-map),
0940 (section-derived-limits), 0E8I (lemma-j-shriek-and-tensor); Step 7 of
lem-pur-compact-support-strict-scalar-mate.
(blueprint: lem-pur-strict-scalar-mate-finite-evaluation).
Proof: compute on a simultaneous diagram resolution, using the normalized tower
proper evaluation and the singleton system evaluation/restriction comparisons.
Their counit equations identify evaluation of the proper scalar mate with the
finite scalar mate: transpose both under the finite geometric adjunction, use
its normalized counit, and apply injectivity of the adjunction bijection. The
open comparison is exact localization of ordinary extension-by-zero balancing;
its normalized unit identifies its evaluation with the finite open comparison.
The reduction balancing is computed on whole K-flat diagram representatives.
On a pure tensor both ways send the coefficient to its ramified quotient;
finiteOrdinaryBalancing and finiteBalancing have exactly this normalization.
Compose these three equations in the order defining arrow. Naturality cancels
the intermediate supportModel and reindexImage identifications. The remaining
endpoint factors are precisely sourceEvaluation and targetEvaluation, and the
two surviving finite maps are properComparison followed by direct image of
openComparison, which defines finiteTensorMap. Localization extends the equality
from the resolving representatives to every derived input. This argument needs
neither boundedness nor constructibility, and makes no claim that evaluations
detect equality of maps in the derived category of strict diagrams. -/
theorem strictScalarMate_finiteEvaluation
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    ∀ n : ℕ,
        (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y n).map
            ((arrow l E F i c S S' e he hepos).app M) ≫
            (targetEvaluation l E F i c S' e he hepos n).hom.app M =
          (sourceEvaluation l E F i c S e he hepos n).hom.app M ≫
            (positiveRestriction l F Y (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n))).map
              (PurCompactSupport.finiteTensorMap l E F i e he hepos n c M) := by
  intro n
  let V := ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y n
  let a := (T l E F i Y).map ((supportModel l E c S).hom.app M) ≫
    (comparison l E F i c).app ((reduction l E X S).obj M)
  let b := (ramifiedImageBalancing l E F i c S S' e he hepos).hom.app M
  have hab : (arrow l E F i c S S' e he hepos).app M = a ≫ b := by
    simp only [arrow, a, b, ramifiedImageBalancing, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
      Category.assoc]
  have hb : V.map b ≫ (targetEvaluation l E F i c S' e he hepos n).hom.app M =
      (scalarImageEvaluation l E F i c S e he hepos n).hom.app M :=
    ramifiedImageBalancing_finiteEvaluation l E F i c S S' e he hepos M n
  have ha := geometricScalar_finiteEvaluation l E F i c S e he hepos M n
  rw [hab, Functor.map_comp, Category.assoc, hb]
  exact ha

end WeilConjectures.PurStrictScalar
