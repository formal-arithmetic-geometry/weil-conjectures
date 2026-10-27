/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Paper.SixFunctorDualNotation
public import Sheaf.Paper.SitePerfectComplex
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import Sheaf.Algebra.Homology.RationalTermHomComparison
import WeilConjectures.Algebra.Homology.StupidTailHomShortExact
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.ScalarExtensionExactIntrinsic
import Sheaf.Paper.BasicOperationsCoefficientReduction

/-!
# Perfect coefficient duals and their evaluation

Source: Weil conjectures blueprint, main-20261015, sec-six-functors,
sk-prop-sf-dualizable-biduality/prop-sf-dualizable; Stacks Project, Tags 08JI and 08JJ
(blueprint: prop-sf-dualizable).

The four clauses use the finite, completed integral, scalar-localized rational and
common-stage categories of the given six-functor datum. Evaluation is constructed
from its specified tensor-Hom adjunction, independently of any local perfect model.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

/-- The actual evaluation in the order K tensor K dual is symmetry followed by
counit evaluation at the coefficient unit. In particular it is not an arbitrary
arrow or a choice of a locally constructed map.
Source: blueprint prop-sf-dualizable, last sentence and proof step 11
(blueprint: prop-sf-dualizable). -/
def sixFunctorCoefficientEvaluation {B : Type a} [Category.{b} B]
    {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)}
    {H : Q.FullSubcategory ⥤ B} (M : SixFunctorClosedDomain P Q H)
    (K : P.FullSubcategory) :
    M.closed.tensor.obj (K, (sixFunctorCoefficientDual M).obj (op K)) ⟶
      M.closed.monoidal.tensorUnit :=
  (M.symmetric.braiding K ((sixFunctorCoefficientDual M).obj (op K))).hom ≫
    M.closed.evaluation K M.closed.monoidal.tensorUnit

/-- The coefficient dual of a site-perfect finite-Tor constructible complex is
site-perfect, at each of the four coefficient stages. The associated evaluation
is `sixFunctorCoefficientEvaluation` applied to that stage's closed domain.
Source: blueprint prop-sf-dualizable; Stacks Project Tags 08JI and 08JJ
(blueprint: prop-sf-dualizable).

Proof, following all eleven steps of the node:
1. At finite and integral coefficients restrict to a covering slice with a bounded
finite-projective representative P. Exact restriction and Hom restriction are
lem-pur-site-restriction-module-adjunction-exact and
lem-weil-pbc-ringed-internal-hom-exact-restriction. Refine the finitely many term
covers to exhibit separate termwise retractions from finite free modules.
2. Precomposition with those retractions makes Hom(P^r,R) a finite free summand,
and Hom(P^r,-) a retract of an exact finite-sum functor. This is exact on every
slice, including rank zero, by splitting the idempotent and its complement.
3. Choose a K-injective resolution R[0] to I. The bounded exact-term Hom criterion
lem-pc-bounded-exact-term-hom-quasi-iso identifies Hom(P,R[0]) with Hom(P,I).
The first complex has terms Hom(P^{-j},R), differential (-1)^{j+1} phi d_P,
and support [-b,-a]. These are the required finite and integral local dual models.
4. At rational coefficients use the actual localized term retractions. Exact
scalar localization and ringed-site Hom restriction give local exact Hom. Hom of
the unit is the unit, and applying Hom to a retraction preserves its splitting.
5. Apply lem-sf-rational-term-hom-comparison to the completed coefficient sheaf:
the comparison Hom(F,R)[0] to Hom(F[0],I) is an isomorphism after localization,
and its source is a rational finite-free summand. Splittings need not lift.
6. Form D = Hom(P,R[0]), bounded in [-b,-a], with the signed differential above.
Its terms have the rational retractions from step 5. Postcomposition with R[0]
to I gives the actual comparison c_P to Hom(P,I).
7. The degreewise split stupid-tail sequence, by
lem-pc-stupid-tail-hom-short-exact, gives a morphism of Hom short exact sequences.
lem-weil-pbc-complex-ses-triangle supplies the connecting square as well.
8. Exact scalar localization takes this to a morphism of distinguished triangles.
The quotient comparison is the shift of the term comparison; the signed shift
isomorphism multiplies degree q by (-1)^{rq} and commutes with postcomposition.
9. Start with the zero tail above b and induct downward to a. The quotient and
next-tail comparisons are invertible, so lem-sf-triangle-morphism-iso makes the
middle one invertible. Thus D is the rational dual's bounded local model.
10. At algebraically closed coefficients descend to a perfect finite-field
representative. Its rational dual is perfect by steps 4--9. Exact scalar
extension preserves the finite cone construction, sums and retractions;
lem-fix-operation-reduction identifies the extended Hom and coefficient unit.
11. The counit at the coefficient unit, preceded by symmetry for the displayed
factor order, constructs sixFunctorCoefficientEvaluation globally. It requires
neither a choice of local models nor gluing local evaluation maps. -/
theorem sixFunctor_sitePerfect_dual
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ)
    (S : SixFunctorDatum D C E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
    (X : SixFunctorSpace D) :
    (∀ K : (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory,
      IsFiniteCoefficientSitePerfect C.l E X.obj.left n K.obj.obj →
      IsFiniteCoefficientSitePerfect C.l E X.obj.left n
        ((sixFunctorCoefficientDual (S.finiteClosed X)).obj (op K)).obj.obj) ∧
    (∀ K : (S.toSixFunctorOperationDatum.integralFiniteTorDomain X).FullSubcategory,
      IsIntegralCoefficientSitePerfect C.l E X.obj.left K.obj.obj →
      IsIntegralCoefficientSitePerfect C.l E X.obj.left
        ((sixFunctorCoefficientDual (S.integralClosed X)).obj (op K)).obj.obj) ∧
    (∀ K : (⊤ : ObjectProperty (sfRationalConstructibleCategory C.l E X.obj.left)).FullSubcategory,
      IsSfRationalCoefficientSitePerfect C.l E X.obj.left K.obj →
      IsSfRationalCoefficientSitePerfect C.l E X.obj.left
        ((sixFunctorCoefficientDual (S.rationalClosed X)).obj (op K)).obj) ∧
    (∀ K : (⊤ : ObjectProperty
        (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)).FullSubcategory,
      IsGeneralAlgebraicallyClosedCoefficientSitePerfect C.l C.Qbar X.obj.left K.obj →
      IsGeneralAlgebraicallyClosedCoefficientSitePerfect C.l C.Qbar X.obj.left
        ((sixFunctorCoefficientDual (S.commonClosed X)).obj (op K)).obj) := by
  sorry

end WeilConjectures
