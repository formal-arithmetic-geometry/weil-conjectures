/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.SixFunctors.RationalVerdier
public import Sheaf.SixFunctors.RationalOperations
public import Sheaf.Paper.CompletedTensorHomTranspose
public import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.RationalizationIdempotentComplete
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.SixFunctors.CoefIntegralFiniteExtension
public import Sheaf.Paper.SitePerfectComplex
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.CategoryTheory.CoefficientBidualTriangles
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.DerivedCompleteOnSlices
import WeilConjectures.CategoryTheory.TruncationTriangle

/-! # Rational evaluation on retracts and finite scalar extension

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-coef-rational-retract-evaluation, statement and proof paragraphs 1--3
(blueprint: lem-coef-rational-retract-evaluation).

The predicates spell out the clauses using the actual raw rational category,
normalized completed tensor-Hom transpose, and signed symmetry. The Hom-domain
witness in the conclusion is infrastructure supplied by rational operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalRetractEvaluation

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (h : ∀ K M : sfRationalConstructibleCategory l E X,
    constructibleRationalHomPairs l E X (op K, M))

/-- The Hom-first transpose, on the recorded permitted pair.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-rational-retract-evaluation). -/
def adjoint {K L W : sfRationalConstructibleCategory l E X}
    (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W) :
    K ⟶ (RationalOperations.homDual l E X h W).obj (op L) :=
  (@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).transpose K
    ⟨(op L, W), h L W⟩ b

/-- Perfection means that both actual adjoints are isomorphisms; the second uses
Koszul symmetry. Source: blueprint statement, second sentence
(blueprint: lem-coef-rational-retract-evaluation). -/
def IsPerfect {K L W : sfRationalConstructibleCategory l E X}
    (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W) : Prop :=
  IsIso (adjoint D l hl X E h b) ∧
    IsIso (adjoint D l hl X E h
      ((@pullbackTensorRationalBraiding l _ E _ _ _ X
        (RationalVerdier.units D l hl X) L K).hom ≫ b))

/-- The usual Hom-first evaluation to any target, including omega and the unit.
Source: blueprint proof paragraphs 1 and 3
(blueprint: lem-coef-rational-retract-evaluation). -/
def evaluation (K W : sfRationalConstructibleCategory l E X) :
    (RationalVerdier.tensor D l hl X E).obj
      ((RationalOperations.homDual l E X h W).obj (op K), K) ⟶ W :=
  (@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).evaluation
    ⟨(op K, W), h K W⟩

/-- Restriction along any chosen splittings with adjoint idempotents, including
zero splittings. The images P,Q are existing objects of the raw category.
Source: blueprint statement and proof paragraph 2
(blueprint: lem-coef-rational-retract-evaluation). -/
def Retracts : Prop :=
  ∀ (K L W P Q : sfRationalConstructibleCategory l E X)
    (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W),
    IsPerfect D l hl X E h b →
    ∀ (i : P ⟶ K) (p : K ⟶ P) (j : Q ⟶ L) (q : L ⟶ Q),
    i ≫ p = 𝟙 P → j ≫ q = 𝟙 Q →
    (RationalVerdier.tensor D l hl X E).map (Prod.mkHom (p ≫ i) (𝟙 L)) ≫ b =
      (RationalVerdier.tensor D l hl X E).map (Prod.mkHom (𝟙 K) (q ≫ j)) ≫ b →
    IsPerfect D l hl X E h
      ((RationalVerdier.tensor D l hl X E).map (Prod.mkHom i j) ≫ b)

/-- The restricted canonical evaluation is the canonical evaluation of the
summand, as an equality of actual arrows. Source: blueprint proof paragraph 1
(blueprint: lem-coef-rational-retract-evaluation). -/
def EvaluationRestriction : Prop :=
  ∀ (K P W : sfRationalConstructibleCategory l E X) (i : P ⟶ K) (p : K ⟶ P),
    i ≫ p = 𝟙 P →
    (RationalVerdier.tensor D l hl X E).map
      (Prod.mkHom ((RationalOperations.homDual l E X h W).map p.op) i) ≫
        evaluation D l hl X E h K W = evaluation D l hl X E h P W

/-- Verdier evaluation is the recorded evaluation with its factors interchanged.
The delta and its inverse restrict by the explicit double-dual formulas.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-rational-retract-evaluation). -/
def VerdierRestriction : Prop :=
  ∀ (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : RationalVerdier.Datum D l hl X E w),
    (∀ K : sfRationalConstructibleCategory l E X,
      IsPerfect D l hl X E h
        ((@pullbackTensorRationalBraiding l _ E _ _ _ X
          (RationalVerdier.units D l hl X) (A.dual.obj (op K)) K).hom ≫ A.evaluation K)) ∧
    ∀ (K P : sfRationalConstructibleCategory l E X) (i : P ⟶ K) (p : K ⟶ P),
      i ≫ p = 𝟙 P →
      ((RationalVerdier.tensor D l hl X E).map
        (Prod.mkHom i (A.dual.map p.op)) ≫ A.evaluation K = A.evaluation P) ∧
      (A.bidual.hom.app P = i ≫ A.bidual.hom.app K ≫
        (A.dual.rightOp ⋙ A.dual).map p) ∧
      (A.bidual.inv.app P = (A.dual.rightOp ⋙ A.dual).map i ≫
        A.bidual.inv.app K ≫ p)

/-- Finite scalar extension uses the coefficient-passage tensor comparison,
with no unrelated pairing or map chosen. The target becomes the scalar-extended
original target. Source: blueprint statement and proof paragraph 2
(blueprint: lem-coef-rational-retract-evaluation). -/
def ScalarExtension (F : Type u) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] (ι : E →ₐ[Padic l] F)
    (hF : ∀ K M : sfRationalConstructibleCategory l F X,
      constructibleRationalHomPairs l F X (op K, M)) : Prop :=
  ∀ (K L W : sfRationalConstructibleCategory l E X)
    (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W),
    IsPerfect D l hl X E h b →
    IsPerfect D l hl X F hF
      ((@rationalTensorScalarComparison l _ E _ _ _ F _ _ _ ι X
        (RationalVerdier.units D l hl X)).inv.app (K, L) ≫
        (RationalVerdier.scalar l X E F ι).map b)

/-- All clauses, for every finite coefficient field. Internal-Hom closure is
asserted rather than assumed. The site-perfect hypothesis occurs only for the
unit-valued pairing, never for Verdier evaluation or the general retract law.
Source: blueprint statement, all sentences
(blueprint: lem-coef-rational-retract-evaluation). -/
def Conclusion : Prop :=
  ∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E],
    ∃ h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M),
    Retracts D l hl X E h ∧ EvaluationRestriction D l hl X E h ∧
    VerdierRestriction D l hl X E h ∧
    (∀ K : sfRationalConstructibleCategory l E X,
      IsSfRationalCoefficientSitePerfect l E X K →
      IsPerfect D l hl X E h
        (evaluation D l hl X E h K (RationalOperations.coefficientUnit l E X D hl))) ∧
    ∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
      (ι : E →ₐ[Padic l] F),
      ∃ hF : ∀ K M : sfRationalConstructibleCategory l F X,
        constructibleRationalHomPairs l F X (op K, M),
      Retracts D l hl X F hF ∧ ScalarExtension D l hl X E h F ι hF

end WeilConjectures.RationalRetractEvaluation

namespace WeilConjectures

/-- Evaluation and biduality restrict to split idempotents; two-sided perfect
pairings stay perfect on adjoint summands and after finite coefficient extension.
For site-perfect objects this applies also to evaluation to the coefficient unit.
Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-coef-rational-retract-evaluation, proof paragraphs 1--3
(blueprint: lem-coef-rational-retract-evaluation).

Proof (the thirteen DAG steps):
1. Use the raw rational category, completed tensor and Hom of rational operations,
and the evaluation-defined delta from rational Verdier duality. Idempotents split
inside this category by lem-weil-rationalization-idempotent-complete.
2. For splittings i,p and j,q, transposition of b gives a,c. Adjointness gives
intertwining with the two idempotents. Naturality identifies the restricted
adjoints with i followed by a and D(j), and j followed by c and D(i).
3. Their inverses are D(q) followed by a inverse and p, and D(p) followed by
c inverse and q. Each inverse equation reduces to the splitting identity using
intertwining. This also covers zero idempotents.
4. Naturality of evaluation gives ev_K composed with D(p) tensor i = ev_P.
The adjoints of Verdier evaluation are identity and delta. Naturality of delta
gives its displayed retract formula and the displayed inverse formula.
5. Finite scalar extension has the canonical tensor and duality comparisons
from integral finite extension, integral scalar comparisons and rational Verdier.
6. lem-coef-rational-scalar-transpose-compatibility transports both adjoints,
their restricted formulas and inverse formulas. Functoriality preserves splitting
identities. The evaluation and delta squares transport step 4 as well.
7. For a site-perfect A use Hom(A,unit) and its canonical evaluation. Internal
Hom exact restriction and exact site restriction identify these maps on slices.
Completed tensor restriction follows from its K-flat and Roos models and exact
countable products, with their fixed quotient and cone-coordinate maps.
8. On a bounded local finite-projective model, the Hom differential is the signed
Hom-complex differential and double evaluation in degree r has sign (-1)^r.
9. lem-coef-rational-bidual-triangle-compatibility supplies the signed shift and
all triangle squares, including the connecting map. Triangle two-out-of-three
makes the invertibility locus stable under shifts and triangles.
10. The unit is reflexive, then finite sums and retracts are reflexive by the
explicit retract inverse. Descend the finite stupid-truncation triangles of the
local bounded model to prove local reflexivity, without integral perfect lifts.
11. Write the rational bidual map as an integral numerator over a uniformizer
power. Its integral cone is constructible. Refine to a finite affine pro-etale
cover (the empty scheme is immediate). Local rational vanishing gives finitely
many annihilator powers; their maximum annihilates every cohomology sheaf
by sheaf separatedness. This does not yet annihilate the cone identity.
12. Derived completeness and exact countable products bound cone cohomology.
If scalar powers kill the ends of a triangle, their sum kills the middle by
Hom exactness. Induction on the finite cohomological truncations therefore kills
the cone identity by a power. Inverting the uniformizer makes the cone zero,
so the actual global bidual map is invertible and unit evaluation is perfect.
13. Apply steps 2--3 to the unit-valued pairing and step 6 with the canonical
unit and internal-Hom scalar comparisons. This gives its retract and extension
clauses, using the very same normalized evaluation and both its adjoints. -/
theorem coef_rational_retract_evaluation
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] :
    RationalRetractEvaluation.Conclusion D l hl X := by
  sorry

end WeilConjectures
