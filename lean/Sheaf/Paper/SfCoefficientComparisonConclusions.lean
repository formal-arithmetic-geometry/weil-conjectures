module

public import Sheaf.Paper.FiniteCoefficientHomChange
public import Sheaf.Paper.IntegralHomReductionModels
public import Sheaf.Paper.FiniteReductionComparisons
public import Sheaf.Paper.FiniteSmoothPullbackExchange
public import Sheaf.Paper.FiniteReductionAffineOrientation
public import Sheaf.CategoryTheory.PerfectPairingReductionAdjoints
public import Sheaf.Paper.SfPackageQbarAdjunctionMapDescent
public import Sheaf.Paper.BasicOperationsCoefficientReduction
public import Sheaf.Paper.CompactSupportProjectionFormula

/-! # Named conclusions for coefficient comparison coherence

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, final coherence sentence and the coefficient,
purity, projection and pairing comparisons it invokes
(blueprint: def-sf-coefficient-comparison-conclusions).

## Main definitions

* `FiniteHomComparisonConclusion`: evaluation, quotient and site comparisons.
* `IntegralHomReductionConclusion`: complete internal Hom and its reduction transpose.
* `PurityFiniteReductionConclusion`: the eight purity and trace reduction equations.
* `ProjectionCoefficientConclusion`: the four coefficient projection squares.
* `PerfectPairingAdjointsConclusion`: evaluation, adjoint and inverse-adjoint squares.
* `CommonStageAdjunctionDescentConclusion`: representative Hom, unit and counit formulas.
* `BasicOperationsReductionConclusion`: elementary coefficient comparisons, reusing
  `IntegralHomReductionConclusion` for its integral-Hom clause.

These are assertion predicates about the published maps, not proofs or new maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.MonoidalCategory
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients

/-- The finite internal-Hom comparison with its evaluation, site and quotient equations.
Source: blueprint final coherence sentence and its cited coefficient theorems
(blueprint: def-sf-coefficient-comparison-conclusions). -/
def FiniteHomComparisonConclusion
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (n m : ℕ) (h : m ≤ n) : Prop :=
    CoefficientEvaluationCompatible
      (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h) ∧
    FiniteHomEvaluation (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h) ∧
    (∀ K M : finiteHomEtale l E X n,
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        ((finiteHomEtaleReduction l E X h).obj
          ((Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X)).obj (op K, M))) ∧
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        ((Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))) X)).obj
          (op ((finiteHomEtaleReduction l E X h).obj K),
            (finiteHomEtaleReduction l E X h).obj M)) ∧
      IsIso (etaleFiniteHomCanonical l E X h K M)) ∧
    CoefficientEvaluationCompatible (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
      (coefficientFiniteQuotientDerived l E X h)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h) ∧
    FiniteHomEvaluation (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
      (coefficientFiniteQuotientDerived l E X h)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h) ∧
    (∀ K M : normalizedDVRDerived l E X n,
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K →
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X M →
      finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X
        ((coefficientFiniteQuotientDerived l E X h).obj
          ((coefficientFiniteInternalHom l E X n).obj (op K, M))) ∧
      finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X
        ((coefficientFiniteInternalHom l E X m).obj
          (op ((coefficientFiniteQuotientDerived l E X h).obj K),
            (coefficientFiniteQuotientDerived l E X h).obj M)) ∧
      IsIso (proEtaleFiniteHomCanonical l E X h K M)) ∧
    FiniteHomEtaleCocycle l E X h ∧ FiniteHomIntrinsicCocycle l E X h ∧
    FiniteHomSiteFormula l E X h


/-- The integral internal-Hom comparison is the normalized evaluation transpose.
Source: blueprint final coherence sentence and its cited coefficient theorems
(blueprint: def-sf-coefficient-comparison-conclusions). -/
def IntegralHomReductionConclusion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u}) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) : Prop :=
    ∃ a : IntegralHom.TensorPresentation.{u, u} Y (completedIntegralCommRingSheaf l E Y D hl),
      (∀ K L : completedIntegralDerivedCategory l E Y D hl,
        IsDerivedComplete l E Y D hl L →
          IsDerivedComplete l E Y D hl
            ((IntegralHom.hom.{u, u} Y
              (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, L))) ∧
      ∀ n : ℕ, ∃ m : IntegralHom.ReductionPresentation l E Y D hl a n,
        ∀ K L : completedIntegralDerivedCategory l E Y D hl,
          IsIso (IntegralHom.comparison l E Y D hl m K L) ∧
          (m.target.tensor.map (Prod.mkHom
              (𝟙 ((integralDerivedReduction l E Y D hl n).obj K))
              (IntegralHom.comparison l E Y D hl m K L)) ≫
            (m.target.adjunction ((integralDerivedReduction l E Y D hl n).obj K)).counit.app
              ((integralDerivedReduction l E Y D hl n).obj L) =
            m.mu.inv.app (K,
              (IntegralHom.hom.{u, u} Y
                (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, L)) ≫
            (integralDerivedReduction l E Y D hl n).map ((a.adjunction K).counit.app L)) ∧
          ∀ (T : completedIntegralDerivedCategory l E Y D hl)
            (f : T ⟶
              (IntegralHom.hom.{u, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj (op K, L)),
            (m.target.adjunction ((integralDerivedReduction l E Y D hl n).obj K)).homEquiv
                ((integralDerivedReduction l E Y D hl n).obj T)
                ((integralDerivedReduction l E Y D hl n).obj L)
                (m.mu.inv.app (K, T) ≫ (integralDerivedReduction l E Y D hl n).map
                  (((a.adjunction K).homEquiv T L).symm f)) =
              (integralDerivedReduction l E Y D hl n).map f ≫
                IntegralHom.comparison l E Y D hl m K L


/-- All eight retained purity reduction equations, with their exact individual domains.
Source: fix-prop-coherence and thm-pur-finite-reduction-of-purity
(blueprint: def-sf-coefficient-comparison-conclusions). -/
def PurityFiniteReductionConclusion : Prop :=
  (∀ (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
{X Y : Scheme.{u}}
[X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
[LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
[QuasiCompact (X ↘ Spec (.of P.field.k))]
[IsSeparated (X ↘ Spec (.of P.field.k))]
[LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
[QuasiCompact (Y ↘ Spec (.of P.field.k))]
[IsSeparated (Y ↘ Spec (.of P.field.k))]
(f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
 (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K),
    (P.finiteReduction m hm hmn X).map (P.smoothPurityMap f d K hK) ≫
        P.finiteReductionExceptionalComparison m hm hmn f d K hK =
      (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
        (P.finiteReductionSetting m hm).smoothPurityMap f d
          ((P.finiteReduction m hm hmn Y).obj K)
          (P.finiteReduction_preserves_ctf m hm hmn Y K hK)) ∧
  (∀ (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
{X Y : Scheme.{u}}
[X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
[LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
[QuasiCompact (X ↘ Spec (.of P.field.k))]
[IsSeparated (X ↘ Spec (.of P.field.k))]
[LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
[QuasiCompact (Y ↘ Spec (.of P.field.k))]
[IsSeparated (Y ↘ Spec (.of P.field.k))]
(f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
 (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K),
    (P.finiteReduction m hm hmn Y).map (P.coefficientValuedSmoothTrace f d K hK) =
      P.finiteReductionCompactSupportComparison m hm hmn f
          ((P.compositionShiftedPullback f d).obj K) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
        (P.finiteReductionSetting m hm).coefficientValuedSmoothTrace f d
          ((P.finiteReduction m hm hmn Y).obj K)
          (P.finiteReduction_preserves_ctf m hm hmn Y K hK)) ∧
  (∀ (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
{X Y : Scheme.{u}}
[X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
[LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
[QuasiCompact (X ↘ Spec (.of P.field.k))]
[IsSeparated (X ↘ Spec (.of P.field.k))]
[LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
[QuasiCompact (Y ↘ Spec (.of P.field.k))]
[IsSeparated (Y ↘ Spec (.of P.field.k))]
(f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
 (d : ℕ) [SmoothOfRelativeDimension d f],
    (P.finiteReduction m hm hmn Y).map (P.smoothTrace f d) ≫
        P.finiteReductionUnitComparison m hm hmn Y =
      P.finiteReductionCompactSupportComparison m hm hmn f
          ((P.compositionShiftedPullback f d).obj (P.coefficientUnit Y)) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          ((P.finiteReductionSourceComparison m hm hmn f d (P.coefficientUnit Y)).hom ≫
            ((P.finiteReductionSetting m hm).compositionShiftedPullback f d).map
              (P.finiteReductionUnitComparison m hm hmn Y)) ≫
        (P.finiteReductionSetting m hm).smoothTrace f d) ∧
  (∀ (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
{X Y Z : Scheme.{u}}
[X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
[Z.Over (Spec (.of P.field.k))]
[LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
[QuasiCompact (X ↘ Spec (.of P.field.k))]
[IsSeparated (X ↘ Spec (.of P.field.k))]
[LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
[QuasiCompact (Y ↘ Spec (.of P.field.k))]
[IsSeparated (Y ↘ Spec (.of P.field.k))]
[LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
[QuasiCompact (Z ↘ Spec (.of P.field.k))]
[IsSeparated (Z ↘ Spec (.of P.field.k))]
(f : X ⟶ Y) (g : Y ⟶ Z)
[f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
[IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
(d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
 (K : Scheme.proEtaleDerivedCategory Z P.Ring),
    (P.finiteReduction m hm hmn X).map
        (P.compositionSourceIdentification f g d e K).hom ≫
      (P.finiteReductionSourceComparison m hm hmn f d
        ((P.compositionShiftedPullback g e).obj K)).hom ≫
      (((P.finiteReductionSetting m hm).compositionShiftedPullback f d).map
        (P.finiteReductionSourceComparison m hm hmn g e K).hom) =
    (P.finiteReductionSourceComparison m hm hmn (f ≫ g) (d + e) K).hom ≫
      ((P.finiteReductionSetting m hm).compositionSourceIdentification f g d e
        ((P.finiteReduction m hm hmn Z).obj K)).hom) ∧
  (∀ (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
{X Y Z : Scheme.{u}}
[X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
[Z.Over (Spec (.of P.field.k))]
[LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
[QuasiCompact (X ↘ Spec (.of P.field.k))]
[IsSeparated (X ↘ Spec (.of P.field.k))]
[LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
[QuasiCompact (Y ↘ Spec (.of P.field.k))]
[IsSeparated (Y ↘ Spec (.of P.field.k))]
[LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
[QuasiCompact (Z ↘ Spec (.of P.field.k))]
[IsSeparated (Z ↘ Spec (.of P.field.k))]
(f : X ⟶ Y) (g : Y ⟶ Z)
[f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
[IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
(d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K),
    (P.finiteReduction m hm hmn X).map (P.compositionExceptionalIso f g K hK).hom ≫
      P.finiteReductionExceptionalComparison m hm hmn f d
        ((P.compositionExceptional g).obj K) (P.compositionExceptional_ctf g e K hK) ≫
      ((P.finiteReductionSetting m hm).compositionExceptional f).map
        (P.finiteReductionExceptionalComparison m hm hmn g e K hK) =
    P.finiteReductionExceptionalComparison m hm hmn (f ≫ g) (d + e) K hK ≫
      ((P.finiteReductionSetting m hm).compositionExceptionalIso f g
        ((P.finiteReduction m hm hmn Z).obj K)
        (P.finiteReduction_preserves_ctf m hm hmn Z K hK)).hom) ∧
  (∀ (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
{X Y Z : Scheme.{u}}
[X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
[Z.Over (Spec (.of P.field.k))]
[LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
[QuasiCompact (X ↘ Spec (.of P.field.k))]
[IsSeparated (X ↘ Spec (.of P.field.k))]
[LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
[QuasiCompact (Y ↘ Spec (.of P.field.k))]
[IsSeparated (Y ↘ Spec (.of P.field.k))]
[LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
[QuasiCompact (Z ↘ Spec (.of P.field.k))]
[IsSeparated (Z ↘ Spec (.of P.field.k))]
(f : X ⟶ Y) (g : Y ⟶ Z)
[f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
[IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
(d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K),
    (P.finiteReduction m hm hmn X).map
        ((P.compositionSourceIdentification f g d e K).hom ≫
          (P.compositionShiftedPullback f d).map (P.smoothPurityMap g e K hK) ≫
          P.smoothPurityMap f d ((P.compositionExceptional g).obj K)
            (P.compositionExceptional_ctf g e K hK) ≫
          (P.compositionExceptionalIso f g K hK).inv) ≫
        P.finiteReductionExceptionalComparison m hm hmn (f ≫ g) (d + e) K hK =
      (P.finiteReductionSourceComparison m hm hmn (f ≫ g) (d + e) K).hom ≫
        ((P.finiteReductionSetting m hm).compositionSourceIdentification f g d e
          ((P.finiteReduction m hm hmn Z).obj K)).hom ≫
        ((P.finiteReductionSetting m hm).compositionShiftedPullback f d).map
          ((P.finiteReductionSetting m hm).smoothPurityMap g e
            ((P.finiteReduction m hm hmn Z).obj K)
            (P.finiteReduction_preserves_ctf m hm hmn Z K hK)) ≫
        (P.finiteReductionSetting m hm).smoothPurityMap f d
          (((P.finiteReductionSetting m hm).compositionExceptional g).obj
            ((P.finiteReduction m hm hmn Z).obj K))
          ((P.finiteReductionSetting m hm).compositionExceptional_ctf g e
            ((P.finiteReduction m hm hmn Z).obj K)
            (P.finiteReduction_preserves_ctf m hm hmn Z K hK)) ≫
        ((P.finiteReductionSetting m hm).compositionExceptionalIso f g
          ((P.finiteReduction m hm hmn Z).obj K)
          (P.finiteReduction_preserves_ctf m hm hmn Z K hK)).inv) ∧
  (∀ (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
{X X' Y Y' : Scheme.{u}}
[X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
[Y.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
[LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
[QuasiCompact (X ↘ Spec (.of P.field.k))]
[IsSeparated (X ↘ Spec (.of P.field.k))]
[LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
[QuasiCompact (X' ↘ Spec (.of P.field.k))]
[IsSeparated (X' ↘ Spec (.of P.field.k))]
[LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
[QuasiCompact (Y ↘ Spec (.of P.field.k))]
[IsSeparated (Y ↘ Spec (.of P.field.k))]
[LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
[QuasiCompact (Y' ↘ Spec (.of P.field.k))]
[IsSeparated (Y' ↘ Spec (.of P.field.k))]
(u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
[u.IsOver (Spec (.of P.field.k))] [v.IsOver (Spec (.of P.field.k))]
[f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
[IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
(sq : IsPullback u f' f v) (d : ℕ)
[SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
 (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K),
    ((P.finiteReduction m hm hmn X').map
        (P.finiteReductionBaseChangeSource u f' f v sq d K).hom ≫
      (P.finiteReductionSourceComparison m hm hmn f' d
        ((P.finiteReductionPullback v).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).compositionShiftedPullback f' d).map
        (P.finiteReductionPullbackComparison m hm hmn v K).hom =
    (P.finiteReductionPullbackComparison m hm hmn u
        ((P.compositionShiftedPullback f d).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback u).map
        (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionBaseChangeSource
        u f' f v sq d ((P.finiteReduction m hm hmn Y).obj K)).hom) ∧
    ((P.finiteReduction m hm hmn X').map
        (P.finiteReductionSmoothExchange u f' f v sq d K hK).hom ≫
      P.finiteReductionExceptionalComparison m hm hmn f' d
        ((P.finiteReductionPullback v).obj K) (P.finiteReductionBaseChangeInput v K hK) ≫
      ((P.finiteReductionSetting m hm).compositionExceptional f').map
        (P.finiteReductionPullbackComparison m hm hmn v K).hom =
    (P.finiteReductionPullbackComparison m hm hmn u
        ((P.compositionExceptional f).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback u).map
        (P.finiteReductionExceptionalComparison m hm hmn f d K hK) ≫
      ((P.finiteReductionSetting m hm).finiteReductionSmoothExchange u f' f v sq d
        ((P.finiteReduction m hm hmn Y).obj K)
        (P.finiteReduction_preserves_ctf m hm hmn Y K hK)).hom)) ∧
  (∀     (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))],
    (P.finiteReduction m hm hmn Y).map (P.finiteReductionOrientation Y) ≫
      P.finiteReductionOrientationExceptionalComparison m hm hmn Y ≫
      ((P.finiteReductionSetting m hm).compositionExceptional
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).map
          (P.finiteReductionOrientationInputComparison m hm hmn Y).hom =
    P.finiteReductionUnitComparison m hm hmn Y ≫
      (P.finiteReductionSetting m hm).finiteReductionOrientation Y)


/-- The projection coefficient squares, including nonflat finite quotients,
completed reduction, and ramified coefficient-field extensions.
Source: fix-prop-projection-formula, coefficient clauses
(blueprint: def-sf-coefficient-comparison-conclusions). -/
def ProjectionCoefficientConclusion
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) : Prop :=
    (∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ≤ m)
      (K : finiteTorConstructibleCategory C.l E m hm X.obj.left)
      (L : finiteTorConstructibleCategory C.l E m hm Y.obj.left),
      CompactSupportProjectionChange (PurCompactSupport.finiteQuotientChange C.l E m n hm hn h)
        c K.obj L.obj) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n)
      (K : sfIntegralConstructibleCategory C.l E X.obj.left)
      (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
      finiteTorConstructibleIntegral C.l E X.obj.left K.obj →
      finiteTorConstructibleIntegral C.l E Y.obj.left L.obj →
      CompactSupportProjectionChange (PurCompactSupport.reduction C.l E n hn) c K.obj L.obj) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic C.l) F]
      [FiniteDimensional (Padic C.l) F] (i : E →ₐ[Padic C.l] F)
      (K : sfIntegralConstructibleCategory C.l E X.obj.left)
      (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
      finiteTorConstructibleIntegral C.l E Y.obj.left L.obj →
      CompactSupportProjectionChange (PurCompactSupport.completedChange C.l E F i)
        c K.obj L.obj) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic C.l) F]
      [FiniteDimensional (Padic C.l) F] (i : E →ₐ[Padic C.l] F)
      (e : ℕ) (he : PurCompactSupport.Ramification C.l E F i e) (hepos : 1 ≤ e)
      (n : ℕ) (hn : 1 ≤ n)
      (K : sixFunctorFiniteCategory D C E n hn X)
      (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      CompactSupportProjectionChange
        (PurCompactSupport.finiteChange C.l E F i e he hepos n hn) c K.obj L.obj)


/-- Evaluation, adjoint and inverse-adjoint squares of a reduced perfect pairing.
The actual pairing is the composite of cup, evaluation and normalized trace; its
reduction square is supplied by the projection, Hom and purity clauses below.
This is the formal inverse-adjoint portion, without an invertibility premise on r.
Source: thm-pod-finite-reduction, final displayed square
(blueprint: def-sf-coefficient-comparison-conclusions). -/
def PerfectPairingAdjointsConclusion : Prop :=
  ∀ {𝒞 :Type (u + 2)} {𝒟 : Type (u + 2)}
  [Category.{u + 2} 𝒞] [Category.{u + 2} 𝒟]
  [MonoidalCategory 𝒞] [MonoidalCategory 𝒟]
  [MonoidalClosed 𝒞] [MonoidalClosed 𝒟]
    (F : 𝒞 ⥤ 𝒟) (m : F.CoreMonoidal)
    {C D : 𝒞} {C' D' : 𝒟}
    (β : C ⊗ D ⟶ 𝟙_ 𝒞) (β' : C' ⊗ D' ⟶ 𝟙_ 𝒟)
    (c : F.obj C ≅ C') (r : F.obj D ⟶ D')
    (b : D ≅ (ihom C).obj (𝟙_ 𝒞)) (b' : D' ≅ (ihom C').obj (𝟙_ 𝒟))
    (_hb : b.hom = MonoidalClosed.curry β)
    (_hb' : b'.hom = MonoidalClosed.curry β')
    (h : F.obj ((ihom C).obj (𝟙_ 𝒞)) ≅ (ihom (F.obj C)).obj (𝟙_ 𝒟))
    (_heval : (F.obj C ◁ h.hom) ≫ (ihom.ev (F.obj C)).app (𝟙_ 𝒟) =
      (m.μIso C ((ihom C).obj (𝟙_ 𝒞))).hom ≫
        F.map ((ihom.ev C).app (𝟙_ 𝒞)) ≫ m.εIso.inv)
    (_hpair : (c.hom ⊗ₘ r) ≫ β' = (m.μIso C D).hom ≫ F.map β ≫ m.εIso.inv),
    (c.hom ⊗ₘ (perfectPairingDualComparison F c h).hom) ≫
        (ihom.ev C').app (𝟙_ 𝒟) =
      (m.μIso C ((ihom C).obj (𝟙_ 𝒞))).hom ≫
        F.map ((ihom.ev C).app (𝟙_ 𝒞)) ≫ m.εIso.inv ∧
    r ≫ b'.hom = F.map b.hom ≫ (perfectPairingDualComparison F c h).hom ∧
    F.map b.inv ≫ r = (perfectPairingDualComparison F c h).hom ≫ b'.inv ∧
    r = F.map b.hom ≫ (perfectPairingDualComparison F c h).hom ≫ b'.inv ∧
    ∃ rIso : F.obj D ≅ D', rIso.hom = r ∧
      rIso.inv = b'.hom ≫ (perfectPairingDualComparison F c h).inv ≫ F.map b.inv


/-- Exact representative formulas for descended Hom bijections, units, counits
and evaluations. The premises are precisely compatibility with field transitions.
Source: exceptional-adjunction paragraph, common-stage descent
(blueprint: def-sf-coefficient-comparison-conclusions). -/
def CommonStageAdjunctionDescentConclusion : Prop :=
  ∀
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    (F : (stageSystem l Ω X).Morphism (stageSystem l Ω Y))
    (G : (stageSystem l Ω Y).Morphism (stageSystem l Ω X))
    (_hF : ∀ E, F.Φ E = sfCompactSupportFiniteFunctor l D.k
      (finiteFieldDatumPrimeUnit D l hl) c (Coefficient.{u} l Ω E))
    (a : ∀ E, F.Φ E ⊣ G.Φ E)
    (_unit : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
      (stageTransition l Ω X E L h).map ((a E).unit.app K) ≫
        (G.β h).hom.app ((F.Φ E).obj K) ≫
        (G.Φ L).map ((F.β h).hom.app K) =
      (a L).unit.app ((stageTransition l Ω X E L h).obj K))
    (_counit : ∀ (E L : Index l Ω) (h : E ≤ L) (M : Stage l Ω Y E),
      (F.β h).hom.app ((G.Φ E).obj M) ≫
        (F.Φ L).map ((G.β h).hom.app M) ≫
        (a L).counit.app ((stageTransition l Ω Y E L h).obj M) =
      (stageTransition l Ω Y E L h).map ((a E).counit.app M)),
    (∃ A : F.functor ⊣ G.functor,
      (∀ (K : Pair l Ω X) (M : Pair l Ω Y) (L : Index l Ω)
        (hK : K.stage ≤ L) (hM : M.stage ≤ L)
        (b : (F.Φ L).obj (K.toStage hK) ⟶ M.toStage hM),
        A.homEquiv K M
            (StageSystem.PairCategory.mkHom
              (X := F.functor.obj K) (Y := M) L hK hM ((F.β hK).hom.app K.obj ≫ b)) =
          StageSystem.PairCategory.mkHom
              (X := K) (Y := G.functor.obj M) L hK hM
            ((a L).homEquiv (K.toStage hK) (M.toStage hM) b ≫
              (G.β hM).inv.app M.obj)) ∧
      (∀ (K : Pair l Ω X) (M : Pair l Ω Y) (L : Index l Ω)
        (hK : K.stage ≤ L) (hM : M.stage ≤ L)
        (b : K.toStage hK ⟶ (G.Φ L).obj (M.toStage hM)),
        (A.homEquiv K M).symm
            (StageSystem.PairCategory.mkHom
              (X := K) (Y := G.functor.obj M) L hK hM (b ≫ (G.β hM).inv.app M.obj)) =
          StageSystem.PairCategory.mkHom
              (X := F.functor.obj K) (Y := M) L hK hM
            ((F.β hK).hom.app K.obj ≫
              ((a L).homEquiv (K.toStage hK) (M.toStage hM)).symm b)) ∧
      (∀ K : Pair l Ω X,
        A.unit.app K =
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := X) K.stage).map ((a K.stage).unit.app K.obj)) ∧
      (∀ M : Pair l Ω Y,
        A.counit.app M =
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := Y) M.stage).map ((a M.stage).counit.app M.obj))) ∧
    SfQbarEvaluationDescent D l hl Ω X ∧ SfQbarEvaluationDescent D l hl Ω Y


/-- The elementary coefficient comparisons in their full proved domains.
This spells out the preservation, representative, mate, evaluation, scalar,
identity, tensor and quotient equations of the recorded reduction theorem.
Source: lem-fix-operation-reduction, every conclusion clause
(blueprint: def-sf-coefficient-comparison-conclusions). -/
def BasicOperationsReductionConclusion
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω]
    (X Y : Scheme.{u}) (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
    ((∀ K : DerivedCategory (integralTowerModules l E Y),
        sfIntegralConstructible l E Y K →
          sfIntegralConstructible l E X ((integralDerivedPullback l E f).obj K) ∧
            ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
              (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ),
              IsIso (integralPullbackFiniteComparison l E f K P e n)) ∧
      ∀ (W : Scheme), W = X ∨ W = Y →
        ∀ M N : DerivedCategory (integralTowerModules l E W),
          sfIntegralConstructible l E W M → sfIntegralConstructible l E W N →
            sfIntegralConstructible l E W ((integralCompletedTensor l E W).obj (M, N)) ∧
              ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
                (e : DerivedCategory.Q.obj P.obj ≅ M)
                (d : DerivedCategory.Q.obj Q.obj ≅ N) (n : ℕ),
                IsIso (integralTensorFiniteComparison l E W M N P Q e d n)) ∧
    (∀ (n : ℕ)
      (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))),
      IsIso ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N).hom) ∧
    (∀ (m n : ℕ) (h : n ≤ m)
      (M : proEtaleDerivedCategory Y (finiteCoefficientRing l E (m + 1))),
      IsIso ((pullbackTensorQuotient l E f h).hom.app M)) ∧
    (∀ (m n : ℕ) (h : n ≤ m)
      (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (m + 1))),
      canonicalFinitePullbackTensor_quotient_condition l E f
        (hX := hX) (hY := hY) h M N) ∧
    (∀ (K₀ : Type u) [Field K₀] (_hl₀ : IsUnit (l : K₀))
      [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
      [QuasiCompact (X ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
      [QuasiCompact (Y ↘ Spec (.of K₀))]
      [f.IsOver (Spec (.of K₀))]
      (K : DerivedCategory (scalarReductionSource l E X))
      (_hK : sfIntegralConstructible l E X K),
      (∃ hprod : HasProduct (sfDirectImageTerm l E f K),
          @Nonempty (@SfIntegralDirectImage l _ E _ _ _ X Y f K hprod)) ∧
        ∀ [_hprod : HasProduct (sfDirectImageTerm l E f K)]
          (L : SfIntegralDirectImage l E f K),
          sfIntegralConstructible l E Y L.obj ∧
            IsSfDerivedComplete l E Y L.obj ∧
              (∀ n : ℕ, IsIso (sfDirectImageReductionComparison l E f L n)) ∧
              ∀ n : ℕ,
                intrinsicFiniteTorsionConstructible l E (n + 1)
                  (Nat.succ_le_succ (Nat.zero_le n)) Y
                  (sfFiniteDerivedDirectImage l E f K n)) ∧
    (∀ (K₀ : Type u) [Field K₀] (_hl₀ : IsUnit (l : K₀))
      [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
      [QuasiCompact (X ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
      [QuasiCompact (Y ↘ Spec (.of K₀))]
      [f.IsOver (Spec (.of K₀))] [IsSeparated f]
      [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f)
      (K : DerivedCategory (scalarReductionSource l E X))
      (_hK : sfIntegralConstructible l E X K)
      (M : DerivedCategory (scalarReductionSource l E Y))
      (p : M ⟶ ∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n)
      (δ : (∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n) ⟶ M⟦(1 : ℤ)⟧)
      (_hδ : IsDerivedLimitTriangle (sfCompactSupportTransition l E c K) M p δ),
      sfIntegralConstructible l E Y M ∧
        (∀ n : ℕ, IsIso (coefIntegralCompactSupportComparison l E c K M p n)) ∧
        ∀ n : ℕ,
          coefIntegralCompactSupportComparison l E c K M p (n + 1) ≫
              coefCompactSupportFiniteTransition l E c K n =
            sfCompactSupportReductionTransition l E Y M n ≫
              (sfCompactSupportFiniteRestriction l E Y n).mapDerivedCategory.map
                (coefIntegralCompactSupportComparison l E c K M p n)) ∧
    (∀ (K₀ : Type u) [Field K₀] (_hl₀ : IsUnit (l : K₀))
      (n : ℕ) (hn : 1 ≤ n) {X' Y' : Scheme.{u}}
      [X'.Over (Spec (.of K₀))] [Y'.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X' ↘ Spec (.of K₀))]
      [QuasiCompact (X' ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y' ↘ Spec (.of K₀))]
      [QuasiCompact (Y' ↘ Spec (.of K₀))]
      (g : X' ⟶ Y') [g.IsOver (Spec (.of K₀))]
      [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
      (c : Compactification g) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
      (K : proEtaleDerivedCategory X' (Padic.coefficientExtensionRing l E n))
      (_hK : finiteTorConstructible l E n hn X' K)
      (_hKm : finiteTorConstructible l E m hm X'
        ((finiteLevelDerivedReduction l E m n hmn X').obj K)),
      IsIso (finiteLevelCompactSupportReductionComparison l E m n hm hmn c K)) ∧
    (∀ (W : Scheme.{u}) (m n : ℕ) (h : m ≤ n),
      CoefficientEvaluationCompatible (finiteIntrinsicClosed l E W n)
        (finiteIntrinsicClosed l E W m) (coefficientFiniteQuotientDerived l E W h)
        ((coefficientDerivedSystemEvaluationCalculus l E W).choose.quotientCalculus.tensor h) ∧
      FiniteHomEvaluation (finiteIntrinsicClosed l E W n) (finiteIntrinsicClosed l E W m)
        (coefficientFiniteQuotientDerived l E W h)
        ((coefficientDerivedSystemEvaluationCalculus l E W).choose.quotientCalculus.tensor h)) ∧
    (∀ (W : Scheme.{u}) (m n : ℕ) (h : m ≤ n)
      (P Q : normalizedDVRDerived l E W n),
      IsProEtaleSitePerfect W (integralCoefficientCommRingSheaf l E W n) P →
      IsIso (finiteIntrinsicReductionHom l E W h P Q)) ∧
    (∀ (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (W : Scheme.{u}),
      IntegralHomReductionConclusion l E W D hl) ∧
    (IntegralScalarOperations.Comparisons l Ω X Y f) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L) (W : Scheme.{u}),
      CoefficientEvaluationCompatible (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
        (integralOrdinaryDerivedScalar l E L ι W) (scalarClosedTensor l E L ι W) ∧
      FiniteHomEvaluation (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
        (integralOrdinaryDerivedScalar l E L ι W) (scalarClosedTensor l E L ι W)) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
      (K : sfRationalConstructibleCategory l E Y),
      HEq ((rationalPullbackScalarComparison l E L ι f).hom.app K)
        ((sfRationalConstructibleLocalization l L X).map
          (integralPullbackScalarComparison l E L ι f K.obj).hom)) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
      (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (M N : sfRationalConstructibleCategory l E W),
      HEq ((rationalTensorScalarComparison l E L ι W).hom.app (M, N))
        ((sfRationalConstructibleLocalization l L W).map
          (integralTensorScalarComparison l E L ι W M.obj N.obj).hom)) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
      (W : Scheme.{u}) (P : (constructibleRationalHomPairs l E W).FullSubcategory),
      HEq (rationalHomScalarComparison l E L ι W P).hom
        ((sfRationalConstructibleLocalization l L W).map
          (integralHomScalarComparison l E L ι W
            (integralPairOfRationalHomPair l E W P)).hom)) ∧
    commonStagePullbackRepresentativeLaws l Ω f ∧
    (∀ W : Scheme.{u}, ∀ [∀ w : W, Invertible (l : W.residueField w)],
      commonStageTensorRepresentativeLaws l Ω W) ∧
    (∀ W : Scheme.{u}, commonStageInternalHomRepresentativeLaws l Ω W) ∧
    coefficientOperationMateEquations.{u} ∧
    (canonicalIntegralPullbackTensor_associative l E f) ∧
    (canonicalIntegralPullbackTensor_unit l E f) ∧
    (canonicalRationalPullbackTensor_associative l E f) ∧
    (canonicalRationalPullbackTensor_unit l E f) ∧
    (canonicalCommonStagePullbackTensor_associative l Ω f) ∧
    (canonicalCommonStagePullbackTensor_unit l Ω f) ∧
    (∀ M N : sfRationalConstructibleCategory l E Y,
      HEq ((canonicalRationalPullbackTensor l E f) M N).hom
        ((sfRationalConstructibleLocalization l E X).map
          ((canonicalIntegralPullbackTensor l E f) M.obj N.obj).hom)) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
      (M N : sfIntegralConstructibleCategory l E Y),
      canonicalIntegralPullbackTensor_scalar_condition l E L ι f M N) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
      (M N : sfRationalConstructibleCategory l E Y),
      canonicalRationalPullbackTensor_scalar_condition l E L ι f M N) ∧
    (∀ (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
      [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
      [QuasiCompact (X ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
      [QuasiCompact (Y ↘ Spec (.of K₀))]
      [f.IsOver (Spec (.of K₀))] [IsSeparated f]
      [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f),
      ∃ S : SfCompactSupportCoefficientAction l K₀ hl₀ Ω c,
        operationIntegralCoefficientCoherent l Ω X Y
          (fun E₀ ↦ sfCompactSupportFiniteIntegralFunctor l K₀ hl₀ c
            (Coefficient.{u} l Ω E₀)) (fun h ↦ S.integralBeta h)) ∧
    (∀ (K₀ : Type u) [Field K₀] (_hl₀ : IsUnit (l : K₀))
      [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
      [QuasiCompact (X ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
      [QuasiCompact (Y ↘ Spec (.of K₀))]
      [f.IsOver (Spec (.of K₀))],
      OperationDirectImageCoefficientAction l Ω X Y f) ∧
    (directImageScalarExtensionLaws.{u} l) ∧
    (compactSupportScalarIsomorphisms.{u} l) ∧
    (compactSupportScalarExtensionLaws.{u}) ∧
    directImageScalarTowerLaws.{u} ∧
    coefficientOperationIdentityLaws.{u} ∧
    (∀ (n : ℕ),
      canonicalFinitePullbackTensor_associativity_condition l E f n ∧
      canonicalFinitePullbackTensor_unit_condition l E f n ∧
      canonicalFinitePullbackTensor_braiding_condition l E f n) ∧
    (∀ (S : Scheme.{u}) (_hS : ∀ s : S, IsUnit (l : S.presheaf.stalk s))
      [X.Over S] [Y.Over S]
      [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
      [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
      [f.IsOver S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f),
      IsExceptionalAdjointAdmissibleAtIntegral l E S X Y _hS f c →
      ∃ DE : ExceptionalFiniteFieldFamily l E f c,
        HasUniformFiniteExceptionalAdjoints l (fun _ : PUnit.{1} ↦ E) f c DE ∧
          ExceptionalFiniteReductionsCompatible l E f c DE ∧
          ∀ (L : Type u) [Field L] [Algebra (Padic l) L]
            [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L),
            ∃ DL : ExceptionalFiniteFieldFamily l L f c,
              HasUniformFiniteExceptionalAdjoints l (fun _ : PUnit.{1} ↦ L) f c DL ∧
                ExceptionalFiniteReductionsCompatible l L f c DL ∧
                ExceptionalFiniteScalarsCompatible l E L ι f c DE DL)


end WeilConjectures
