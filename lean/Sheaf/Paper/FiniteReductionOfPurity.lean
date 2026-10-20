/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.FiniteReductionComparisons
public import Sheaf.Paper.FiniteSmoothPullbackExchange
public import Sheaf.Paper.FiniteReductionAffineOrientation
public import Sheaf.Paper.SmoothTrace
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity

import Sheaf.Paper.FixedFinitePositiveCoefficientTwist
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.SmoothPurityMap
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension
import Sheaf.Paper.SmoothExceptionalBaseChangeStatement
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Paper.FiniteCoefficientReductionFlatModel
import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
import Sheaf.Paper.PurityAffineLineOrientation
import Sheaf.Paper.PurityCompositionCoherence
import Sheaf.Paper.PurityDiagonalDualizingObject
import Sheaf.AlgebraicGeometry.CartierKummerMap
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.Paper.CohomologicalSmoothnessTheorem
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.PurityDiagonalBaseChangeCompared
import Sheaf.Paper.PurityDncInvariance
import Sheaf.Paper.PuritySectionInvariantIntrinsic
import Sheaf.Paper.VectorBundlePurity

/-! # Reduction of the canonical finite-coefficient purity maps

Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
thm-pur-finite-reduction-of-purity (blueprint: thm-pur-finite-reduction-of-purity).

## Main statements

- `finiteReductionOfPurity`: reduction of the canonical purity morphism.
- `finiteReductionOfSmoothTrace`: reduction of coefficient-valued smooth traces.
- `finiteReductionOfCompositionCoherence`: reduction of the full purity composite.
- `finiteReductionOfBaseChange`: reduction of the specified smooth exchange square.
- `finiteReductionOfAffineOrientation`: reduction of the supported-Kummer orientation.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
section Morphism
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Finite reduction takes the specified purity morphism to the specified purity
morphism over the smaller quotient, through the canonical six-operation comparisons.
There is no ramification-index divisibility or quotient-flatness hypothesis.
Source: blueprint thm-pur-finite-reduction-of-purity, displayed square
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: use bounded flat representatives to obtain the tensor, pullback, support,
shift and rank-one twist comparisons. The supported Cartier class reduces because
the finite Kummer sequences commute and the supported boundary is natural; its
adjoint gives the affine orientation at the smaller level. The deformation
localization triangles and their specialization maps commute with reduction, as
do zero-section duality and vector-bundle trace, so normalized diagonal orientation
reduces. The tensor transformation is the counit mate of the projection-formula
inverse; finite adjoint-mate compatibility makes it commute with reduction.
Substitute these identities into tau, tensor with the inverse diagonal orientation,
and theta defining gamma. This gives precisely the displayed equality. -/
theorem finiteReductionOfPurity (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    (P.finiteReduction m hm hmn X).map (P.smoothPurityMap f d K hK) ≫
        P.finiteReductionExceptionalComparison m hm hmn f d K hK =
      (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
        (P.finiteReductionSetting m hm).smoothPurityMap f d
          ((P.finiteReduction m hm hmn Y).obj K)
          (P.finiteReduction_preserves_ctf m hm hmn Y K hK) := by
  sorry

/-- Reduction preserves every coefficient-valued smooth trace, with the actual
compact-support and source comparisons on its domain.
Source: blueprint Step 6, trace paragraph
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: the trace is compact support of gamma followed by the exceptional counit.
Use naturality of the compact-support coefficient map to move reduced gamma
through it, apply finiteReductionOfPurity, and then apply the defining counit
identity of the exceptional coefficient comparison. The resulting composite is
the smaller-coefficient trace with exactly the source comparison displayed here. -/
theorem finiteReductionOfSmoothTrace (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    (P.finiteReduction m hm hmn Y).map (P.coefficientValuedSmoothTrace f d K hK) =
      P.finiteReductionCompactSupportComparison m hm hmn f
          ((P.compositionShiftedPullback f d).obj K) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
        (P.finiteReductionSetting m hm).coefficientValuedSmoothTrace f d
          ((P.finiteReduction m hm hmn Y).obj K)
          (P.finiteReduction_preserves_ctf m hm hmn Y K hK) := by
  sorry


/-- The coefficient-unit smooth trace reduces to the specified unit trace.
Source: blueprint Step 6, trace paragraph
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: specialize coefficient-valued trace compatibility to the coefficient unit.
Its finite-Tor amplitude is [0,0] and it is constructible. The explicit unit
presentation of smoothTrace agrees with that specialization by the uniqueness
of smoothPurityTensorMap. The scalar-unit map is the normalized rank-one tensor
comparison. Naturality in the coefficient input then gives the displayed formula. -/
theorem finiteReductionOfUnitSmoothTrace (d : ℕ) [SmoothOfRelativeDimension d f] :
    (P.finiteReduction m hm hmn Y).map (P.smoothTrace f d) ≫
        P.finiteReductionUnitComparison m hm hmn Y =
      P.finiteReductionCompactSupportComparison m hm hmn f
          ((P.compositionShiftedPullback f d).obj (P.coefficientUnit Y)) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          ((P.finiteReductionSourceComparison m hm hmn f d (P.coefficientUnit Y)).hom ≫
            ((P.finiteReductionSetting m hm).compositionShiftedPullback f d).map
              (P.finiteReductionUnitComparison m hm hmn Y)) ≫
        (P.finiteReductionSetting m hm).smoothTrace f d := by
  sorry

end Morphism
section Composition
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y Z : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [Z.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Z ↘ Spec (.of P.field.k))]
variable [IsSeparated (Z ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
variable (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]

/-- Reduction preserves the specified source identification in composition coherence.
Source: blueprint Step 6, composition paragraph
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: the source identification is assembled from ordered tensor powers, the
Koszul symmetry, shifts, pullback composition and root-line pullback. On bounded
flat models scalar extension preserves each of these canonical maps. In compatible
primitive-root charts the source coefficient comparisons are precisely the same
balancing maps, so the two displayed composites agree, including dimension zero. -/
theorem finiteReductionOfCompositionSource (K : Scheme.proEtaleDerivedCategory Z P.Ring) :
    (P.finiteReduction m hm hmn X).map
        (P.compositionSourceIdentification f g d e K).hom ≫
      (P.finiteReductionSourceComparison m hm hmn f d
        ((P.compositionShiftedPullback g e).obj K)).hom ≫
      (((P.finiteReductionSetting m hm).compositionShiftedPullback f d).map
        (P.finiteReductionSourceComparison m hm hmn g e K).hom) =
    (P.finiteReductionSourceComparison m hm hmn (f ≫ g) (d + e) K).hom ≫
      ((P.finiteReductionSetting m hm).compositionSourceIdentification f g d e
        ((P.finiteReduction m hm hmn Z).obj K)).hom := by
  sorry

/-- Reduction preserves the standing exceptional composition arrow itself.
Source: blueprint Step 6, composition paragraph
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: transpose both composites using the standing compact-support adjunctions.
Each exceptional comparison is characterized by its counit equation; each
composition arrow is the mate of compact-support composition. Coefficient change
preserves the proper/open compact-support compositor, and its counits paste to
epsilon_g after Rg_!(epsilon_f). Both transposes are therefore equal. Injectivity
of the relative Hom equivalences proves the stated equality. -/
theorem finiteReductionOfCompositionExceptional
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K) :
    (P.finiteReduction m hm hmn X).map (P.compositionExceptionalIso f g K hK).hom ≫
      P.finiteReductionExceptionalComparison m hm hmn f d
        ((P.compositionExceptional g).obj K) (P.compositionExceptional_ctf g e K hK) ≫
      ((P.finiteReductionSetting m hm).compositionExceptional f).map
        (P.finiteReductionExceptionalComparison m hm hmn g e K hK) =
    P.finiteReductionExceptionalComparison m hm hmn (f ≫ g) (d + e) K hK ≫
      ((P.finiteReductionSetting m hm).compositionExceptionalIso f g
        ((P.finiteReduction m hm hmn Z).obj K)
        (P.finiteReduction_preserves_ctf m hm hmn Z K hK)).hom := by
  sorry

/-- The entire three-arrow composition formula reduces to the formula with the
specified smaller-coefficient source and exceptional composition arrows.
Source: blueprint Step 6, composition paragraph
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: reduce the composition formula. The preceding source and exceptional
identities preserve its two outer comparison arrows. Apply the purity reduction
square to each purity arrow and naturality of the tensor/pullback comparison to
the middle pulled-back arrow. Cancellation of the invertible comparisons yields
exactly this three-arrow path over the smaller coefficient ring. -/
theorem finiteReductionOfCompositionCoherence
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K) :
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
          (P.finiteReduction_preserves_ctf m hm hmn Z K hK)).inv := by
  sorry
end Composition
section BaseChange
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X X' Y Y' : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
variable [Y.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X' ↘ Spec (.of P.field.k))]
variable [IsSeparated (X' ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y' ↘ Spec (.of P.field.k))]
variable (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
variable [u.IsOver (Spec (.of P.field.k))] [v.IsOver (Spec (.of P.field.k))]
variable [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
variable (sq : IsPullback u f' f v) (d : ℕ)
variable [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']

/-- Reduction preserves both specified vertical arrows in the smooth base-change square.
The base morphism v is arbitrary; all extra displayed properties of f' are its
Cartesian pullback properties, not restrictions on v.
Source: blueprint Step 6, base-change paragraph
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: for the first equality use the independent root charts. Their coefficient
normalization, exact shift comparison and ordinary pullback compositors commute
with coefficient extension on K-flat representatives, so the middle source arrow
is precisely the one at the smaller coefficient level. For the second equality,
substitute the literal purity composite defining both exchanges. Apply the purity
reduction square to f and f', naturality of the pullback coefficient comparison,
and the first equality. The inverse of an isomorphism reduces to the inverse
under these comparisons. This identifies the actual exchange arrow at level m,
and hence every edge of the smooth base-change square, without a condition on v. -/
theorem finiteReductionOfBaseChange (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
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
        (P.finiteReduction_preserves_ctf m hm hmn Y K hK)).hom) := by
  sorry
end BaseChange

/-- Finite reduction preserves the Kummer-normalized affine orientation itself.
The two comparisons are fixed independently by primitive-root and counit equations.
Source: blueprint finite-reduction statement, affine-orientation clause
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: realize the supported coordinate Kummer boundary in the ordinary derived
category. The scalar quotient sends its relative Kummer extension to the extension
at the smaller coefficient level, independently of the annihilating exponent.
Supported-boundary uniqueness identifies the reduced supported class. The standing
exceptional adjunction and the counit-normalized exceptional comparison identify
its reduced adjoint with the adjoint at the smaller level. Comparison pullback and
intrinsic realization preserve these composites, proving the displayed equation.
This covers every positive level, including ramified levels and equal indices. -/
theorem finiteReductionOfAffineOrientation
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))] :
    (P.finiteReduction m hm hmn Y).map (P.finiteReductionOrientation Y) ≫
      P.finiteReductionOrientationExceptionalComparison m hm hmn Y ≫
      ((P.finiteReductionSetting m hm).compositionExceptional
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).map
          (P.finiteReductionOrientationInputComparison m hm hmn Y).hom =
    P.finiteReductionUnitComparison m hm hmn Y ≫
      (P.finiteReductionSetting m hm).finiteReductionOrientation Y := by
  sorry

end WeilConjectures.PurityFiniteSetting
