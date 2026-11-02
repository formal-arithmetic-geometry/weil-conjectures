/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData

import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerGeometricComposition
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerPullTensorConstructible
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerNormalized
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
import WeilConjectures.CategoryTheory.ScalarHomTensor.ScalarHomTensorComparison
import WeilConjectures.CategoryTheory.Tensor.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.SixFunctors.Supporting.SemilinearTotalTensorEvaluation
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryInverseSystemKFlat
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemsExistence
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.Picard.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import WeilConjectures.Algebra.Homology.SequenceCoinduced.SystemCoinducedAdjunction
import WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarTensorSection
import WeilConjectures.CategoryTheory.Ringed.RingedScalarTensorMonoidal
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import WeilConjectures.SmoothPurity.CochainCompositeHom
import WeilConjectures.SixFunctors.Coefficient.CoefficientMonoidalSquareUnit
import WeilConjectures.SmoothPurity.CochainInverseComparison
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Sites.CoverPreserving
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.AlgebraicGeometry.Tensor.TensorComparisonModelPreservesFlat
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.ProperBaseChange.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedKFlatModel.RingedKFlatNativeModelIdentification
import WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ExactDerivedMonoidalConstruction
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.ProperBaseChange.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement

/-!
# Statement of the integral compactly supported direct-image tower

This module records the current short statement of
`det-sp-integral-direct-image-tower`.  The standing coefficient, pro-etale,
constructibility, compactification, derived push-pull, tensor, and lower-shriek
notions are the canonical declarations imported from the dependency modules.
The bundled `Presentation` supplies the construction-only reduction tower and the
varying-coefficient tower operations.  The imported current reduction statement
`sp_reduction_tower_integral_heart_statement` supplies normalization unconditionally and
constructibility in the separated finite-type integral-heart setting over a field
where `l` is invertible. Its comparison through the exact internal/section equivalence
transports these properties to the same construction. The fields in the
conclusion spell out respectively the normalized image tower and its `2*d` Tor widening, the
compactification-independent reconstruction and finite reductions, and the
pullback/projection-formula assertions.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction-direct-image.md
(blueprint: det-sp-integral-direct-image-tower).

The proof is postponed as the node proof requires the reconstruction,
compactification coherence, and complete projection-mate descent results.  Its steps
are: first obtain the construction and normalized/constructible consequences from
`sp_reduction_tower_integral_heart_statement`, then apply the finite compactification
comparisons and the canonical tower reconstruction to obtain the normalized image,
Tor widening, inverse-limit comparison, finite reductions, and compactification
independence; finally apply pullback/tensor constructibility and the tower
projection mates, transporting their isomorphisms through the reconstruction units.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/--
The normalized constructible tower, integral inverse-limit reconstruction,
compactification independence, pullback reduction, and projection formula for
compactly supported direct image.

The first conjunct for each `M` is clause (1): `spNormalizedConstructibleTorTowers`
records normalization and constructibility, while the displayed
`Scheme.HasProEtaleTorAmplitude` bound is exactly the input interval with `2*d`
added.  The `CanonicalTowerComparison`, `reconstruction`, and `finiteBaseChange`
fields in clause (2) are the canonical comparison with the total derived inverse
limit and its finite reductions; the natural isomorphisms `φ` satisfy identity,
cocycle, and common-refinement independence.  Clause (3) is represented by the
canonical `pull` and `tensor` functors together with the two projection mates,
whose `IsIso` fields give the stated projection formula after transport to the
integral category.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction-direct-image.md
(blueprint: det-sp-integral-direct-image-tower).

Proof, following the current blueprint paragraphs (1)--(3):
1. Use the current reduction theorem on X and Y. The standing finite-type schemes
are separated of finite type over k, and l is a unit in k. The integral-heart
proof works over any such field, as recorded by its Q42 general-field audit.
`Presentation.reduction` is this theorem's construction. Its condensed-source
functor and internal/section comparison transport normalized constructibility
and the common finite-Tor bounds to the displayed reduction.
Apply tower shriek evaluation and the uniform bound to widen the upper bound by
2d. The finite direct-image comparison identifies the actual image transitions
with the invertible source reductions, proving normalized constructibility.
2. The integral-model criterion makes M complete. Commute open extension and
proper direct image with the scalar-restricted total limit, retaining the
canonical projections. The normalized equivalence and counit identify the
resulting reconstruction with the completion unit, and give both the whole-tower
and finite reduction comparisons. Apply geometric calculus and the finite
proper/open comparisons to the strict tower, then R lim and conjugation by
reconstruction, to get common-refinement independence, identity and cocycle.
3. Pullback and tensor preserve bounded constructibility; K-flat scalar comparison
gives their actual reductions. Apply the tower projection formula to red_X M and
red_Y K. Reconstruct M tensor f* K as in step 2 and use tensor closure for the
other endpoint. The normalized equivalence gives invertibility of both actual
completion units. Complete projection-mate descent identifies the actual integral
proper and inverse open mates with the limits of these tower mates, giving the
projection formula with both endpoints in Dbc. -/
theorem integral_direct_image_tower_statement :
    ∀ s : Presentation l E,
    ∃ (q : ReductionGeometry l E s) (hq : OpenReductionIsIso l E s q),
    ∃ L : ∀ T : Scheme.{u}, Limit l E s T,
    ∀ (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
      (X Y : Scheme.{u}) [X.Over (Spec (.of k))]
      [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
      (d : ℕ) [SmoothOfRelativeDimension d f],
    (∃ φ : ∀ c₁ c₂ : Compactification f,
        (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙ shriek l E c₁ ≅
          (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙ shriek l E c₂,
      (∀ c : Compactification f, φ c c = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : Compactification f, φ c₁ c₂ ≪≫ φ c₂ c₃ = φ c₁ c₃) ∧
      ∀ (c₁ c₂ : Compactification.BoundaryCompactification f)
        (r : Compactification.DenseBoundaryCompactification f)
        (h₁ : r.obj ⟶ c₁) (h₂ : r.obj ⟶ c₂) (M : Constructible l E X),
        (φ c₁.obj.obj c₂.obj.obj).hom.app M ≫
          CondensedRing.compactificationRefinementComponent (spIntegralCondensed l E) h₂ M.obj =
        CondensedRing.compactificationRefinementComponent (spIntegralCondensed l E) h₁ M.obj) ∧
    ∀ c : Compactification f,
      ∃ _v : CanonicalTowerComparison l E s q hq c,
      (∀ M : Constructible l E X,
        spNormalizedConstructibleTorTowers l E Y (s.towers Y)
          (imageTower l E s c M.obj) ∧
        (∀ a b : ℤ, a ≤ b →
          DerivedCategory.torAmplitudeIn _ a b M.obj → ∀ n : ℕ,
          Scheme.HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
            (imageLevel l E s c M.obj n) a (b + 2 * d)) ∧
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          ((shriek l E c).obj M.obj) ∧
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          ((lim l E s Y (L Y)).obj
            (imageTower l E s c M.obj)) ∧
        IsIso (reconstruction l E s c (L Y) q hq M) ∧
        ∀ n : ℕ, IsIso (finiteBaseChange l E s q hq c M.obj n)) ∧
      (∀ K : Constructible l E Y,
        constantModelBoundedConstructible (spIntegralCondensed l E) X
          ((pull l E f).obj K.obj)) ∧
      ∀ (M : Constructible l E X) (K : Constructible l E Y),
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          ((shriek l E c).obj
            (((tensor l E X).obj M.obj).obj ((pull l E f).obj K.obj))) ∧
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          (((tensor l E Y).obj ((shriek l E c).obj M.obj)).obj K.obj) ∧
        IsIso (properProjection l E c M.obj K.obj) ∧
        IsIso (compactOpenProjection l E c M.obj K.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
