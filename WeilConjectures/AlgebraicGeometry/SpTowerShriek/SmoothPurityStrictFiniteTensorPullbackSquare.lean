/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteTensorPullbackSquareDescent
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteTensorPullbackSquareRepresentatives

/-! The tensor and inverse-image square in prescribed finite coordinates. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerShriek

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

/-- The pinned tensor comparison commutes with the prescribed finite inverse-image
comparison and the normalized level tensor comparison.
Source: blueprint operations proof (2), tensor comparison on signed total representatives.
(blueprint: new-lem-sp-strict-finite-tensor-pullback-square).

Proof: restrict to flat-term K-flat representatives of M and N. The scalar unit
and the sectionwise inverse-image unit identify the two ordinary tensor arrows
on a balanced pure tensor. The finite tensor pin identifies their realization
with the two prescribed pure-tensor arrows. Evaluate this equality in each
bidegree and use the coproduct injection equations to obtain the equality on
the signed total complex; both routes carry the same Koszul differential.
The pin's model equation identifies its derived tensor arrow, while
ComparisonFiniteTensorRepresentative identifies the target representative arrow
with the given semilinear model. The normalized tensorPullback condition gives
exactly the level inverse-image tensor arrow. Localize the chain square and
cancel the exact/left-derived comparison isomorphisms in comparisonFinitePull.
Finally use flat-term K-flat replacements in both variables and naturality to
extend the equality to M and N. All constructions use universal properties,
so also apply to the zero ring, empty schemes and zero complexes. -/
theorem strictFiniteTensorPullbackSquare (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    (hpin : (∀ (T : Scheme.{u}) (n : ℕ),
    ∃ e : SheafOfModules.OpenTensorNormalization.FiniteRealization.{u}
        (ULift.{u + 1, u} (R l E n)) T (B l E T n)
        (comparisonFiniteConstantSection l E T n),
    ∃ t : AlgebraicGeometry.Scheme.ProjectionRestriction.TensorModel.{u} (B l E T n),
    ∃ d : SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
        (ULift.{u + 1, u} (R l E n)) T ⋙ e.derived ≅
          (e.derived.prod e.derived) ⋙ t.functor,
      HEq e.equivalence (sfIntrinsicModuleEquivalence T (R l E n)) ∧
      HEq e.underlying (comparisonFiniteUnderlying l E b T n) ∧
      HEq t.functor (comparisonLevelTensor l E b T n) ∧
      ComparisonFiniteTensorRepresentative l E b T n t ∧ HEq d (tensor T n) ∧
      Nonempty (@SheafOfModules.OpenTensorNormalization.FiniteTensorPin.{u}
        (ULift.{u + 1, u} (R l E n)) _ _ T (B l E T n)
        (comparisonFiniteConstantSection l E T n) e t d))) :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
      (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))),
      (comparisonFiniteRealization l E b X n).map
          (((leftDerivedUpperStarTensorComparison
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).app M).app N) ≫
        (tensor X n).hom.app
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
              f).leftDerivedFunctor.obj M,
            (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
              f).leftDerivedFunctor.obj N) ≫
        (comparisonLevelTensor l E b X n).map
          (Prod.mkHom ((comparisonFinitePull l E b f n).hom.app M)
            ((comparisonFinitePull l E b f n).hom.app N)) =
      (comparisonFinitePull l E b f n).hom.app
          ((SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
            (ULift.{u + 1, u} (R l E n)) Y).obj (M, N)) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) f).map
          ((tensor Y n).hom.app (M, N)) ≫
        (levels.tensorPullback f n).hom.app
          ((comparisonFiniteRealization l E b Y n).obj M,
            (comparisonFiniteRealization l E b Y n).obj N) := by
  exact @strictFiniteTensorPullbackSquare_descent l _ E _ _ _ b o levels tensor
    (fun {X Y} f n P Q hP hQ ↦
      strictFiniteTensorPullbackSquare_representatives l E b o levels tensor hpin
        f n P Q hP hQ)

end AlgebraicGeometry.ProEtale.SpTowerShriek
