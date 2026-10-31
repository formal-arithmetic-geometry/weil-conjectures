/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.Coordinates.IntegralProjectionCoordinateData
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralProjectionProperFactorReduction
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralProjectionOpenFactorReduction

/-! # The coefficient square of one compactification projection

Source: prop-sf-pf-coherence.proof.md, the proper counit/open projection construction;
integral compactification-system realization, generator comparison.
(blueprint: lem-sf-integral-projection-reduction-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification
open IntegralSystemRealization

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus Coordinates.sourceMap Coordinates.targetMap
  ProjectionFactors.middleMap ProjectionFactors.first ProjectionFactors.second

/-- One projection commutes with the explicitly constructed coefficient maps.
No refinement and no choice of endpoint comparisons occurs in this statement.

Source: prop-sf-pf-coherence.proof.md, proper-counit/open projection construction;
integral compactification-system realization, steps 3--5.
(blueprint: lem-sf-integral-projection-reduction-normalization).

Proof: expand compactificationProjection into the proper projection mate, normalized
open tensor isomorphism and inverse pullback compositor. Expand projectionComponent
using compactSupportNormalization and openProjectionNormalization in the supplied
datum. Compute the coefficient square for the proper factor by the proper
pull/direct Hom bijection: both transposes are the tensor comparison followed by
the counit tensored with the identity. The datum's tensorPullback normalization
identifies the comparison with the prescribed completed tensor comparison.
For the open factor, transpose the inverse tensor map under extension by zero;
the normalized open unit and integralOpenTensorPullbackNormalization identify the
two transposes. The actual ordinary-to-completed comparisons are fixed by the
completion units, so their coefficient maps are the ones used in tensorReductionIso
and pullReduction. Paste these squares, whiskering by the outer proper image.
Naturality cancels the intervening inverse comparisons, and the adjunction triangle
identifies the remaining support coefficient map with supportReduction, defined
as the transpose of supportValue inverse. This is exactly sourceMap followed by
the system projection on one side, and reduction of projectionComponent followed
by targetMap on the other. The calculation is on the simultaneous strict quotient
models before localization, retaining all quotient transitions; no arbitrary map
is reconstructed from its evaluated finite arrows. Integral residue Tor and the
finite-Tor assumption supply common bounds whenever a complete comparison is
inverted. The calculation also includes identity opens, empty opens and zero inputs. -/
theorem integralProjectionReductionNormalization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left)
    (hL : finiteTorConstructibleIntegral C.l E Y.obj.left L.obj) :
    Coordinates.sourceMap D C E S.higher hl o z f c K L ≫
        compactificationProjection C.l E o z.compositors z.openComparisons c
          ((calculus C.l E X.obj.left).reduction.obj K.obj)
          ((calculus C.l E Y.obj.left).reduction.obj L.obj) =
      (calculus C.l E Y.obj.left).reduction.map
        (((S.higher.integralExchange (identitySquare f c)).projectionComponent K L).hom) ≫
          Coordinates.targetMap D C E S.higher hl o z f c K L := by
  let A := S.higher.integralExchange (identitySquare f c)
  let R := (calculus C.l E Y.obj.left).reduction
  have hp := integralProjectionProperFactorReduction D C E n hn S hl o z f c K L hL
  have hj := integralProjectionOpenFactorReduction D C E n hn S hl o z f c K L hL
  change Coordinates.sourceMap D C E S.higher hl o z f c K L ≫
      (ProjectionFactors.systemFirst D C E o f c
        ((calculus C.l E X.obj.left).reduction.obj K.obj)
        ((calculus C.l E Y.obj.left).reduction.obj L.obj) ≫
      ProjectionFactors.systemSecond D C E o z f c
        ((calculus C.l E X.obj.left).reduction.obj K.obj)
        ((calculus C.l E Y.obj.left).reduction.obj L.obj)) = _
  have hf : (ProjectionFactors.first A K L).hom ≫
      (ProjectionFactors.second A K L).hom = (A.projectionComponent K L).hom :=
    congrArg (fun v ↦ v.hom) (ProjectionFactors.factorization A K L).symm
  exact ProjectionFactors.paste R
    (ProjectionFactors.first A K L).hom (ProjectionFactors.second A K L).hom
    (A.projectionComponent K L).hom
    (Coordinates.sourceMap D C E S.higher hl o z f c K L)
    (ProjectionFactors.systemFirst D C E o f c
      ((calculus C.l E X.obj.left).reduction.obj K.obj)
      ((calculus C.l E Y.obj.left).reduction.obj L.obj))
    (ProjectionFactors.systemSecond D C E o z f c
      ((calculus C.l E X.obj.left).reduction.obj K.obj)
      ((calculus C.l E Y.obj.left).reduction.obj L.obj))
    (ProjectionFactors.middleMap D C E n hn S hl o z f c K L)
    (Coordinates.targetMap D C E S.higher hl o z f c K L) hp hj hf

end WeilConjectures.FixProjectionCompactification
