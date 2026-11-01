/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData

/-! # Scalar naturality of the completed pullback unit

Source: Bhatt--Scholze, Sections 3.5 and 6.5, Lemmas 6.5.9 and 6.8.2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  Scheme.coefficientProEtaleDirectRingMap WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.PrimitiveCounit.ringMap
namespace WeilConjectures.CompletedUnitPullback
attribute [local irreducible] calculus systemUnit systemObject systemMap systemMultiplication
  finiteMultiplication rationalObject integralObject rationalSource modelUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The completed geometric unit arrow commutes with the normalized coefficient
transport to the canonical small model.

Source: Bhatt--Scholze, Lemmas 6.5.9 and 6.8.2; the final paragraph of step 6 of
lem-pur-completed-unit-pullback-tower.
(blueprint: lem-pur-completed-unit-scalar-naturality).

Proof: compute both integral pullback-unit composites on the regular flat-term
K-flat complex. At every quotient, the scalar/pullback comparison is the balanced
tensor associator. On a generator b tensor (c tensor a), both composites multiply
the structural images of b,c,a in the target quotient ring. The same calculation
commutes with the actual quotient transitions, so it is an equality of strict
system maps. The normalized scalar-unit inverse has the actual quotient
projections and zero shifted Roos coordinate. Functoriality of the normalized
Roos construction therefore preserves this whole-system equality and identifies
its unit maps with the augmentation and multiplication composites specified in
Core.unit_formula. Coherent reduction and the adjunction triangles identify these
composites with Core.unit, independently of the chosen presentations. Applying
raw rationalization gives v tensor 1 on each arrow. Its specified unchanged-object
comparisons are rationalSource and modelUnit, while the normalized scalar/pullback
comparison is rationalPullbackScalarComparison. Substituting these comparisons
yields exactly the displayed square. The calculation includes the identity
extension and ramified coefficient rings; it never identifies completion with
the discrete constant sheaf. -/
theorem completedUnitScalarNaturality (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    (core : Core P.coefficients.l P.extension f)
    (model : Core P.coefficients.l (coefficientModel P) f) :
    (modelScalar P X).map (rationalMap P.coefficients.l P.extension f
        core.admissibleX.1.1 core.admissibleY.1.1 core.unit.hom) ≫
        (modelUnit P X core.admissibleX.1.1 model.admissibleX.1.1).hom =
      (rationalPullbackScalarComparison P.coefficients.l P.extension (coefficientModel P)
        (modelEmbedding P) f).hom.app
          (rationalObject P.coefficients.l P.extension Y core.admissibleY.1.1) ≫
        (rationalDerivedPullback P.coefficients.l (coefficientModel P) f).map
          (modelUnit P Y core.admissibleY.1.1 model.admissibleY.1.1).hom ≫
        rationalMap P.coefficients.l (coefficientModel P) f
          model.admissibleX.1.1 model.admissibleY.1.1 model.unit.hom
    := by
  sorry

end WeilConjectures.CompletedUnitPullback
