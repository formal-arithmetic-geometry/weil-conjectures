/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.Paper.IntegralTwistBaseChange
public import Sheaf.Paper.IntegralAmbientOperationModels
public import Sheaf.Paper.PuritySourceTransports

/-! # Canonical positive coefficient-line comparisons

Source: main-20261015, def-coefficient-twists-detailed, completed tensor and
scheme pullback conventions (blueprint: def-sf-orientation-integral-line-comparisons).
The original coefficient lines are reexported. Their normalized inverse-image
maps are supplied for arbitrary scheme morphisms, as required by orientations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

/-- The inverse-image map of a positive completed line for an arbitrary base map.
Every local scalar and every compatible root is retained. Unlike the Frobenius
interface, this statement does not require the map of schemes to be invertible.
Source: base naturality in clause 1 (blueprint: def-sf-orientation-integral-line-comparisons).
Proof: use the projection-normalized completed coefficient map and root-limit map.
The integral inverse-image theorem identifies their tensor product with the first
line. Apply tensor pullback recursively. At degree zero use the coefficient map.
The indicated pure tensors generate locally, so the formulas determine every map.
The locally free rank-one comparisons are invertible on a pro-etale cover, hence
globally. This proof applies to every morphism and to the empty scheme. -/
theorem sfOrientationIntegralLineMaps_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! tau : ∀ d : ℕ,
      (FrobeniusCoefficientTwists.modulePull l E g).obj
        (FrobeniusCoefficientTwists.positiveLine l E Y d) ≅
          FrobeniusCoefficientTwists.positiveLine l E X d,
      ∀ (d : ℕ) (V : Y.ProEt)
        (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
          (Opposite.op V)) (x : Fin d → (purTwistZlOne Y l).obj.obj (Opposite.op V)),
        (tau d).hom.val.app (Opposite.op ((proEtaleBaseChange g).obj V))
          (FrobeniusCoefficientTwists.moduleSection l E g
            (FrobeniusCoefficientTwists.positiveLine l E Y d) V
            (FrobeniusCoefficientTwists.generator l E Y (Opposite.op V) a d x)) =
        FrobeniusCoefficientTwists.generator l E X
          (Opposite.op ((proEtaleBaseChange g).obj V))
          ((sfCompletedCoefficientMap l E g).hom.app (Opposite.op V) a) d
          (fun i ↦ FrobeniusCoefficientTwists.rootSection l g V (x i)) := by
  sorry

/-- The actual completed-module line map selected by its unique root formula.
Source: clause 1, pullback/twist comparison
(blueprint: def-sf-orientation-integral-line-comparisons). -/
def sfOrientationIntegralLineMaps
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    (FrobeniusCoefficientTwists.modulePull l E g).obj
      (FrobeniusCoefficientTwists.positiveLine l E Y d) ≅
        FrobeniusCoefficientTwists.positiveLine l E X d :=
  (sfOrientationIntegralLineMaps_existsUnique l E g).exists.choose d

/-- A positive Tate line with its even shift, in its one-term complex model.
Source: coefficient conventions, Lambda(d)[2d]
(blueprint: def-sf-orientation-integral-line-comparisons). -/
def sfOrientationIntegralComplex
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (d : ℕ) :
    CochainComplex (integralTowerModules l E X) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) (-2 * (d : ℤ))).obj
    (FrobeniusCoefficientTwists.positiveLine l E X d)

/-- Insert a pure root tensor into the only nonzero term of the shifted line.
Source: positive tensor powers and cohomological shifts
(blueprint: def-sf-orientation-integral-line-comparisons). -/
def sfOrientationIntegralComplexGenerator
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (d : ℕ) (U : X.ProEtᵒᵖ)
    (a : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
    (x : Fin d → (purTwistZlOne X l).obj.obj U) :
    ((sfOrientationIntegralComplex l E X d).X (-2 * (d : ℤ))).val.obj U :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) (-2 * (d : ℤ))
    (FrobeniusCoefficientTwists.positiveLine l E X d)).inv.val.app U
      (FrobeniusCoefficientTwists.generator l E X U a d x)

/-- The shifted line is still a flat-term K-flat representative.
Source: coefficient-line conventions (blueprint: def-sf-orientation-integral-line-comparisons).
Proof: each positive root line is locally free of rank one, including the unit
at zero. The complex is supported in one degree, so tensoring with it is an exact
line tensor followed by a shift. It therefore preserves acyclic complexes; every
term is either this flat line or zero. -/
theorem sfOrientationIntegralComplex_good
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (d : ℕ) :
    integralOperationsGoodComplex l E X (sfOrientationIntegralComplex l E X d) := by
  sorry

/-- Multiplication in the ordinary total tensor is fixed on every pure root tensor.
This includes all scalar factors; no trivialization of the root line is chosen.
Source: coefficient multiplicativity and tensor-shift convention
(blueprint: def-sf-orientation-integral-line-comparisons).
Proof: the total tensor of the two single complexes has only the summand
(-2d,-2e). Reassociate the two positive root powers, with scalar multiplication
at exponent zero. The ordinary tensor universal property makes this a sheaf map.
Its inverse splits the ordered list of roots after d entries; balancing identifies
the scalar factors. Both differentials vanish. The degree identity is
-2d-2e=-2(d+e), with no odd Koszul sign. The two maps are inverse on pure tensors,
which generate after sheafification. These generators also prove uniqueness. -/
theorem sfOrientationIntegralComplexProduct_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (d e : ℕ) :
    ∃! m : (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X)).obj
          (sfOrientationIntegralComplex l E X d, sfOrientationIntegralComplex l E X e) ≅
        sfOrientationIntegralComplex l E X (d + e),
      ∀ (U : X.ProEtᵒᵖ)
        (a b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
        (x : Fin d → (purTwistZlOne X l).obj.obj U)
        (y : Fin e → (purTwistZlOne X l).obj.obj U),
        HEq ((m.hom.f (-2 * (d : ℤ) + -2 * (e : ℤ))).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X)
            (sfOrientationIntegralComplex l E X d) (sfOrientationIntegralComplex l E X e)
            (-2 * (d : ℤ)) (-2 * (e : ℤ)) (-2 * (d : ℤ) + -2 * (e : ℤ)) rfl U
            (sfOrientationIntegralComplexGenerator l E X d U a x)
            (sfOrientationIntegralComplexGenerator l E X e U b y)))
          (sfOrientationIntegralComplexGenerator l E X (d + e) U (a * b)
            (Fin.addCases x y)) := by
  sorry

/-- The uniquely specified multiplication of the positive shifted line complexes.
Source: coefficient multiplicativity (blueprint: def-sf-orientation-integral-line-comparisons). -/
def sfOrientationIntegralComplexProduct
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (d e : ℕ) :=
  (sfOrientationIntegralComplexProduct_existsUnique l E X d e).exists.choose

/-- Completion of the ordinary tensor of two shifted root lines changes no object.
The actual operation unit, including its zero shifted-product component, is retained.
Source: completed tensor in the coefficient conventions
(blueprint: def-sf-orientation-integral-line-comparisons).
Proof: the ordinary tensor is a single locally free rank-one complete line in
degree -2(d+e), by the preceding multiplication. Its finite quotient tower has
surjective transitions, and its inverse limit is the original completed line.
The Roos unit is therefore a quasi-isomorphism. The normalized tensorTowerIso
identifies that unit with tensorOperationUnit, preserving both cone coordinates.
Applying derived localization makes this very map invertible. -/
theorem sfOrientationIntegralTensorUnit_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (d e : ℕ) :
    IsIso (DerivedCategory.Q.map (IntegralAmbient.tensorOperationUnit l E X
      (sfOrientationIntegralComplex l E X d) (sfOrientationIntegralComplex l E X e))) := by
  sorry

/-- Actual multiplication of completed derived root lines, calculated by the
specified good representatives and the specified tensor-operation augmentation.
Source: completed tensor and Tate multiplication
(blueprint: def-sf-orientation-integral-line-comparisons). -/
def sfOrientationIntegralDerivedProduct
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (d e : ℕ) :
    (integralCompletedTensor l E X).obj
      (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d),
        DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X e)) ≅
      DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X (d + e)) :=
  (integralCompletedTensorComparison l E X).app
    (⟨sfOrientationIntegralComplex l E X d, sfOrientationIntegralComplex_good l E X d⟩,
      ⟨sfOrientationIntegralComplex l E X e, sfOrientationIntegralComplex_good l E X e⟩) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (IntegralAmbient.tensorOperationUnit l E X
      (sfOrientationIntegralComplex l E X d) (sfOrientationIntegralComplex l E X e)))
        (sfOrientationIntegralTensorUnit_isIso l E X d e)).symm ≪≫
    DerivedCategory.Q.mapIso (sfOrientationIntegralComplexProduct l E X d e)

/-- The specified pullback augmentation is invertible on each shifted root line.
Source: completed pullback in the coefficient conventions
(blueprint: def-sf-orientation-integral-line-comparisons).
Proof: the ordinary module inverse image of the line is the corresponding
completed root line on the source, by the scalar/root comparison. Its quotient
tower therefore reconstructs it. On the single flat representative the finite
pullback tower computes precisely these quotients. Its surjective transitions
have zero higher inverse limit. The root projections identify the first Roos
coordinate of the published augmentation with the quotient units; its second
coordinate is zero. Thus its localization is an isomorphism. -/
theorem sfOrientationIntegralPullUnit_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    IsIso (DerivedCategory.Q.map
      ((FrobeniusCoefficientTwists.pullbackAugmentation l E g).app
        (sfOrientationIntegralComplex l E Y d))) := by
  sorry

/-- The actual completed derived pullback comparison for the shifted root line.
Source: coefficient conventions, arbitrary scheme pullback
(blueprint: def-sf-orientation-integral-line-comparisons). -/
def sfOrientationIntegralDerivedPull
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    (integralDerivedPullback l E g).obj
        (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E Y d)) ≅
      DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d) :=
  (integralDerivedPullbackComparison l E g).app
      ⟨sfOrientationIntegralComplex l E Y d, sfOrientationIntegralComplex_good l E Y d⟩ ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map
      ((FrobeniusCoefficientTwists.pullbackAugmentation l E g).app
        (sfOrientationIntegralComplex l E Y d)))
        (sfOrientationIntegralPullUnit_isIso l E g d)).symm ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (FrobeniusCoefficientTwists.modulePull l E g) (.up ℤ) (-2 * (d : ℤ))).app
        (FrobeniusCoefficientTwists.positiveLine l E Y d)) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.single _ (.up ℤ) (-2 * (d : ℤ))).mapIso
        (sfOrientationIntegralLineMaps l E g d))

end WeilConjectures
