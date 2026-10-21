/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.OrientationCoefficientTwists
public import Sheaf.Paper.FiniteTateSiteDescent

/-! Canonical finite quotient and realization of the completed root lines.
Source: def-coefficient-twists-detailed
(blueprint: def-sf-orientation-finite-reduction-comparisons). -/
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

/-- The finite positive root line in its single-complex model.
Source: finite coefficient convention
(blueprint: def-sf-orientation-finite-reduction-comparisons). -/
def sfOrientationFiniteComplex
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m d : ℕ) :=
  (HomologicalComplex.single _ (.up ℤ) (-2 * (d : ℤ))).obj
    (finiteCoefficientTwist l E X m (d : ℤ))

/-- The scalar-adjunction transpose of a quotient map on a shifted root line.
Exact restriction, its single-complex comparison and its derived factors are
used literally. Source: coefficient reduction comparison
(blueprint: def-sf-orientation-finite-reduction-comparisons). -/
def sfOrientationFiniteQuotientTranspose
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m d : ℕ)
    (q : integralTwistLine l E X (d : ℤ) ⟶
      (scalarReductionRestriction l E X m).obj (finiteCoefficientTwist l E X m (d : ℤ))) :=
  letI := (scalarReductionRestriction_exact l E X m).1
  letI := (scalarReductionRestriction_exact l E X m).2
  let F := scalarReductionRestriction l E X m
  DerivedCategory.Q.map
    ((HomologicalComplex.single _ (.up ℤ) (-2 * (d : ℤ))).map q) ≫
    (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ)
        (-2 * (d : ℤ))).app (finiteCoefficientTwist l E X m (d : ℤ)))).inv ≫
    (F.mapDerivedCategoryFactors.app (sfOrientationFiniteComplex l E X m d)).inv

/-- The normalized derived quotient of every shifted positive root power.
The auxiliary ordinary arrows are specified by their coefficient, first-root,
and tensor formulas; they are not extra input or freely chosen data.
Source: finite reduction convention (blueprint: def-sf-orientation-finite-reduction-comparisons).
Proof: at zero use the completed coefficient projection. At one use the ordinary
scalar-extension unit of the first root line. Tensor these semilinear maps to
obtain all higher powers. The displayed pure tensors generate locally, so the
ordinary arrows are unique. Derive on the flat one-term root representatives:
the scalar adjunction gives the unique derived maps with those transposes.
On a local rank-one trivialization these are coefficient quotient isomorphisms.
Isomorphy descends, and uniqueness follows from the adjunction bijection and
from generation by all displayed root tensors. -/
theorem sfOrientationFiniteReduction_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (m : ℕ) :
    ∃! t : ∀ d : ℕ, (scalarReductionDerivedExtension l E X m).obj
      (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d)) ≅
        DerivedCategory.Q.obj (sfOrientationFiniteComplex l E X m d),
      ∃ q : ∀ d : ℕ, integralTwistLine l E X (d : ℤ) ⟶
        (scalarReductionRestriction l E X m).obj (finiteCoefficientTwist l E X m (d : ℤ)),
        (∀ (W : X.ProEtᵒᵖ)
          (a : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj W),
          (q 0).val.app W a =
            (completedIntegralCommRingProjectionUnrestricted l E X m).hom.app W a) ∧
        (∀ (W : X.ProEtᵒᵖ) (x : (purTwistIntegralOne X l E).val.obj W),
          (q 1).val.app W x =
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (integralCoefficientSheaf l E X m).obj)).unit.app
                (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u+1, u+1, u+1}
                  (purTwistIntegralQuotient X l E m) (purTwistIntegralOne X l E))).app W)
              ((1 : (integralCoefficientCommRingSheaf l E X m).obj.obj W)
                ⊗ₜ[_, ((purTwistIntegralQuotient X l E m).hom.app W).hom] x)) ∧
        (∀ (d : ℕ) (W : X.ProEtᵒᵖ)
          (x : (integralTwistLine l E X ((d + 1 : ℕ) : ℤ)).val.obj W)
          (y : (purTwistIntegralModule X l E).val.obj W),
          (q (d + 2)).val.app W
            (SheafOfModules.siteSheafTensorTmul
              (A := completedIntegralCommRingSheafUnrestricted l E X)
              (integralTwistLine l E X ((d + 1 : ℕ) : ℤ))
              (purTwistIntegralModule X l E) W x y) =
          SheafOfModules.siteSheafTensorTmul
            (A := integralCoefficientCommRingSheaf l E X m)
            (finiteCoefficientTwist l E X m ((d + 1 : ℕ) : ℤ))
            (finiteCoefficientTwist l E X m (1 : ℤ)) W
            ((q (d + 1)).val.app W x) ((q 1).val.app W y)) ∧
        ∀ d : ℕ,
          ((derivedScalarExtensionRestrictionAdjunction l E X m).choose.homEquiv _ _)
            (t d).hom =
          sfOrientationFiniteQuotientTranspose l E X m d (q d) := by
  sorry

/-- The actual finite reduction, selected by its unique root-quotient transpose.
Source: coefficient convention (blueprint: def-sf-orientation-finite-reduction-comparisons). -/
def sfOrientationFiniteReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (m d : ℕ) :=
  (sfOrientationFiniteReduction_existsUnique l E X m).exists.choose d

/-- Use the published positive-quotient finiteness witness.
Source: coefficient conventions (blueprint: def-sf-orientation-finite-reduction-comparisons). -/
instance sfOrientationQuotientFinite
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (m + 1)) :=
  Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))


end WeilConjectures
