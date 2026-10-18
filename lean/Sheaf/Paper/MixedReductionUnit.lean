/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.CompactSupportReductionTower

/-! # Normalized mixed reduction unit

Source: lem-fix-operation-reduction, tensor reassociation and completed comparison
(blueprint: def-weil-mixed-reduction-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open TensorProduct
namespace WeilConjectures

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section ScalarUnit
variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) (n : ℕ)

/-- The ordinary mixed-reduction unit, uniquely prescribed on sheafified tensors.
Source: lem-fix-operation-reduction, tensor reassociation paragraph
(blueprint: def-weil-mixed-reduction-unit).
Proof: send s tensor x to ι_n(s) tensor (1 tensor x). The projection identity
for integralCompletedScalarMap makes this balanced. It commutes with restrictions;
sheafification gives the transformation. Pure tensors locally generate, giving uniqueness. -/
theorem sfMixedReductionUnit_existsUnique :
    ∃! η : scalarReductionExtension l E W n ⟶
      integralOrdinaryScalar l E L ι W ⋙ scalarReductionExtension l L W n ⋙
        proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n),
      ∀ (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l E W n).obj.obj U) (x : M.val.obj U),
        (η.app M).val.app U (sfReductionTensor l E W n M U s x) =
          sfReductionTensor l L W n ((integralOrdinaryScalar l E L ι W).obj M) U
            ((integralScalarQuotientSheafMap l E L ι W n).hom.app U s)
            (integralOrdinaryTensorSection l E L ι W M U 1 x) := by
  sorry

/-- The actual mixed tensor unit, with no choice of a comparison isomorphism.
Source: lem-fix-operation-reduction, tensor reassociation paragraph
(blueprint: def-weil-mixed-reduction-unit). -/
def sfMixedReductionUnit := (sfMixedReductionUnit_existsUnique l E L ι W n).exists.choose

/-- The homotopy-level mixed unit, with the tensor composites explicitly associated.
Source: lem-fix-operation-reduction, tensor reassociation paragraph
(blueprint: def-weil-mixed-reduction-unit). -/
def sfMixedReductionUnitHomotopy :
    (scalarReductionExtension l E W n).mapHomotopyCategory (.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι W).mapHomotopyCategory (.up ℤ) ⋙
        (scalarReductionExtension l L W n).mapHomotopyCategory (.up ℤ) ⋙
          (proEtaleCoefficientRestrictScalars W
            (integralScalarQuotientMap l E L ι n)).mapHomotopyCategory (.up ℤ) :=
  letI : (scalarReductionExtension l L W n ⋙
      proEtaleCoefficientRestrictScalars W
        (integralScalarQuotientMap l E L ι n)).Additive := inferInstance
  letI : (integralOrdinaryScalar l E L ι W ⋙ scalarReductionExtension l L W n ⋙
      proEtaleCoefficientRestrictScalars W
        (integralScalarQuotientMap l E L ι n)).Additive := inferInstance
  NatTrans.mapHomotopyCategory (sfMixedReductionUnit l E L ι W n) (.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso
      (F := integralOrdinaryScalar l E L ι W)
      (G := scalarReductionExtension l L W n ⋙
        proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n))
      (Iso.refl _) (.up ℤ)).inv ≫
      Functor.whiskerLeft _ (Functor.mapHomotopyCategoryCompIso
        (F := scalarReductionExtension l L W n)
        (G := proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n))
        (Iso.refl _) (.up ℤ)).inv

/-- Localization of the tensor-unit map. The equation is on the whole homotopy
category, including both coordinates of every Roos complex; it is not a choice of
maps after evaluation of a derived inverse limit.
Source: lem-fix-operation-reduction, tensor reassociation paragraph
(blueprint: def-weil-mixed-reduction-unit).
Proof: ordinary finite free extension is exact, and restriction is exact. Derive
the ordinary mixed unit using the two universal left-derived tensor counits.
On K-flat complexes those counits are invertible, so the equation determines the
map there. K-flat resolutions and the localization universal property give existence,
naturality and uniqueness on all complexes. -/
theorem sfMixedReductionDerivedUnit_existsUnique :
    ∃! η : scalarReductionDerivedExtension l E W n ⟶
      integralOrdinaryDerivedScalar l E L ι W ⋙ scalarReductionDerivedExtension l L W n ⋙
        (proEtaleCoefficientRestrictScalars W
          (integralScalarQuotientMap l E L ι n)).mapDerivedCategory,
      ∀ P : HomotopyCategory (scalarReductionSource l E W) (.up ℤ),
        η.app (DerivedCategory.Qh.obj P) ≫
          (proEtaleCoefficientRestrictScalars W
            (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.map
            ((scalarReductionDerivedExtension l L W n).map
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactorsh.hom.app P) ≫
              (scalarReductionCounit l L W n).app
                (((integralOrdinaryScalar l E L ι W).mapHomotopyCategory (.up ℤ)).obj P)) ≫
          (proEtaleCoefficientRestrictScalars W
            (integralScalarQuotientMap l E L ι n)).mapDerivedCategoryFactorsh.hom.app
            (((scalarReductionExtension l L W n).mapHomotopyCategory (.up ℤ)).obj
              (((integralOrdinaryScalar l E L ι W).mapHomotopyCategory (.up ℤ)).obj P)) =
        (scalarReductionCounit l E W n).app P ≫
          DerivedCategory.Qh.map ((sfMixedReductionUnitHomotopy l E L ι W n).app P) := by
  sorry

/-- The derived unit is selected from a unique universally normalized transformation.
Source: lem-fix-operation-reduction, tensor reassociation paragraph
(blueprint: def-weil-mixed-reduction-unit). -/
def sfMixedReductionDerivedUnit :=
  (sfMixedReductionDerivedUnit_existsUnique l E L ι W n).exists.choose

/-- Complete the target of the ordinary tensor-unit map using the prescribed diagonal
Roos completion map. This retains its quotient augmentation and shifted cone coordinate.
Source: lem-fix-operation-reduction, completed comparison paragraph
(blueprint: def-weil-mixed-reduction-unit). -/
def sfMixedCompletedReductionUnit
    (K : DerivedCategory (scalarReductionSource l E W)) :
    (scalarReductionDerivedExtension l E W n).obj K ⟶
      (proEtaleCoefficientRestrictScalars W
        (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.obj
          ((scalarReductionDerivedExtension l L W n).obj
            ((integralScalarExtension l E L ι W).obj K)) :=
  (sfMixedReductionDerivedUnit l E L ι W n).app K ≫
    (proEtaleCoefficientRestrictScalars W
      (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.map
        ((scalarReductionDerivedExtension l L W n).map
          ((scalarCompletion l E L ι W).app K))
end ScalarUnit


end WeilConjectures
