/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-! # Uniqueness of the etale pure-tensor normalization

Source: Stacks Project, Cohomology on Sites, Tag 07A4.
(blueprint: lem-sfb-etale-constant-module-tensor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
universe z
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction
namespace CategoryTheory.ConstantModuleDerivedProjection

/-- A derived tensorator normalized by the geometric pure-tensor map agrees with the
published etale tensorator under the canonical exact/left-derived comparison.
Source: Stacks Tag 07A4, proof by flat-term K-flat representatives.
(blueprint: lem-sfb-etale-constant-module-tensor-normalization).

Proof: the ordinary monoidal identification identifies the tensorator with the
published ordinary etale inverse-image tensorator, including the canonical unit.
On cochain complexes this equality holds on
every degree-p,q summand of the direct-sum total tensor, including its signed
differential. The normalization hypothesis and the defining equation of the published
leftDerivedUpperStarTensorComparison therefore give the same square on flat-term
K-flat representatives. The exact/left-derived isomorphism identifies the two
localization counits. Cancel the invertible representative tensor and localization
maps. The constant-scalar tensor equivalence transports the resolving localization
of ring-sheaf modules to fixed-coefficient sheaves. Its two-variable faithfulness
extends the equality to all unbounded inputs. No projection map, derived adjunction,
scalar derived equivalence,
finite ring hypothesis, or boundedness assumption is used. The zero object, the
zero ring and the identity morphism satisfy the same representative calculation. -/
theorem etale_constant_module_tensor_normalization
    {X Y : AlgebraicGeometry.Scheme.{z}} (f : X ⟶ Y)
    (B : Type (z + 1)) [CommRing B]
    (d : GeometricData Y.smallEtaleTopology X.smallEtaleTopology B) (x : ExactData d)
    (t : FixedTensorData d)
    (hL : d.pullA = AlgebraicGeometry.Etale.upperStar (ModuleCat.{z + 1} B) f)
    (hm : HEq t.monoidal
      (inferInstance :
        (AlgebraicGeometry.Etale.upperStar (ModuleCat.{z + 1} B) f).Monoidal))
    (n : d.pullA.mapDerivedCategory.Monoidal)
    (hn : TensorNormalization (Fixed Y.smallEtaleTopology B) (Fixed X.smallEtaleTopology B)
      d.pullA t.monoidal n) :
    TensorSquare d.pullA.mapDerivedCategory
      (AlgebraicGeometry.Etale.upperStar (ModuleCat.{z + 1} B) f).leftDerivedFunctor
      (𝟭 _) (𝟭 _) n
      (AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal (ModuleCat.{z + 1} B) f)
      inferInstance inferInstance
      (Functor.mapDerivedCategoryNatIso (eqToIso hL) ≪≫
        (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{z + 1} B) f).symm) := by
  sorry

end CategoryTheory.ConstantModuleDerivedProjection
