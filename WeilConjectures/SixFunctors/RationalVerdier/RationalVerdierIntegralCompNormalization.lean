/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.Completed.CompletedScalarCanonicalAssociatorFormula

/-! # Identification of the integral scalar associator representatives

Source: blueprint thm-coef-rational-verdier, proof step 7
(blueprint: lem-coef-rational-verdier-composition-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The intrinsic integral scalar associator is the prescribed finite-extension map.
Source: blueprint thm-coef-rational-verdier, proof step 7, composition normalization
(blueprint: lem-coef-rational-verdier-composition-normalization).

Proof: expand the intrinsic scalar associator and the finite-extension composition map.
The completion comparison maps, completed coefficient tensor associator, and their
inverses are the same three factors in both constructions; naturality identifies the
component on each integral constructible object. -/
theorem integral_comp_normalization_bridge
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (H : Type u) [Field H] [Algebra (Padic l) H] [FiniteDimensional (Padic l) H]
    (i : F →ₐ[Padic l] G) (j : G →ₐ[Padic l] H)
    (K : sfIntegralConstructibleCategory l F X) :
    (sfIntegralScalarComp l F G i X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) H j).hom.app K =
      ObjectProperty.homMk
        (X := (integralScalar l X G H j).obj ((integralScalar l X F G i).obj K))
        (Y := (integralScalar l X F H (j.comp i)).obj K)
        (IntegralFiniteExtension.comp l F G i X H j K.obj K.property.1).hom := by
  apply ObjectProperty.hom_ext
  exact completedScalarCanonicalAssociatorFormula l F G H i j X K

end WeilConjectures.RationalVerdier
