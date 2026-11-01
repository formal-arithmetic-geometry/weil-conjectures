/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierIntegralCompNormalization

/-! # Integral normalization of the rational Verdier associator

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

/-- The rational scalar associator has the prescribed integral normalization.
Source: blueprint thm-coef-rational-verdier, proof step 7, composition clause
(blueprint: lem-coef-rational-verdier-composition-normalization).

Proof: localize the normalized integral tensor associator. The object formula for
rational scalar extension identifies its source and target with the localized
integral representatives, while the integral comparison's composition map is
exactly the normalized component. This gives the displayed heterogeneous equality
on every integral representative. -/
theorem rational_scalar_comp_normalization
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (H : Type u) [Field H] [Algebra (Padic l) H] [FiniteDimensional (Padic l) H]
    (i : F →ₐ[Padic l] G) (j : G →ₐ[Padic l] H) :
    ∃ a : scalar l X F G i ⋙ scalar l X G H j ≅ scalar l X F H (j.comp i),
      ∀ K : sfIntegralConstructibleCategory l F X,
        HEq (a.hom.app ((sfRationalConstructibleLocalization l F X).obj K))
          ((sfRationalConstructibleLocalization l H X).map
            (ObjectProperty.homMk
              (X := (integralScalar l X G H j).obj ((integralScalar l X F G i).obj K))
              (Y := (integralScalar l X F H (j.comp i)).obj K)
              (IntegralFiniteExtension.comp l F G i X H j K.obj K.property.1).hom)) := by
  let hzero : l ≠ 0 := Nat.Prime.ne_zero (Fact.out : l.Prime)
  obtain ⟨a, ha⟩ := sfRationalScalarComp_existsUnique l F G i X 0 hzero H j
  refine ⟨a, ?_⟩
  intro K
  have hcomp := ha.1 ((sfRationalConstructibleLocalization l F X).obj K)
  have hbridge := integral_comp_normalization_bridge (l := l) (X := X) F G H i j K
  have hbridge' :
      (sfIntegralScalarComp l F G i X 0 hzero H j).hom.app
          ((sfRationalConstructibleLocalization l F X).obj K).obj =
        ObjectProperty.homMk
          (X := (integralScalar l X G H j).obj ((integralScalar l X F G i).obj K))
          (Y := (integralScalar l X F H (j.comp i)).obj K)
          (IntegralFiniteExtension.comp l F G i X H j K.obj K.property.1).hom := by
    simpa only [sfRationalConstructibleLocalization, ScalarLocalization.localization]
      using hbridge
  rw [hbridge'] at hcomp
  exact hcomp

end WeilConjectures.RationalVerdier
