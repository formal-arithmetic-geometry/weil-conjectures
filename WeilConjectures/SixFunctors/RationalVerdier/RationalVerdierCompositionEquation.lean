/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierIntegralCocycle
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierLocalizedComposition

/-! # Associator equation for rational Verdier comparisons

Source: blueprint thm-coef-rational-verdier, proof step 7, composition clause
(blueprint: lem-coef-rational-verdier-composition-equation).
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

/-- The canonical rational associator satisfies the normalized Verdier comparison equation.
Source: blueprint thm-coef-rational-verdier, proof step 7, composition clause
(blueprint: lem-coef-rational-verdier-composition).

Proof: first use `integral_comparison_cocycle` for the three ordinary presentations,
then localize the integral beta composition equation for the three normalized
presentations. The canonical integral tensor associator is natural on pure tensors,
and additivity extends the equation to all localized morphisms. The three
`ExtensionProperties` clauses identify each rational comparison with the localized
integral beta. Functoriality of localization and the canonical rational scalar
associator then give the displayed equality on every rational object. -/
theorem extension_composition_equation
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (H : Type u) [Field H] [Algebra (Padic l) H] [FiniteDimensional (Padic l) H]
    (i : F →ₐ[Padic l] G) (j : G →ₐ[Padic l] H)
    (wF : IntegralFiniteExtension.DualizingDatum l X D hl F)
    (wG : IntegralFiniteExtension.DualizingDatum l X D hl G)
    (wH : IntegralFiniteExtension.DualizingDatum l X D hl H)
    (A : Datum D l hl X F wF) (B : Datum D l hl X G wG) (C : Datum D l hl X H wH)
    (a : scalar l X F G i ⋙ scalar l X G H j ≅ scalar l X F H (j.comp i))
    (hnorm : ∀ K : sfIntegralConstructibleCategory l F X,
      HEq (a.hom.app ((sfRationalConstructibleLocalization l F X).obj K))
        ((sfRationalConstructibleLocalization l H X).map
          (ObjectProperty.homMk
            (X := (integralScalar l X G H j).obj ((integralScalar l X F G i).obj K))
            (Y := (integralScalar l X F H (j.comp i)).obj K)
            (IntegralFiniteExtension.comp l F G i X H j K.obj K.property.1).hom)))
    (eFG : Extension D l hl X F G i wF wG A B)
    (eGH : Extension D l hl X G H j wG wH B C)
    (eFH : Extension D l hl X F H (j.comp i) wF wH A C)
    (hFG : ExtensionProperties D l hl X F G i wF wG A B eFG)
    (hGH : ExtensionProperties D l hl X G H j wG wH B C eGH)
    (hFH : ExtensionProperties D l hl X F H (j.comp i) wF wH A C eFH) :
    ∀ K : sfRationalConstructibleCategory l F X,
      (scalar l X G H j).map (eFG.comparison.hom.app (op K)) ≫
          eGH.comparison.hom.app (op ((scalar l X F G i).obj K)) =
        a.hom.app (A.dual.obj (op K)) ≫
          eFH.comparison.hom.app (op K) ≫
            C.dual.map (a.hom.app K).op := by
  have hcomp :=
    integral_comparison_cocycle D l hl X F G H i j wF wG wH A B C
  intro K
  rcases K with ⟨K⟩
  exact localized_extension_composition D l hl X F G H i j wF wG wH A B C a hnorm
    eFG eGH eFH hFG hGH hFH hcomp K

end WeilConjectures.RationalVerdier
