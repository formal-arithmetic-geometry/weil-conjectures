/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RationalVerdierModels
import Sheaf.SixFunctors.RationalVerdierIntegralCocycle

/-! # Integral-representative transport for rational Verdier composition

This is the localization step in the composition equation.  It is stated only on
integral representatives; the enclosing rational category has exactly these objects.
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

/--
The normalized comparison equation on an integral representative.
Source: blueprint thm-coef-rational-verdier, proof step 7, composition clause;
the localization of the integral beta composition equation.

Proof: localize the beta component of `CompositionConclusion`, transport its
endpoints through the normalized associator equation, and use the three
`ExtensionProperties` comparison normalizations.  The pure-tensor clause of
`Datum.pure`, additivity of the dual functors, and functoriality of scalar
localization extend the equality from integral arrows to the localized arrow.
The construction is independent of the choice of representative, so this
integral-representative form is sufficient for the raw localization category.
(blueprint: lem-coef-rational-verdier-composition-equation).
-/
theorem localized_extension_composition
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
    (hFH : ExtensionProperties D l hl X F H (j.comp i) wF wH A C eFH)
    (hcomp : IntegralFiniteExtension.CompositionConclusion l F G i X D hl wF wG
      A.ordinary B.ordinary H j wH C.ordinary) :
    ∀ K : sfIntegralConstructibleCategory l F X,
      (scalar l X G H j).map
          (eFG.comparison.hom.app (op ((sfRationalConstructibleLocalization l F X).obj K))) ≫
          eGH.comparison.hom.app
            (op ((scalar l X F G i).obj ((sfRationalConstructibleLocalization l F X).obj K))) =
        a.hom.app
            (A.dual.obj (op ((sfRationalConstructibleLocalization l F X).obj K))) ≫
          eFH.comparison.hom.app ((op ((sfRationalConstructibleLocalization l F X).obj K))) ≫
            C.dual.map
              (a.hom.app ((sfRationalConstructibleLocalization l F X).obj K)).op := by
  sorry

end WeilConjectures.RationalVerdier
