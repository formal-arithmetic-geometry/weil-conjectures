/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierCompositionEquation
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierCompositionNormalization
import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition

/-! # Composition of normalized rational Verdier coefficient comparisons

Source: blueprint thm-coef-rational-verdier, proof
(blueprint: lem-coef-rational-verdier-composition). -/

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

/-- The specified rational comparisons obey the integral tensor associator equation.
Source: thm-coef-rational-verdier, proof step 7, composition clause;
current blueprint proof, paragraph 3
(blueprint: lem-coef-rational-verdier-composition).

Proof: localize the integral tensor associator comp on complete constructible
objects. Integral naturality on pure tensors, multiplied by the scalar image,
and additivity give a natural isomorphism a on rational categories, with the
displayed integral normalization. Use the composition equation for integral
beta, with the ordinary tensor presentations of A, B and C. Their normalized
representatives give the canonical tensor-Hom transposes, so the equation of
integral finite extension applies to these presentations. Move the inverse
associator through the contravariant dual using its inverse and functoriality.
Localize the resulting equality. Each e comparison is the localized beta by
its ExtensionProperties hypothesis. The object and pure-tensor equations
for scalar extension and C identify the functor images with the rational
ones in the conclusion. Functoriality of localization gives the desired
composite equation. Every rational K has an integral representative, so
this proves the assertion for all K, including torsion and zero objects.
The formulas also apply when either or both coefficient embeddings are identities. -/
theorem extension_composition
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (H : Type u) [Field H] [Algebra (Padic l) H] [FiniteDimensional (Padic l) H]
    (i : F →ₐ[Padic l] G) (j : G →ₐ[Padic l] H)
    (wF : IntegralFiniteExtension.DualizingDatum l X D hl F)
    (wG : IntegralFiniteExtension.DualizingDatum l X D hl G)
    (wH : IntegralFiniteExtension.DualizingDatum l X D hl H)
    (A : Datum D l hl X F wF) (B : Datum D l hl X G wG) (C : Datum D l hl X H wH)
    (eFG : Extension D l hl X F G i wF wG A B)
    (eGH : Extension D l hl X G H j wG wH B C)
    (eFH : Extension D l hl X F H (j.comp i) wF wH A C)
    (hFG : ExtensionProperties D l hl X F G i wF wG A B eFG)
    (hGH : ExtensionProperties D l hl X G H j wG wH B C eGH)
    (hFH : ExtensionProperties D l hl X F H (j.comp i) wF wH A C eFH) :
    ∃ a : scalar l X F G i ⋙ scalar l X G H j ≅ scalar l X F H (j.comp i),
      (∀ K : sfIntegralConstructibleCategory l F X,
        HEq (a.hom.app ((sfRationalConstructibleLocalization l F X).obj K))
          ((sfRationalConstructibleLocalization l H X).map
            (ObjectProperty.homMk
              (X := (integralScalar l X G H j).obj ((integralScalar l X F G i).obj K))
              (Y := (integralScalar l X F H (j.comp i)).obj K)
              (IntegralFiniteExtension.comp l F G i X H j K.obj K.property.1).hom))) ∧
      ∀ K : sfRationalConstructibleCategory l F X,
        (scalar l X G H j).map (eFG.comparison.hom.app (op K)) ≫
          eGH.comparison.hom.app (op ((scalar l X F G i).obj K)) =
        a.hom.app (A.dual.obj (op K)) ≫
          eFH.comparison.hom.app (op K) ≫
            C.dual.map (a.hom.app K).op := by
  obtain ⟨a, hnorm⟩ := rational_scalar_comp_normalization l X F G H i j
  refine ⟨a, hnorm, ?_⟩
  exact extension_composition_equation D l hl X F G H i j wF wG wH A B C a hnorm
    eFG eGH eFH hFG hGH hFH

end WeilConjectures.RationalVerdier
