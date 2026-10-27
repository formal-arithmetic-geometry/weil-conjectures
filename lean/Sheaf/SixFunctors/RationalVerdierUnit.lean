/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.SixFunctors.RationalVerdierModels

/-! # Identity coefficient extension for normalized rational Verdier comparisons

Source: blueprint thm-coef-rational-verdier, proof
(blueprint: lem-coef-rational-verdier-unit). -/

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

/-- The specified rational comparison obeys the integral tensor unit equation.
Source: thm-coef-rational-verdier, proof step 7, identity-extension clause;
current blueprint proof, paragraph 3
(blueprint: lem-coef-rational-verdier-unit).

Proof: the integral tensor multiplication unit is a natural isomorphism on
complete inputs. Its localization defines j on the unchanged objects. Its
naturality on a pure tensor is integral naturality times that coefficient;
additivity extends it to all maps, and the integral inverse localizes. This
also gives the displayed normalization. The integral identity-extension
formula says beta is the tensor unit at the integral dual followed by the
dual of the unit at K. It holds for A.ordinary because representative
normalization identifies its evaluation transpose with the canonical one.
Apply localization to this equality. ExtensionProperties identifies its
left side with e.comparison, and A.pure at coefficient one identifies the
dual of the localized unit on the right. A.objects fixes the endpoints.
Every rational object is literally an integral representative, so this
proves the equation for all K. No faithfulness of localization is used;
in particular torsion objects and the empty scheme are included. -/
theorem extension_unit
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : Datum D l hl X E wE)
    (e : Extension D l hl X E E (AlgHom.id (Padic l) E) wE wE A A)
    (he : ExtensionProperties D l hl X E E (AlgHom.id (Padic l) E) wE wE A A e) :
    ∃ j : scalar l X E E (AlgHom.id (Padic l) E) ≅ 𝟭 (sfRationalConstructibleCategory l E X),
      (∀ K : sfIntegralConstructibleCategory l E X,
        HEq (j.hom.app ((sfRationalConstructibleLocalization l E X).obj K))
          ((sfRationalConstructibleLocalization l E X).map
            (ObjectProperty.homMk
              (X := (integralScalar l X E E (AlgHom.id (Padic l) E)).obj K) (Y := K)
              (IntegralFiniteExtension.unit l E X K.obj K.property.1).hom))) ∧
      ∀ K : sfRationalConstructibleCategory l E X,
        e.comparison.hom.app (op K) =
          j.hom.app (A.dual.obj (op K)) ≫
            A.dual.map (j.hom.app K).op := by sorry

end WeilConjectures.RationalVerdier
