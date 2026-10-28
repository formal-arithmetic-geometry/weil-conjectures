/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RationalVerdierModels

/-! # Naturality of the integral beta comparison after localization

Source: blueprint thm-coef-rational-verdier, proof, paragraph 3
(blueprint: lem-coef-rational-verdier-integral-beta-naturality).

The integral case is the transpose calculation for the finite coefficient
comparison.  It is isolated from the rational tensor extension so that the
remaining argument only uses tensor-product induction.
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

/-- The localized integral beta comparison is natural on integral arrows.
Source: blueprint thm-coef-rational-verdier.proof.md, paragraph 3, the
integral-arrow transpose calculation (blueprint:
lem-coef-rational-verdier-integral-beta-naturality).

Proof: expand `beta` as the evaluation transpose followed by the canonical
dualizing map.  Naturality of the tensor-Hom adjunction in its first argument,
the scalar tensorator formula on pure tensors, and naturality of the internal
Hom map identify the two transposes.  The localized map preserves this
identity.  The statement is strictly the integral-arrow subcase; tensor
product induction and the supplied-family transport are handled by its caller.
-/
theorem integralBeta_naturality
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : Datum D l hl X E wE) (B : Datum D l hl X L wL)
    (c : ∀ K : sfRationalConstructibleCategory l E X,
      (scalar l X E L i).obj (A.dual.obj (op K)) ⟶
        B.dual.obj (op ((scalar l X E L i).obj K)))
    (hc : (∀ K : sfIntegralConstructibleCategory l E X,
    HEq (c ((sfRationalConstructibleLocalization l E X).obj K))
      ((sfRationalConstructibleLocalization l L X).map
        (ObjectProperty.homMk
          (X := (integralScalar l X E L i).obj
            ((IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves).obj (op K)))
          (Y := (IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves).obj
            (op ((integralScalar l X E L i).obj K)))
          (IntegralFiniteExtension.beta l E L i X D hl wE wL A.ordinary B.ordinary
            K.obj K.property.1)))))
    (K M : sfIntegralConstructibleCategory l E X)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
    (f : K ⟶ M) :
    (A.dual ⋙ scalar l X E L i).map
        (Quiver.Hom.op (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (sfRationalConstructibleLocalization l E X).obj K ⟶
            (sfRationalConstructibleLocalization l E X).obj M)) ≫
      c ((sfRationalConstructibleLocalization l E X).obj K) =
      c ((sfRationalConstructibleLocalization l E X).obj M) ≫
        ((scalar l X E L i).op ⋙ B.dual).map
          (Quiver.Hom.op (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
            (sfRationalConstructibleLocalization l E X).obj K ⟶
              (sfRationalConstructibleLocalization l E X).obj M)) := by
  sorry

end WeilConjectures.RationalVerdier
