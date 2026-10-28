/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RationalVerdierModels

/-! # Integral representative evaluation for normalized scalar comparisons

Source: blueprint thm-coef-rational-verdier, proof
(blueprint: lem-coef-rational-verdier-comparison-evaluation-integral).

This is the integral representative calculation used by the raw rational evaluation
statement. Its proof is split from the final objectwise transport: uncurry the
internal-Hom transpose, use the completion representative equation on K-flat
models, and localize the resulting evaluation square. -/

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

/-- Integral-representative evaluation compatibility.
Source: blueprint thm-coef-rational-verdier.proof.md, paragraph 3; the
internal-Hom transpose and completion representative calculation.
(blueprint: lem-coef-rational-verdier-comparison-evaluation-integral).

Proof: uncurry the internal-Hom comparison on a K-flat integral representative.
The inverse tensor-Hom adjunction turns `homMap` into scalar-extended ordinary
evaluation; postcomposition with `u` is `beta`. The completion representative
identity identifies this with the prescribed completed tensorator on pure
homogeneous tensors and hence on the localized object. Apply the two HEq
normalizations `hu` and `hb` to retain the displayed endpoint transports. -/
theorem normalizedExtension_evaluation_integral
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : Datum D l hl X E wE) (B : Datum D l hl X L wL)
    (e : Extension D l hl X E L i wE wL A B)
    (hu : (HEq e.omega.hom ((sfRationalConstructibleLocalization l L X).map
    (ObjectProperty.homMk (X := (integralScalar l X E L i).obj wE.omega) (Y := wL.omega)
      (IntegralFiniteExtension.u l E L i X D hl wE wL)))))
    (hb : (∀ K : sfIntegralConstructibleCategory l E X,
    HEq (e.comparison.hom.app (op ((sfRationalConstructibleLocalization l E X).obj K)))
      ((sfRationalConstructibleLocalization l L X).map
        (ObjectProperty.homMk
          (X := (integralScalar l X E L i).obj
            ((IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves).obj (op K)))
          (Y := (IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves).obj
            (op ((integralScalar l X E L i).obj K)))
          (IntegralFiniteExtension.beta l E L i X D hl wE wL A.ordinary B.ordinary
            K.obj K.property.1))))) :
    ∀ K : sfIntegralConstructibleCategory l E X, HEq
      ((tensor D l hl X L).map
        (Prod.mkHom (𝟙 ((scalar l X E L i).obj
          ((sfRationalConstructibleLocalization l E X).obj K)))
          (e.comparison.hom.app (op ((sfRationalConstructibleLocalization l E X).obj K)))) ≫
        B.evaluation ((scalar l X E L i).obj
          ((sfRationalConstructibleLocalization l E X).obj K)))
      ((@rationalTensorScalarComparison l _ E _ _ _ L _ _ _ i X (units D l hl X)).inv.app
        ((sfRationalConstructibleLocalization l E X).obj K,
          A.dual.obj (op ((sfRationalConstructibleLocalization l E X).obj K))) ≫
        (scalar l X E L i).map (A.evaluation
          ((sfRationalConstructibleLocalization l E X).obj K)) ≫ e.omega.hom) := by sorry


end WeilConjectures.RationalVerdier
