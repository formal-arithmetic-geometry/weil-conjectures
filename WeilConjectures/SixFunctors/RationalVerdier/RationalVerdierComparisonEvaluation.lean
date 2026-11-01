/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierComparisonEvaluationIntegral

/-! # Completed evaluation for normalized scalar comparisons

Source: blueprint thm-coef-rational-verdier, proof
(blueprint: lem-coef-rational-verdier-comparison-evaluation). -/

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

/-- Completed evaluation for normalized scalar comparisons.
Source: current blueprint thm-coef-rational-verdier.proof.md, paragraph 3;
lem-coef-integral-finite-extension.proof.md, evaluation and transposition paragraphs.
(blueprint: lem-coef-rational-verdier-comparison-evaluation).

Proof: uncurry the definition of IntegralFiniteExtension.beta. Adjunction's
inverse Hom equivalence sends homMap to scalar-extended ordinary evaluation;
postcomposition with internal Hom of u sends it to that evaluation followed by u.
On a good K-flat pair the defining representative equation of each completion
map identifies the conjugated ordinary scalar tensorator with the specified
completed scalar tensorator: both multiply coefficient factors and apply the
same quotient maps, including the zero shifted mapping-fiber coordinate.
Naturality and the K-flat localization extend this identity to constructible
inputs. Apply integral-to-rational localization to the resulting evaluation
square. The normalization hypotheses on e identify its two components, and
A.evaluation_integral and B.evaluation_integral identify the evaluation maps.
The pure-tensor normalization of rationalTensorScalarComparison identifies its
inverse with this localized tensorator. Every raw rational object is literally
an integral representative, so this proves the displayed formula for every K.
The same formulas apply to zero inputs, degree-one extensions and empty X -/
theorem normalizedExtension_evaluation
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
    (∀ K : sfRationalConstructibleCategory l E X,
    (tensor D l hl X L).map
        (Prod.mkHom (𝟙 ((scalar l X E L i).obj K)) (e.comparison.hom.app (op K))) ≫
      B.evaluation ((scalar l X E L i).obj K) =
    (@rationalTensorScalarComparison l _ E _ _ _ L _ _ _ i X (units D l hl X)).inv.app
        (K, A.dual.obj (op K)) ≫
      (scalar l X E L i).map (A.evaluation K) ≫ e.omega.hom)  := by
  intro K
  rcases K with ⟨K⟩
  exact eq_of_heq (normalizedExtension_evaluation_integral D l hl X E L i wE wL A B e hu hb K)

end WeilConjectures.RationalVerdier
