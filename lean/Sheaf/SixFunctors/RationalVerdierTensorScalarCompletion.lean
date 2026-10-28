/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RationalVerdierModels

/-! # The tensor-only scalar/completion square

Source: blueprint thm-coef-rational-verdier, paragraph 3, and
lem-coef-integral-finite-extension, evaluation and completion paragraphs.
(blueprint: lem-coef-rational-verdier-tensor-scalar-completion). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Scalar extension respects the normalized ordinary-to-completed tensor comparison.
This square contains no internal Hom, evaluation, dualizing object, or rationalization.

Source: blueprint thm-coef-rational-verdier.proof.md, paragraph 3; the normalized
completion calculation in lem-coef-integral-finite-extension.proof.md.
(blueprint: lem-coef-rational-verdier-tensor-scalar-completion).

Proof: represent K and M by flat-term K-flat complexes. The ordinary scalar tensorator
sends s tensor (x tensor y) to (s tensor x) tensor (1 tensor y). The representative
condition of each Completion identifies its map with the fixed completion chain map:
every positive quotient coordinate is the quotient tensor map and the shifted coordinate
is zero. The scalar completion map has the same quotient/zero-coordinate normalization.
Consequently completing before or after the ordinary scalar tensorator gives the same
map: on a homogeneous tensor both quotient coordinates are its scalar-extended quotient,
and both shifted coordinates vanish. Sheafification, the total-tensor coproduct
inclusions and the two mapping-fiber coordinates detect equality. Descend this equation
through the K-flat localization; representative independence and naturality transport it
to K and M. Invert the constructible tensor completion comparisons and the scalar
completion comparisons on K and M. The normalized definition of scalarTensorCompleted
then gives the displayed inverse square. Zero objects and the identity extension use
exactly the same quotient and zero-coordinate maps. -/
theorem tensor_scalar_completion
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (cE : Completion D l hl X E a) (cL : Completion D l hl X L b)
    (K M : sfIntegralConstructibleCategory l E X) :
    (@asIso _ _ _ _ (cL.map.app
      (((integralScalar l X E L i).obj K).obj, ((integralScalar l X E L i).obj M).obj))
      (cL.invertible ((integralScalar l X E L i).obj K)
        ((integralScalar l X E L i).obj M))).inv ≫
      b.tensor.map (Prod.mkHom
        (IntegralFiniteExtension.completion l E L i X K.obj K.property.1).inv
        (IntegralFiniteExtension.completion l E L i X M.obj M.property.1).inv) ≫
      (PurCompactSupport.scalarTensor (completedCoefficientMap l E L i X)
        (IntegralFiniteExtension.tensorModel X a)
        (IntegralFiniteExtension.tensorModel X b)).inv.app (K.obj, M.obj) ≫
      (completedScalarComparison l E L i X).app (a.tensor.obj (K.obj, M.obj)) =
    (@integralTensorScalarComparison l _ E _ _ _ L _ _ _ i X (units D l hl X) K M).inv.hom ≫
      (integralScalarExtensionOfUniverses l E L i X).map
        (@asIso _ _ _ _ (cE.map.app (K.obj, M.obj)) (cE.invertible K M)).inv := by
  sorry

end WeilConjectures.RationalVerdier
