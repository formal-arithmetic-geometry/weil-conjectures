/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCocycles
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationNaturality

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
The integral cocycle package needed for the rational composition equation.
Source: the integral comparison cocycle in
`lem-coef-integral-finite-extension`, used in the proof of
`lem-coef-rational-verdier-composition-equation`.

Proof: the ordinary tensor presentations in the three Verdier data satisfy the
first-variable evaluation naturality theorem.  Apply the integral comparison
cocycle theorem to the F-to-G presentation and specialize its final tower to
G-to-H with the C presentation.  The resulting `CompositionConclusion` is the
six-part integral coherence package; its beta component is the equation
localized in the rational proof.  No rational comparison or associator is
introduced here.
(blueprint: lem-coef-rational-verdier-composition-equation).
-/
theorem integral_comparison_cocycle
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (H : Type u) [Field H] [Algebra (Padic l) H] [FiniteDimensional (Padic l) H]
    (i : F →ₐ[Padic l] G) (j : G →ₐ[Padic l] H)
    (wF : IntegralFiniteExtension.DualizingDatum l X D hl F)
    (wG : IntegralFiniteExtension.DualizingDatum l X D hl G)
    (wH : IntegralFiniteExtension.DualizingDatum l X D hl H)
    (A : Datum D l hl X F wF) (B : Datum D l hl X G wG) (C : Datum D l hl X H wH) :
    IntegralFiniteExtension.CompositionConclusion l F G i X D hl wF wG
      A.ordinary B.ordinary H j wH C.ordinary := by
  exact (IntegralFiniteExtension.comparison_cocycles l F G i X D hl wF wG
    A.ordinary B.ordinary
    (IntegralHom.evaluation_naturality X _ A.ordinary)
    (IntegralHom.evaluation_naturality X _ B.ordinary)).2.2 H j wH C.ordinary
      (IntegralHom.evaluation_naturality X _ C.ordinary)

end WeilConjectures.RationalVerdier
