/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.SixFunctors.RationalVerdierModels

/-! # Biduality follows from the scalar evaluation square

Source: blueprint thm-coef-rational-verdier, proof
(blueprint: lem-coef-rational-verdier-comparison-biduality). -/

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

/-- Biduality follows from the scalar evaluation square.
Source: current blueprint thm-coef-rational-verdier.proof.md, paragraph 3;
lem-coef-integral-finite-extension.proof.md, evaluation and transposition paragraphs.
(blueprint: lem-coef-rational-verdier-comparison-biduality).

Proof: the natural signed symmetries of A and B are uniquely determined by
their Koszul representative equations. Indeed represent each ambient derived
object by a K-flat complex and use naturality of the swap to conjugate to those
representatives. The completed tensorator respects the two swaps: on homogeneous
K-flat tensors its coefficient factors have degree zero, so the Koszul signs
on the two paths agree, and the completion normalizations identify the maps.
For every integral representative K, transpose the supplied evaluation square
again, now in the dual input. IntegralVerdier.delta is exactly the transpose of
evaluation after the signed swap. Use the preceding symmetry square and
naturality of the comparison isomorphism to identify the two transposes with
the two displayed double-dual composites. The tensor-Hom Hom equivalence is
injective, so these composites are equal. A.bidual_integral and
B.bidual_integral identify the localized deltas with the specified bidual maps.
All raw rational objects are integral representatives; hence the same equality
holds for every K. No identity-field or zero-object exception is required -/
theorem evaluation_implies_biduality
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : Datum D l hl X E wE) (B : Datum D l hl X L wL)
    (hA : ∀ (K M K' M' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X))
      (f : K ⟶ K') (g : M ⟶ M'),
      A.ordinary.tensor.map (Prod.mkHom f g) ≫ (A.symmetry.swap K' M').hom =
        (A.symmetry.swap K M).hom ≫ A.ordinary.tensor.map (Prod.mkHom g f))
    (hB : ∀ (K M K' M' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l L X))
      (f : K ⟶ K') (g : M ⟶ M'),
      B.ordinary.tensor.map (Prod.mkHom f g) ≫ (B.symmetry.swap K' M').hom =
        (B.symmetry.swap K M).hom ≫ B.ordinary.tensor.map (Prod.mkHom g f))
    (e : Extension D l hl X E L i wE wL A B)
    (heval : (∀ K : sfRationalConstructibleCategory l E X,
    (tensor D l hl X L).map
        (Prod.mkHom (𝟙 ((scalar l X E L i).obj K)) (e.comparison.hom.app (op K))) ≫
      B.evaluation ((scalar l X E L i).obj K) =
    (@rationalTensorScalarComparison l _ E _ _ _ L _ _ _ i X (units D l hl X)).inv.app
        (K, A.dual.obj (op K)) ≫
      (scalar l X E L i).map (A.evaluation K) ≫ e.omega.hom)) :
    (∀ K : sfRationalConstructibleCategory l E X,
    (scalar l X E L i).map (A.bidual.hom.app K) ≫
      e.comparison.hom.app (op (A.dual.obj (op K))) =
    B.bidual.hom.app ((scalar l X E L i).obj K) ≫
      B.dual.map (e.comparison.hom.app (op K)).op) := by sorry

end WeilConjectures.RationalVerdier
