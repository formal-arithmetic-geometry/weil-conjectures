/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomOrdinaryTransposeEvaluation

/-! # The ordinary coordinates of the finite coefficient Hom transpose
Source: blueprint thm-coef-finite-hom, evaluation paragraph
(blueprint: lem-coef-finite-hom-ordinary-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b c d
open CategoryTheory AlgebraicGeometry Opposite
namespace WeilConjectures

private theorem finiteHom_unique_transpose
      {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
      {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
      (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
      (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
      (K M : A)
      (v : F.obj (HA.obj (op K, M)) ⟶ HB.obj (op (F.obj K), F.obj M))
      (hv : SB.tensor.map (Prod.mkHom v (𝟙 (F.obj K))) ≫
        SB.evaluation (F.obj K) (F.obj M) =
          μ.inv.app (HA.obj (op K, M), K) ≫ F.map (SA.evaluation K M)) :
      v = coefficientBaseChangeHom SA SB F μ K M := by
    have hu : (SB.transpose _ (F.obj K) (F.obj M)).symm v =
        SB.tensor.map (Prod.mkHom v (𝟙 (F.obj K))) ≫
          SB.evaluation (F.obj K) (F.obj M) := by
      simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
        CoefficientClosedStructure.evaluation] using!
        (SB.adjunction (F.obj K)).homEquiv_counit _ (F.obj M) v
    apply (SB.transpose _ (F.obj K) (F.obj M)).symm.injective
    rw [hu, hv]
    unfold coefficientBaseChangeHom
    exact ((SB.transpose _ _ _).symm_apply_apply _).symm


/-- The right-tensor closed transpose is the published ordinary left-tensor transpose.
Source: blueprint thm-coef-finite-hom, proof paragraphs 1--2, the sentence defining v
as the transpose of reduced evaluation
(blueprint: lem-coef-finite-hom-ordinary-transpose).

Proof: the normalization of finiteHomEtaleData identifies its closed record with
finiteHomEtaleClosedGeneral and its tensorator with ExceptionalCoefficients.tensorIso.
The closed-record normalization identifies its right-tensor adjunction with the
ordinary derived tensor-Hom adjunction transported through the Koszul symmetry.
The ordinary scalar tensor comparison is the inverse of that tensorator, by uniqueness
of its flat-term K-flat representative normalization. Its signed symmetry square
moves the Koszul interchange through scalar extension. Thus both arrows, when
untransposed along the ordinary left-tensor adjunction, are the ordinary scalar
tensor comparison followed by scalar extension of its evaluation counit.
Injectivity of this adjunction's Hom equivalence gives the stated equality. This
equality is recorded in Arrow so the endpoint data are included without a costly
implicit conversion. The argument uses arbitrary objects, includes zero objects
and identity quotients,
and does not assert invertibility of either Hom comparison. -/
theorem finiteHom_ordinary_transpose
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n)
    (K M : finiteHomEtale l E X n) :
    Arrow.mk (etaleFiniteHomCanonical l E X h K M) =
      Arrow.mk (Etale.CoefficientPairingChange.evaluationComparison
        (finiteHomQuotient l E h) X K M) := by
  have hchar := finiteHom_ordinary_transpose_evaluation l E X h K M
  have hv := finiteHom_unique_transpose (finiteHomEtaleClosed l E X n)
    (finiteHomEtaleClosed l E X m) (finiteHomEtaleReduction l E X h)
    (finiteHomEtaleTensor l E X h) K M
    (Etale.CoefficientPairingChange.evaluationComparison
      (finiteHomQuotient l E h) X K M) hchar
  have hh := congrArg (fun f :
      (finiteHomEtaleReduction l E X h).obj
          ((finiteHomEtaleInternalHom l E X n).obj (op K, M)) ⟶
        (finiteHomEtaleInternalHom l E X m).obj
          (op ((finiteHomEtaleReduction l E X h).obj K),
            (finiteHomEtaleReduction l E X h).obj M) =>
      (Arrow.mk f : Arrow (finiteHomEtale l E X m))) hv.symm
  unfold finiteHomEtaleCategory
  exact hh

end WeilConjectures
