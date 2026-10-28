/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.SixFunctors.FiniteAdjunctionTransitionData

/-! # Coefficient compatibility of finite adjunctions

Source: blueprint integral-dualizing proof, paragraph 2.
(blueprint: lem-coef-finite-adjunction-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

namespace FiniteAdjunctionTransition

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable
  (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
  (a₀ b₀ : ℤ)
  (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
    DerivedCategory (pbcTowers (Spec (.of D.k))
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))))
  (e : ∀ n : ℕ, T ⋙ pbcTowerEvaluation (Spec (.of D.k))
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) n ≅
      compactSupportRestrictedLevel l E (finiteDualizingCompactification D X) n)
  (M : CoefCurryingModels l E D X Q a₀ b₀ T e)

/-- A proper part of finite adjunction compatibility: finiteAdjunctionSquare.
Source: blueprint integral-dualizing proof, paragraph 2, original steps 1--9.
(blueprint: lem-coef-finite-adjunction-square).

Proof: Uncurry both horizontals. IsSpecified.pairingEvaluation and hOrigin identify each
with the evaluation of the same tower beta followed by its trace. The support_finite
normalization makes the actual Roos projections a cone. Canonical tensor evaluation
respects transitions, and hHom identifies the Hom transition. Naturality of the tower
beta and hTrace equate the uncurried arrows. Curry and substitute the gamma equations.
Identity indices and identity input maps are included. Zero inputs give zero-source
pairings, and no assertion of a projection isomorphism is needed. -/
theorem finiteAdjunctionSquare (hl : l ≠ D.p)
    (_hab : a₀ ≤ b₀)
    (_htransition : ∀ (m n : ℕ) (h : n ≤ m)
      (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
      (pbcTowerTransition (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) m n h).app
          (T.obj K) ≫ (e n).hom.app K =
        (e m).hom.app K ≫ compactSupportRestrictedTransition l E
          (finiteDualizingCompactification D X) m n h K)
    (_hM : M.IsSpecified l E D X Q a₀ b₀ T e)
    (_hTensor : ∀ n : ℕ, M.tensorEvaluation n = canonicalTensorEvaluation l E n)
    (_hscalar : ∀ (r : ℕ) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
      (M.integralHom r).inv.app (op K) ≫ (M.finiteHom r).hom.app (op K) =
        scalarHom D l E X Q a₀ b₀ T e M r K)
    (eTrace : ∀ n : ℕ,
      (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
        coefTraceFiniteValue l E D X n)
    (_hTrace : ∀ (m n : ℕ) (h : n ≤ m),
      (coefTraceTransition l E h).app (coefTraceDualizingTower l E D X Q) ≫
          (eTrace n).hom ≫ coefTraceFiniteCounit l E D X n ≫
            (coefTraceTargetIso l E D n).hom =
        (eTrace m).hom ≫ coefTraceFiniteCounit l E D X m ≫
          (coefTraceTargetIso l E D m).hom ≫
            (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).map
              (coefTraceQuotientMap l E h))
    (_hOrigin : ∀ n : ℕ,
      (M.omegaEvaluation n).hom ≫ (M.omegaOrigin n).hom = (eTrace n).hom)
    (_hHom : ∀ (m n : ℕ) (h : n ≤ m)
      (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
      (coefTraceTransition l E h).app ((coefPairingHom l E X M.calculus Q).obj (op K)) ≫
          (M.integralHom n).hom.app (op K) =
        (M.integralHom m).hom.app (op K) ≫ HTransition D l E X hl h K) :
    ∀ (K : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory)
      (m n : ℕ) (h : n ≤ m),
      HTransition D l E X hl h K.obj ≫ finiteHorizontal D l E X Q a₀ b₀ T e M n K =
        finiteHorizontal D l E X Q a₀ b₀ T e M m K ≫
          JTransition D l E X T h K.obj := by sorry

end FiniteAdjunctionTransition
end WeilConjectures
