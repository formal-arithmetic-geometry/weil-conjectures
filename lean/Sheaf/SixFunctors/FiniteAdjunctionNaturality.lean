/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.SixFunctors.FiniteAdjunctionTransitionData

/-! # Input naturality of finite adjunctions

Source: blueprint integral-dualizing proof, paragraph 2.
(blueprint: lem-coef-finite-adjunction-naturality).
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

/-- A proper part of finite adjunction compatibility: finiteAdjunctionNaturality.
Source: blueprint integral-dualizing proof, paragraph 2, original steps 10.
(blueprint: lem-coef-finite-adjunction-naturality).

Proof: Uncurry both horizontals. IsSpecified.pairingEvaluation and hOrigin express them
using the same tower beta. Apply pairingDinaturality to z, evaluate the tower at r,
and use naturality of tensorEvaluation inverse. The actual compact-support
projection is a composite of natural transformations; combine its naturality with
that of eB inverse and integralHom inverse. Braiding naturality and tensor
functoriality equate the uncurried arrows, and curry_pre_app gives the conclusion.
Identity indices and identity input maps are included. Zero inputs give zero-source
pairings, and no assertion of a projection isomorphism is needed. -/
theorem finiteAdjunctionNaturality (_hab : a₀ ≤ b₀)
    (_hM : M.IsSpecified l E D X Q a₀ b₀ T e)
    (_hscalar : ∀ (r : ℕ) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
      (M.integralHom r).inv.app (op K) ≫ (M.finiteHom r).hom.app (op K) =
        scalarHom D l E X Q a₀ b₀ T e M r K)
    (eTrace : ∀ n : ℕ,
      (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
        coefTraceFiniteValue l E D X n)
    (_hOrigin : ∀ n : ℕ,
      (M.omegaEvaluation n).hom ≫ (M.omegaOrigin n).hom = (eTrace n).hom)
 :
    ∀ (K K' : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory)
      (z : K ⟶ K') (r : ℕ),
      (H D l E X r).map z.hom.op ≫ finiteHorizontal D l E X Q a₀ b₀ T e M r K =
        finiteHorizontal D l E X Q a₀ b₀ T e M r K' ≫
          (coefCurryingPointHom l E r).map ((C D l E X T).map z.hom).op := by sorry

end FiniteAdjunctionTransition
end WeilConjectures
