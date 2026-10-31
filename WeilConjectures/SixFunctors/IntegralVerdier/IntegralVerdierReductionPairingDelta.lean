/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierReductionPairingDeltaUncurried

/-! # Split lemma: Reduction compatibility of the signed Verdier delta

Source: Stacks Project, Tags 06YL and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Reduction compatibility of the signed Verdier delta.

Source: Stacks Project, Tags 06YL and 08J9.

Prove the delta reduction square by uncurrying through the finite adjunction. Evaluation
compatibility and signed swap naturality identify the transpose; the inverse comparison appears by
contravariance of Hom.
(blueprint: lem-sf-integral-verdier-reduction-pairing-delta). -/
theorem reductionPairing_delta
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl))
    (s : SignedSymmetry X (completedIntegralCommRingSheaf l E X D hl) a)
    (hs : ∀ (K L K' L' : Ambient l E X) (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f))
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (t : ∀ n : ℕ, SignedSymmetry X (integralCoefficientCommRingSheaf l E X n)
      (m n).target)
    (ht : ∀ (n : ℕ) (K L K' L' : DerivedCategory (scalarReductionTarget l E X n))
      (f : K ⟶ K') (g : L ⟶ L'),
      (m n).target.tensor.map (Prod.mkHom f g) ≫ ((t n).swap K' L').hom =
        ((t n).swap K L).hom ≫ (m n).target.tensor.map (Prod.mkHom g f))
    (he : ∀ (K K' W : Ambient l E X) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (completedIntegralCommRingSheaf l E X D hl)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ (a.adjunction K').counit.app W =
      a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app W)
    (het : ∀ (n : ℕ) (K K' W : DerivedCategory (scalarReductionTarget l E X n))
      (f : K' ⟶ K),
      (m n).target.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ ((m n).target.adjunction K').counit.app W =
      (m n).target.tensor.map (Prod.mkHom f (𝟙 _)) ≫
        ((m n).target.adjunction K).counit.app W)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n)
    (h : ∀ (K : Ambient l E X) (n : ℕ), IsIso (comparison l E X D hl (m n) ω r K)) :
    (∀ (K : Ambient l E X) (n : ℕ),
      (scalarReductionDerivedExtension l E X n).map (delta X a s ω.obj K) ≫
        comparison l E X D hl (m n) ω r ((dual l E X ω.obj).obj (op K)) ≫
        (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom (@asIso _ _ _ _ (comparison l E X D hl (m n) ω r K)
            (h K n)).inv.op (𝟙 (integralDualizingFiniteTerm l E D X n))) =
      delta X (m n).target (t n) (integralDualizingFiniteTerm l E D X n)
        ((scalarReductionDerivedExtension l E X n).obj K))  := by
  intro K n
  unfold delta restrictionDualDelta comparison
  let adj := (m n).target.adjunction
    ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).obj
      (op ((scalarReductionDerivedExtension l E X n).obj K),
        integralDualizingFiniteTerm l E D X n))
  change _ = adj.homEquiv
    ((scalarReductionDerivedExtension l E X n).obj K)
    (integralDualizingFiniteTerm l E D X n) _
  apply adj.homEquiv
    ((scalarReductionDerivedExtension l E X n).obj K)
    (integralDualizingFiniteTerm l E D X n) |>.symm.injective
  simpa [adj, delta, restrictionDualDelta, comparison, restrictionDualEvaluation] using
    (reductionPairing_delta_uncurried D l hl E X a s hs m t ht he het ω r h K n)

end WeilConjectures.IntegralVerdier
