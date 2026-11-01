/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionPureTensor
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionTranspose

/-! Composition equation for integral finite-extension comparisons.

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-sf-integral-finite-extension-cocycles).

This is the composition component of the cocycle argument, split from the
identity components.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

/-- Composition and pentagon equations for the fixed integral comparisons.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, final paragraph.
(blueprint: lem-sf-integral-finite-extension-composition)
Proof: combine the pure-tensor coefficient coherence with the transposed
u, v and beta coherence for the same further extension.
-/
theorem comparison_composition
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (_hevalE : ∀ (K K' M : IntegralVerdier.Ambient l E X) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (a.adjunction K').counit.app M =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app M)
    (_hevalL : ∀ (K K' M : IntegralVerdier.Ambient l L X) (f : K' ⟶ K),
      b.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l L X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (b.adjunction K').counit.app M =
        b.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (b.adjunction K).counit.app M) :
    ∀ (F : Type u) [Field F] [Algebra (Padic l) F]
      [FiniteDimensional (Padic l) F]
      (j : L →ₐ[Padic l] F) (wF : DualizingDatum l X D hl F)
      (c : IntegralHom.TensorPresentation.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l F X)),
      (∀ (K K' M : IntegralVerdier.Ambient l F X) (f : K' ⟶ K),
        c.tensor.map (Prod.mkHom (𝟙 K')
            ((IntegralHom.hom.{u, u} X
              (completedIntegralCommRingSheafUnrestricted l F X)).map
              (Prod.mkHom f.op (𝟙 M)))) ≫ (c.adjunction K').counit.app M =
          c.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (c.adjunction K).counit.app M) →
      CompositionConclusion l E L ι X D hl wE wL a b F j wF c := by
  intro F _ _ _ j wF c hc
  obtain ⟨h₁, h₂, h₆⟩ :=
    comparison_composition_pure_tensor l E L ι X D hl wE wL a b F j wF c
  obtain ⟨h₃, h₄, h₅⟩ :=
    comparison_composition_transpose l E L ι X D hl wE wL a b _hevalE _hevalL F j wF c hc
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

end WeilConjectures.IntegralFiniteExtension
