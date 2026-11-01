/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionIdentityE
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionIdentityL
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionComposition

/-! # Canonical integral finite-extension comparisons

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-coef-integral-finite-extension).

The defining comparisons are publicly re-exported from the models module.
This module fixes the maps and predicates independently of their compatibility theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.derivedInternalHomOfUniverses
  CategoryTheory.homComplexFunctor
  WeilConjectures.IntegralHom.totalTensor WeilConjectures.IntegralHom.homModelMap
  WeilConjectures.IntegralHom.projection WeilConjectures.IntegralHom.evaluate

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)

/-- Unit, composition and associator equations for the specified integral comparisons.
This concerns coefficient coherence only, with no invertibility, reduction or
biduality assertion.
Source: current blueprint lem-coef-integral-finite-extension.proof.md, final paragraph
(blueprint: lem-sf-integral-finite-extension-cocycles).

Proof: the ordinary scalar unit sends s tensor x to sx and the scalar associator
sends c tensor (b tensor x) to c*j(b) tensor x. On three successive extensions,
both parenthesizations multiply these degree-zero coefficient factors in the same
order. These generator formulas give the two unit equations for comp and its
pentagon. The normalized completion maps cancel at intermediate vertices, giving
exactly unit and comp as defined here. For u the finite counit transposes have
these unit and composition equations, by pasting the compact-support comparisons
and the exceptional adjunction counits. Apply the coherent total-limit functor;
uniqueness in u_existsUnique identifies the result with the specified maps.
For v, transpose both composites after the same scalar tensor associator: both
are scalar-extended evaluation, so uniqueness of transpose gives equality.
Postcompose with internal Hom into the u equation to obtain the beta equation.
The same argument for the identity ring map gives all three identity equations.
These computations use the fixed representative normalizations in each tensor
presentation and do not choose a new comparison or basis. They include identical
fields, identity embeddings, zero objects and empty schemes.
Each presentation is assumed natural in the first tensor variable (as supplied by
signedCalculus): its adjunction is otherwise free at objects that are not K-flat
complexes, and composing it there with -1 would change the sign of v. -/
theorem comparison_cocycles
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (hevalE : ∀ (K K' M : IntegralVerdier.Ambient l E X) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (a.adjunction K').counit.app M =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app M)
    (hevalL : ∀ (K K' M : IntegralVerdier.Ambient l L X) (f : K' ⟶ K),
      b.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l L X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (b.adjunction K').counit.app M =
        b.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (b.adjunction K).counit.app M) :
    IdentityConclusion l E X D hl wE a ∧ IdentityConclusion l L X D hl wL b ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
      (j : L →ₐ[Padic l] F) (wF : DualizingDatum l X D hl F)
      (c : IntegralHom.TensorPresentation.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l F X)),
      (∀ (K K' M : IntegralVerdier.Ambient l F X) (f : K' ⟶ K),
        c.tensor.map (Prod.mkHom (𝟙 K')
            ((IntegralHom.hom.{u, u} X
              (completedIntegralCommRingSheafUnrestricted l F X)).map
              (Prod.mkHom f.op (𝟙 M)))) ≫ (c.adjunction K').counit.app M =
          c.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (c.adjunction K).counit.app M) →
    CompositionConclusion l E L ι X D hl wE wL a b F j wF c) := by
  refine ⟨comparison_identity_E l E X D hl wE a hevalE,
    comparison_identity_L l L X D hl wL b hevalL, ?_⟩
  exact comparison_composition l E L ι X D hl wE wL a b hevalE hevalL

end WeilConjectures.IntegralFiniteExtension
