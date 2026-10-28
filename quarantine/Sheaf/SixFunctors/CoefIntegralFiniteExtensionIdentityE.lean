module

public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore

/-! Identity equation for the E-side integral finite-extension comparison.

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-sf-integral-finite-extension-cocycles).

This is the E component of the cocycle argument.  It is split from the main
statement so that the identity calculation can be proved independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

/-- E-side identity equations for the fixed integral comparison.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, final paragraph.
(blueprint: lem-sf-integral-finite-extension-identity-e)
Proof: transpose the finite dualizing counit comparisons through the coherent
total limit, then use the tensor-Hom adjunction and the identity multiplication
map to obtain the v and beta equations. -/
theorem comparison_identity_E
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wE : DualizingDatum l X D hl E)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (_hevalE : ∀ (K K' M : IntegralVerdier.Ambient l E X) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (a.adjunction K').counit.app M =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app M) :
    IdentityConclusion l E X D hl wE a := by
  sorry

end WeilConjectures.IntegralFiniteExtension
