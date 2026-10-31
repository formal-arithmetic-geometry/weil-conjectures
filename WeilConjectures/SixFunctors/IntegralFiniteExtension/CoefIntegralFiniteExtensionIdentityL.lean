/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionIdentityE

/-! Identity equation for the L-side integral finite-extension comparison.

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-sf-integral-finite-extension-cocycles).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

/-- L-side identity equations for the fixed integral comparison.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, final paragraph.
(blueprint: lem-sf-integral-finite-extension-identity-l)
Proof: repeat the finite counit-transpose and tensor-Hom calculation for L;
the normalized identity map is multiplication, including degenerate objects. -/
theorem comparison_identity_L
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (X : Scheme.{u}) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wL : DualizingDatum l X D hl L)
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (_hevalL : ∀ (K K' M : IntegralVerdier.Ambient l L X) (f : K' ⟶ K),
      b.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l L X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (b.adjunction K').counit.app M =
        b.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (b.adjunction K).counit.app M) :
    IdentityConclusion l L X D hl wL b := by
  exact comparison_identity_E l L X D hl wL b _hevalL

end WeilConjectures.IntegralFiniteExtension
