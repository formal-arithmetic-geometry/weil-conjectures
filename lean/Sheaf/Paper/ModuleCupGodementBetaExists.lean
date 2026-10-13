module

public import Sheaf.Paper.ModuleCupGodementCodegeneracies
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The coordinatewise Godement tensor maps obey naturality, unit and multiplication laws.
Source: Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16; Stacks, Tag 0FKR.
(blueprint: new-module-cup-godement-beta-exists)
Proof: For each point x, project TH and TK onto their x skyscrapers and evaluate their
stalks at x. Identify (TH tensor TK)_x with TH_x tensor TK_x by the canonical
stalk tensor isomorphism. Tensor the two evaluation maps into H_x tensor K_x, then
use the stalk tensor isomorphism into (H tensor K)_x. The skyscraper adjunction gives
a morphism from TH tensor TK to the
skyscraper of (H tensor K)_x; product universality assembles these into b. Naturality
is checked after each product projection on tensors of local representatives, where
both composites apply the two stalk maps to the same representatives. For the unit
law these representatives are germs of sections of H and K, and both composites give
the germ of their tensor. For multiplication, choose a common neighbourhood for the
outer germs and inner representatives: both composites evaluate the inner x
coordinates and tensor them. Equality on pure tensors, the stalk colimit universal
property, the skyscraper adjunction and product extensionality prove the laws.
The argument also applies to empty products and zero module sheaves. -/
theorem moduleCup_godement_beta_maps_exists (X : Scheme.{u}) :
    ∃ b : ∀ H K : X.Modules,
        moduleCup_godementObject X H ⊗ moduleCup_godementObject X K ⟶
          moduleCup_godementObject X (H ⊗ K),
      (∀ (H K H' K' : X.Modules) (f : H ⟶ H') (g : K ⟶ K'),
        (moduleCup_godementMap X f ⊗ₘ moduleCup_godementMap X g) ≫ b H' K' =
          b H K ≫ moduleCup_godementMap X (f ⊗ₘ g)) ∧
      (∀ H K : X.Modules,
        (moduleCup_godementUnit X H ⊗ₘ moduleCup_godementUnit X K) ≫ b H K =
          moduleCup_godementUnit X (H ⊗ K)) ∧
      (∀ H K : X.Modules,
        (moduleCup_godementMultiply X H ⊗ₘ moduleCup_godementMultiply X K) ≫ b H K =
          b (moduleCup_godementObject X H) (moduleCup_godementObject X K) ≫
            moduleCup_godementMap X (b H K) ≫ moduleCup_godementMultiply X (H ⊗ K)) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
