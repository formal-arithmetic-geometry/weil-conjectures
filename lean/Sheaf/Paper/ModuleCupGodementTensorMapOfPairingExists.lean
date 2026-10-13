module

public import Sheaf.Paper.ModuleCupGodementTensorCoordinates

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Extension of a stalkwise pairing to the Godement tensor map.
Source: Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16; Stacks, Tag 0FKR.
(blueprint: new-module-cup-godement-tensor-map-of-pairing-exists)
The maps to each skyscraper coordinate are obtained from tensor universality and
sheafification, then assembled by the product universal property. -/
theorem moduleCup_godement_tensor_map_of_pairing_exists (X : Scheme.{u})
    (t : ∀ (H K : X.Modules) (x : X),
      H.presheaf.stalk x → K.presheaf.stalk x → (H ⊗ K).presheaf.stalk x)
    (ht : ∀ (H K : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
        (s : Γ(H, U)) (r : Γ(K, U)),
      t H K x (H.presheaf.germ U x hx s) (K.presheaf.germ U x hx r) =
        (H ⊗ K).presheaf.germ U x hx
          ((moduleCup_sectionTensor X H K).app (op U)
            (s ⊗ₜ[Γ(X, U)] r))) :
    ∃ b : ∀ H K : X.Modules,
      moduleCup_godementObject X H ⊗ moduleCup_godementObject X K ⟶
        moduleCup_godementObject X (H ⊗ K),
      ∀ (H K : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
        (s : Γ(moduleCup_godementObject X H, U))
        (r : Γ(moduleCup_godementObject X K, U)),
      (moduleCup_sectionTensor X (moduleCup_godementObject X H)
          (moduleCup_godementObject X K) ≫ (b H K).val ≫
        (Pi.π (fun y : X ↦ skyscraper y ((H ⊗ K).presheaf.stalk y)) x).val).app
          (op U) (s ⊗ₜ[Γ(X, U)] r) ⟨hx⟩ =
        t H K x
          ((Pi.π (fun y : X ↦ skyscraper y (H.presheaf.stalk y)) x).app U s ⟨hx⟩)
          ((Pi.π (fun y : X ↦ skyscraper y (K.presheaf.stalk y)) x).app U r ⟨hx⟩) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
