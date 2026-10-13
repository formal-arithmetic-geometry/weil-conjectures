module

public import Sheaf.Paper.ModuleCupGodementTensorCoordinates

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Existence of the stalkwise pairing used in the coordinate construction.
Source: Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16.
(blueprint: new-module-cup-godement-tensor-stalk-pairing-exists)
The pairing sends germs represented on a common neighbourhood to the germ of the
sectionwise tensor. Compatibility under restriction makes this well-defined, and
bilinearity follows from bilinearity of the presheaf tensor product. -/
theorem moduleCup_godement_tensor_stalk_pairing_exists (X : Scheme.{u}) :
    ∃ t : ∀ (H K : X.Modules) (x : X),
      H.presheaf.stalk x → K.presheaf.stalk x → (H ⊗ K).presheaf.stalk x,
    ∀ (H K : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
        (s : Γ(H, U)) (r : Γ(K, U)),
      t H K x (H.presheaf.germ U x hx s) (K.presheaf.germ U x hx r) =
        (H ⊗ K).presheaf.germ U x hx
          ((moduleCup_sectionTensor X H K).app (op U)
            (s ⊗ₜ[Γ(X, U)] r)) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
