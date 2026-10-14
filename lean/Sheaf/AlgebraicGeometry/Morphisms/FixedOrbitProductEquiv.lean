module

public import Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantAlgebra
public import Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentGeometric

@[expose] public section
universe u
set_option autoImplicit false
namespace AlgebraicGeometry.Scheme
/-- Proof: isolate the finite orbit-model construction and the comparison with supplied
fixed orbit data.
(blueprint: lem-sbc-fixed-orbit-product-equiv) -/
theorem fixed_orbit_product_equiv
    (H C : Type u) [CommRing H] [CommRing C] [Algebra H C]
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (d : ℕ) (α : G →* Equiv.Perm (Fin d)) (D : FixedOrbitData G d)
    (hD : D.action = α) :
    ∀ (m : ℕ) (K : Fin m → Subgroup G),
      Nonempty ((∀ k : Fin m,
        (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)) ≃ₐ[H]
      (∀ k : Fin D.m,
        (⨅ ζ : D.stabilizer k,
          AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C))) := by
  sorry


end AlgebraicGeometry.Scheme
