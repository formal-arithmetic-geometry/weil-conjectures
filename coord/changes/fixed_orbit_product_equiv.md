# fixed_orbit_product_equiv

## Reason
The unrestricted product comparison is false when the finite index family has a different cardinality. The caller constructs a compatible family, so the theorem requires that witness.

## Old
```lean
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
          AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)))
```

## New
```lean
theorem fixed_orbit_product_equiv
    (H C : Type u) [CommRing H] [CommRing C] [Algebra H C]
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (d : ℕ) (α : G →* Equiv.Perm (Fin d)) (D : FixedOrbitData G d)
    (hD : D.action = α) :
    ∀ (m : ℕ) (K : Fin m → Subgroup G),
      (∃ e : Fin m ≃ Fin D.m, ∀ k, K k = D.stabilizer (e k)) →
      Nonempty ((∀ k : Fin m,
        (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)) ≃ₐ[H]
      (∀ k : Fin D.m,
        (⨅ ζ : D.stabilizer k,
          AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)))
```

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantDescent | K4 | supplies the compatibility witness; adaptation is forced |

## Status
landed 20261014T022541-L-4043907 2026-10-14 (merge of deliver/B3/Sheaf.AlgebraicGeometry.Morphisms.FixedOrbitProductEquiv)
