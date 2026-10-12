module
public import Sheaf.Algebra.LocallyFreeCharpoly
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Module.LinearMap.Prod

@[expose] public section
universe u v₁ v₂
namespace Algebra
/-- Product localizations of two unit-ideal covers admit the expected local bases.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1).
(blueprint: lem-weil-pbc-charpoly-locally-free-direct-sum-cover)
The product family generates the unit ideal by multiplying the two finite linear
combinations of one. Over each product localization, scalar extension of each
summand is free by the localization base-change tower; tensor products commute
with finite products, giving the displayed basis. -/
theorem locallyFreeCharpoly_prodCover
    {A : Type u} {M₁ : Type v₁} {M₂ : Type v₂} [CommRing A]
    [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
    {n₁ n₂ r₁ r₂ : ℕ} (f₁ : Fin r₁ → A) (f₂ : Fin r₂ → A)
    (hgen₁ : Ideal.span (Set.range f₁) = ⊤)
    (hgen₂ : Ideal.span (Set.range f₂) = ⊤)
    (hfree₁ : ∀ i : Fin r₁,
      ∃ _e : Module.Basis (Fin n₁) (Localization.Away (f₁ i))
        (LocalizedModule.Away (f₁ i) M₁), True)
    (hfree₂ : ∀ j : Fin r₂,
      ∃ _e : Module.Basis (Fin n₂) (Localization.Away (f₂ j))
        (LocalizedModule.Away (f₂ j) M₂), True) :
    let g : Fin (r₁ * r₂) → A := fun k ↦
      f₁ (finProdFinEquiv.symm k).1 * f₂ (finProdFinEquiv.symm k).2
    ∃ (hggen : Ideal.span (Set.range g) = ⊤)
      (hgfree : ∀ k : Fin (r₁ * r₂),
        ∃ _e : Module.Basis (Fin (n₁ + n₂)) (Localization.Away (g k))
          (LocalizedModule.Away (g k) (M₁ × M₂)), True), True := by
  sorry
end Algebra
