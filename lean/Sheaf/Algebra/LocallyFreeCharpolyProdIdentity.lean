module
public import Sheaf.Algebra.LocallyFreeCharpoly

@[expose] public section
universe u v₁ v₂
namespace Algebra
/-- The locally free characteristic polynomial of a product endomorphism factors
once a product cover and its local bases are supplied.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1).
(blueprint: lem-weil-pbc-charpoly-locally-free-direct-sum-identity)
After scalar extension to every product localization, the chosen local bases
identify the endomorphism with a block diagonal map; the free characteristic
polynomial identity gives equality there, and coefficientwise localization
injectivity gives equality over the original ring. -/
theorem locallyFreeCharpoly_prodIdentity
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
        (LocalizedModule.Away (f₂ j) M₂), True)
    (φ₁ : M₁ →ₗ[A] M₁) (φ₂ : M₂ →ₗ[A] M₂)
    {g : Fin (r₁ * r₂) → A}
    (hggen : Ideal.span (Set.range g) = ⊤)
    (hgfree : ∀ k : Fin (r₁ * r₂),
      ∃ _e : Module.Basis (Fin (n₁ + n₂)) (Localization.Away (g k))
        (LocalizedModule.Away (g k) (M₁ × M₂)), True)
    (hg : g = fun k ↦ f₁ (finProdFinEquiv.symm k).1 * f₂ (finProdFinEquiv.symm k).2) :
    locallyFreeCharpoly g hggen hgfree (φ₁.prodMap φ₂) =
      locallyFreeCharpoly f₁ hgen₁ hfree₁ φ₁ * locallyFreeCharpoly f₂ hgen₂ hfree₂ φ₂ := by
  sorry
end Algebra
