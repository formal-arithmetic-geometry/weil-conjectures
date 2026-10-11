module

public import Sheaf.CategoryTheory.PushoutShortExactSequence
public import WeilConjectures.AlgebraicGeometry.Modules.Ext

/-!
# Pushout of an extension and postcomposition in Ext

Source: Stacks Project, Homology Tag 010I and Derived Tag 06XP
(blueprint: lem-sc-p1-ext-pushout-postcompose).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Pushing out a short exact sequence along a coefficient morphism postcomposes
its extension class in `Ext`.
Source: Stacks Project, Homology Tag 010I and Derived Tag 06XP.
(blueprint: lem-sc-p1-ext-pushout-postcompose)

Proof: apply `CategoryTheory.pushout_short_exact_sequence`
(lem-weil-pbc-pushout-short-exact-sequence) to `S` and `φ`: it gives the projection
`p : B ⊔_A W ⟶ C` with `inl ≫ p = 0`, `inr ≫ p = S.g`, the short exactness of the pushed-out
sequence `0 → W → B ⊔_A W → C → 0`, and the morphism of short exact sequences
`(φ, inr, 𝟙 C)` from `S` to it. Apply the naturality of extension classes
(lem-sc-p1-ext-class-naturality; Mathlib `ShortComplex.ShortExact.extClass_naturality`)
to this morphism: `φ[1] ∘ [S] = [pushout] ∘ 𝟙_C`, and composition with the class of the
identity is the identity (`Ext.mk₀_id_comp`), so the class of the pushout is `φ[1] ∘ [S]`. -/
theorem pushout_extClass_postcompose {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (S : ShortComplex X.Modules)
    (hS : S.ShortExact) {W : X.Modules} (φ : S.X₁ ⟶ W) :
    ∃ p : pushout φ S.f ⟶ S.X₃, ∃ hz : pushout.inl φ S.f ≫ p = 0,
      pushout.inr φ S.f ≫ p = S.g ∧
      ∃ hp : (ShortComplex.mk (pushout.inl φ S.f) p hz).ShortExact,
      (hp.extClass : Ext S.X₃ W 1) = hS.extClass.comp (Abelian.Ext.mk₀ φ) (add_zero 1) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
