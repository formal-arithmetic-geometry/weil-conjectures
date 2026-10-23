/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.Supports

/-!
# The supported exterior product

For closed subschemes `i : Z ⟶ X`, `j : W ⟶ Y` of schemes over a field `k`, with projections
`p : X ×_k Y ⟶ X`, `q : X ×_k Y ⟶ Y`, the *supported exterior product*

`RΓ_Z(X, K) ⊗ᴸ RΓ_W(Y, L) ⟶ RΓ_{Z × W}(X ×_k Y, K ⊠ L)`

pulls back sections along the two projections and tensors them; their supports meet in
`Z × W` (`def-pur-supported-exterior-product`). Cohomology with supports is written
`RΓ_Z(X, K) = Ra_{X*}(Ri_! Ri^! K)`, as an object of `D((Spec k)_ét)`; the map is the Künneth map
(`AlgebraicGeometry.Etale.kunnethMap`) followed by the restriction of supports along `p`, `q`
(`AlgebraicGeometry.Etale.supportedRestriction`) and the product of supports
(`AlgebraicGeometry.Etale.supportedProduct`). Forgetting supports gives the ordinary exterior
product.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  {X Y Z W P Z₁ W₁ T : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hw : p₂ ≫ aY = p₁ ≫ aX)
  (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
  (i₁ : Z₁ ⟶ P) (g₁ : Z₁ ⟶ Z) (hg₁ : IsPullback g₁ i₁ i p₁)
  (j₁ : W₁ ⟶ P) (g₂ : W₁ ⟶ W) (hg₂ : IsPullback g₂ j₁ j p₂)
  [IsClosedImmersion i₁] [IsClosedImmersion j₁] (ι : T ⟶ P) [IsClosedImmersion ι]
  (h : Set.range ι.base = Set.range i₁.base ∩ Set.range j₁.base)

/-- Blueprint `def-pur-supported-exterior-product`: The supported exterior product

Let `P = X ×_k Y` with projections `p₁`, `p₂` (any square `p₂ ≫ a_Y = p₁ ≫ a_X`), let
`i : Z ⟶ X`, `j : W ⟶ Y` be closed immersions with preimages `i₁ : Z₁ ⟶ P`, `j₁ : W₁ ⟶ P`, and
`ι : T ⟶ P` a closed immersion onto their intersection `Z × W`. The supported exterior product

`κ^{Z,W}_{K,L} : RΓ_Z(X, K) ⊗ᴸ RΓ_W(Y, L) ⟶ RΓ_{Z × W}(X ×_k Y, K ⊠ L)`,

with `RΓ_Z(X, K) = Ra_{X*}(Ri_! Ri^! K)` in `D((Spec k)_ét)`, is the Künneth map at
`Ri_! Ri^! K` and `Rj_! Rj^! L`, followed by `Rc_*` of the restriction of supports along the
projections and of the product of supports
`Ri₁_! Ri₁^! p₁^*K ⊗ Rj₁_! Rj₁^! p₂^*L ⟶ Rι_! Rι^!(K ⊠ L)`. -/
noncomputable def supportedExteriorProduct
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  kunnethMap (ModuleCat.{u + 1} Λ) p₁ p₂ aX aY (p₁ ≫ aX) rfl hw
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj K))
      ((R(j)_![ModuleCat.{u + 1} Λ]).obj ((R(j)^![ModuleCat.{u + 1} Λ]).obj L)) ≫
    (R((p₁ ≫ aX)_*[ModuleCat.{u + 1} Λ])).map
      (derivedTensorHom (ModuleCat.{u + 1} Λ)
          (supportedRestriction (ModuleCat.{u + 1} Λ) p₁ i i₁ g₁ hg₁ K _ (Iso.refl _))
          (supportedRestriction (ModuleCat.{u + 1} Λ) p₂ j j₁ g₂ hg₂ L _ (Iso.refl _)) ≫
        supportedProduct (ModuleCat.{u + 1} Λ) i₁ j₁ ι h _ _)

end AlgebraicGeometry.Etale
