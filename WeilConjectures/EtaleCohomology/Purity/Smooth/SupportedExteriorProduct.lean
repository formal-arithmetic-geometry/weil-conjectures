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
  {X Y Z W T : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
  (ι : T ⟶ pullback aX aY) [IsClosedImmersion ι]

/-- Blueprint `def-pur-supported-exterior-product`: The supported exterior product

For closed immersions `i : Z ⟶ X`, `j : W ⟶ Y` over a field `k` and a closed immersion
`ι : T ⟶ X ×_k Y` onto `Z × W` (`h`: the range of `ι` is the intersection of the preimages of `Z`
and `W`), the supported exterior product

`κ^{Z,W}_{K,L} : RΓ_Z(X, K) ⊗ᴸ RΓ_W(Y, L) ⟶ RΓ_{Z × W}(X ×_k Y, K ⊠ L)`,

with `RΓ_Z(X, K) = Ra_{X*}(Ri_! Ri^! K)` in `D((Spec k)_ét)`: the Künneth map at
`Ri_! Ri^! K` and `Rj_! Rj^! L`, followed by `Rc_*` of the restriction of supports along the
projections and of the product of supports `Ri'_! Ri'^! p^*K ⊗ Rj'_! Rj'^! q^*L ⟶
Rι_! Rι^!(K ⊠ L)`. -/
noncomputable def supportedExteriorProduct
    (h : Set.range ι.base = Set.range (pullback.snd i (pullback.fst aX aY)).base ∩
      Set.range (pullback.snd j (pullback.snd aX aY)).base)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        ((R((aX)_*[ModuleCat.{u + 1} Λ])).obj
          ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj K)))).obj
        ((R((aY)_*[ModuleCat.{u + 1} Λ])).obj
          ((R(j)_![ModuleCat.{u + 1} Λ]).obj ((R(j)^![ModuleCat.{u + 1} Λ]).obj L))) ⟶
      (R((pullback.fst aX aY ≫ aX)_*[ModuleCat.{u + 1} Λ])).obj
        ((R(ι)_![ModuleCat.{u + 1} Λ]).obj ((R(ι)^![ModuleCat.{u + 1} Λ]).obj
          (((derivedTensor (ModuleCat.{u + 1} Λ) (pullback aX aY)).obj
            ((L((pullback.fst aX aY)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
              ((L((pullback.snd aX aY)^*[ModuleCat.{u + 1} Λ])).obj L)))) :=
  kunnethMap (ModuleCat.{u + 1} Λ) (pullback.fst aX aY) (pullback.snd aX aY) aX aY
      (pullback.fst aX aY ≫ aX) rfl pullback.condition.symm _ _ ≫
    (R((pullback.fst aX aY ≫ aX)_*[ModuleCat.{u + 1} Λ])).map
      (derivedTensorHom (ModuleCat.{u + 1} Λ)
          (supportedRestriction (ModuleCat.{u + 1} Λ) (pullback.fst aX aY) i
            (pullback.snd i (pullback.fst aX aY)) (pullback.fst i (pullback.fst aX aY))
            (IsPullback.of_hasPullback _ _) K _ (Iso.refl _))
          (supportedRestriction (ModuleCat.{u + 1} Λ) (pullback.snd aX aY) j
            (pullback.snd j (pullback.snd aX aY)) (pullback.fst j (pullback.snd aX aY))
            (IsPullback.of_hasPullback _ _) L _ (Iso.refl _)) ≫
        supportedProduct (ModuleCat.{u + 1} Λ) _ _ ι h _ _)

end AlgebraicGeometry.Etale
