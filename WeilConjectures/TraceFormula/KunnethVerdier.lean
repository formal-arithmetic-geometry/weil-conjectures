/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.TraceFormula.Product

/-!

# External products and the Künneth–Verdier map

Let `X, Y` be separated `k`-schemes of finite type, with projections `p_X : X ⨯ Y ⟶ X` and
`p_Y : X ⨯ Y ⟶ Y` of their product over the base point. The *external product* of
`M ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` and `N ∈ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` is `M ⊠ N = Lp_X^* M ⊗ Lp_Y^* N`
(`ProEtale.CondensedRing.externalProduct`, blueprint `def-trf-external-product`).

The *Künneth–Verdier map* (blueprint `def-sf-kv-maps`, (iv))
```
κ_{M,N} : M ⊠ D_Y N ⟶ RHom(Lp_Y^* N, Rp_X^! M)
```
(`ProEtale.CondensedRing.kunnethVerdierMap`) is the transpose of
```
Lp_Y^* N ⊗ (Lp_X^* M ⊗ Lp_Y^* D_Y N) ≅ Lp_X^* M ⊗ (Lp_Y^* N ⊗ Lp_Y^* D_Y N)
  ⟶ Lp_X^* M ⊗ Lp_Y^* (N ⊗ D_Y N) --ev--> Lp_X^* M ⊗ Lp_Y^* ω_Y --α--> Rp_X^! M,
```
where `α = α_{𝟙, a_Y}` is the *exceptional Künneth map* (blueprint `def-sf-kv-maps`, (ii);
`ProEtale.CondensedRing.exceptionalKunnethMap`): the exceptional adjoint of
```
Rp_X! (Lp_X^* M ⊗ Lp_Y^* ω_Y) ≅ Rp_X! (Lp_Y^* ω_Y ⊗ Lp_X^* M) ≅ Rp_X! (Lp_Y^* ω_Y) ⊗ M
  ≅ La_X^* Ra_Y! ω_Y ⊗ M --ε--> La_X^* ℚ̄_ℓ ⊗ M ≅ M,
```
built from the derived projection formula for `p_X`, compact-support base change in the
cartesian square of the product, and the counit of `Ra_Y! ⊣ Ra_Y^!`; this is the composite
`Ku_!` of `def-sf-kv-maps` (i) for the pair `(𝟙_X, a_Y)` followed by the counits. Its
invertibility is the Künneth–Verdier theorem (blueprint `thm-trf-kunneth-verdier`), recorded
here as the sorried input `ProEtale.CondensedRing.isIso_kunnethVerdierMap`.

All constructions are classical: ordinary categories and natural transformations built by
composition, whiskering and mates from the data of the six functors (blueprint
`rem-trf-classical-framework`).

## Main definitions

- `ProEtale.CondensedRing.externalProduct`: the external product `M ⊠ N`.
- `ProEtale.CondensedRing.exceptionalKunnethMap`: `α_{𝟙, a_Y} : M ⊠ ω_Y ⟶ Rp_X^! M`.
- `ProEtale.CondensedRing.kunnethVerdierMap`: `κ_{M,N}`.

## Sorried input

- `ProEtale.CondensedRing.isIso_kunnethVerdierMap`: the Künneth–Verdier theorem (blueprint
  `thm-trf-kunneth-verdier`, section `sec-six-functors`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The *external product* `M ⊠ N = Lp_X^* M ⊗ Lp_Y^* N` on `X ⨯ Y` (blueprint
`def-trf-external-product`), with the projections `p_X = prod.fst` and `p_Y = prod.snd`; the
order of the factors is part of the notation. -/
noncomputable def externalProduct (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Dᵇc((X ⨯ Y).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M ⊗
    (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N

variable (X Y) in
/-- Compact-support base change for the product square, inverted:
`Rp_X! ⋙ ... : Lp_Y^* ⋙ Rp_X! ≅ Ra_Y! ⋙ La_X^*`. -/
noncomputable def prodBaseChangeIso :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ Y ⟶ Y) ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.fst : X ⨯ Y ⟶ X) ≅
      boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Y) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) :=
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    (isPullback_prod_toPoint X Y)
  (asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    (isPullback_prod_toPoint X Y))).symm

/-- The morphism `Rp_X! (Lp_X^* M ⊗ Lp_Y^* ω_Y) ⟶ M` whose exceptional adjoint is the exceptional
Künneth map: the tensor symmetry, the inverse of the projection formula for `p_X`, the inverse
of compact-support base change in the product square, the counit of `Ra_Y! ⊣ Ra_Y^!` and the
unit isomorphism of the monoidal functor `La_X^*`. -/
noncomputable def exceptionalKunnethAdjoint (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj
        (externalProduct ℓ M (dualizingComplex' ℓ Y)) ⟶ M :=
  (boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map (β_ _ _).hom ≫
    inv (((boundedConstructibleExceptionalProjection _ ℓ (prod.fst : X ⨯ Y ⟶ X)).app
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
        (dualizingComplex' ℓ Y))).app M) ≫
    ((prodBaseChangeIso ℓ X Y).hom.app (dualizingComplex' ℓ Y) ▷ M) ≫
    ((boundedConstructibleUpperStar _ ℓ (toPoint X)).map
      ((boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint Y)).counit.app (𝟙_ _)) ▷ M) ≫
    ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv ▷ M) ≫
    (λ_ M).hom

/-- The *exceptional Künneth map* `α_{𝟙, a_Y} : M ⊠ ω_Y ⟶ Rp_X^! M` (blueprint `def-sf-kv-maps`,
(ii), for `f₁ = 𝟙_X`, `f₂ = a_Y`, `L₁ = M`, `L₂ = ℚ̄_ℓ`): the exceptional adjoint of
`exceptionalKunnethAdjoint`. -/
noncomputable def exceptionalKunnethMap (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ M (dualizingComplex' ℓ Y) ⟶
      (boundedConstructibleUpperShriek _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M :=
  (boundedConstructibleUpperShriekAdjunction _ ℓ (prod.fst : X ⨯ Y ⟶ X)).homEquiv _ _
    (exceptionalKunnethAdjoint ℓ M)

/-- The pairing `Lp_Y^* N ⊗ (M ⊠ D_Y N) ⟶ Rp_X^! M` whose transpose is the Künneth–Verdier map:
the symmetry moving `Lp_Y^* N` next to `Lp_Y^* D_Y N`, the monoidal structure of `Lp_Y^*`, the
evaluation `N ⊗ D_Y N ⟶ ω_Y` and the exceptional Künneth map. -/
noncomputable def kunnethVerdierPairing (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N ⊗
        externalProduct ℓ M (verdierDual ℓ (toPoint Y) N) ⟶
      (boundedConstructibleUpperShriek _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M :=
  (α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
    (_ ◁ Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)) _ _) ≫
    (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map
      ((ihom.ev N).app (dualizingComplex' ℓ Y))) ≫
    exceptionalKunnethMap ℓ M

/-- The *Künneth–Verdier map* `κ_{M,N} : M ⊠ D_Y N ⟶ RHom(Lp_Y^* N, Rp_X^! M)` (blueprint
`def-sf-kv-maps`, (iv)): the transpose of `kunnethVerdierPairing`, that is the external Hom map
`β` of the two evaluations followed by the exceptional Künneth map `α_{𝟙, a_Y}`. -/
noncomputable def kunnethVerdierMap (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ M (verdierDual ℓ (toPoint Y) N) ⟶
      (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N)).obj
        ((boundedConstructibleUpperShriek _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M) :=
  curry (kunnethVerdierPairing ℓ M N)

/-- **The Künneth–Verdier isomorphism** (blueprint `thm-trf-kunneth-verdier`, section
`sec-six-functors`): for bounded constructible `M` on `X` and `N` on `Y`, the Künneth–Verdier map
`κ_{M,N} : M ⊠ D_Y N ⟶ RHom(Lp_Y^* N, Rp_X^! M)` is an isomorphism. -/
instance isIso_kunnethVerdierMap (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (kunnethVerdierMap ℓ M N) :=
  sorry

/-- The double-dual morphism is natural, for any braiding. -/
private lemma bidualityMap_naturality {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞]
    [MonoidalClosed 𝒞] {_ : BraidedCategory 𝒞} (ω : 𝒞) {M M' : 𝒞} (f : M ⟶ M') :
    f ≫ Verdier.bidualityMap ω M' = Verdier.bidualityMap ω M ≫ (pre ((pre f).app ω)).app ω :=
  toIhomIhom_naturality ω f

/-- **Verdier biduality for the dualizing complex** (blueprint `thm-trf-verdier-biduality`): for
bounded constructible `M` on `Y`, the double-dual morphism `M ⟶ D_Y D_Y M`, the transpose of the
evaluation `D_Y M ⊗ M ⟶ M ⊗ D_Y M ⟶ ω_Y`, is an isomorphism. It is the constructible biduality
theorem (`isIso_verdierBiduality`, blueprint `thm-coef-qbar-verdier`). -/
noncomputable def verdierBidualityIso (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    M ≅ verdierDual ℓ (toPoint Y) (verdierDual ℓ (toPoint Y) M) :=
  haveI := isIso_verdierBiduality ℓ (toPoint Y) M
  asIso (verdierBiduality ℓ (toPoint Y) M)

lemma verdierBidualityIso_hom (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (verdierBidualityIso ℓ M).hom = verdierBiduality ℓ (toPoint Y) M :=
  rfl

/-- The biduality isomorphism is natural (blueprint `thm-trf-verdier-biduality`). -/
@[reassoc]
lemma verdierBidualityIso_hom_naturality {M M' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (f : M ⟶ M') :
    f ≫ (verdierBidualityIso ℓ M').hom =
      (verdierBidualityIso ℓ M).hom ≫
        (pre ((pre f).app (dualizingComplex' ℓ Y))).app (dualizingComplex' ℓ Y) :=
  bidualityMap_naturality _ f

end AlgebraicGeometry.ProEtale.CondensedRing
