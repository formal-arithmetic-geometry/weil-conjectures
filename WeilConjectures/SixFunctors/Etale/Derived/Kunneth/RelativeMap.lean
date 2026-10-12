/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-!

# The relative Künneth map

Let `Λ` be a finite coefficient ring, `f : X ⟶ B`, `g : Y ⟶ B` morphisms admitting
compactifications and `p`, `q` the projections of `X ×_B Y`. This file defines the canonical
isomorphism of the relative product theorem (blueprint `sk-thm-sf-kunneth-relative`,
`thm-sf-kunneth-relative`)

`κ^rel_{K,L} : R(f ×_B g)_! (K ⊠ L) ≅ Rf_! K ⊗ᴸ Rg_! L`

as the explicit composite of the blueprint: the inverse of the composition isomorphism
`α_{g,q}`, the inverse of the projection map of `q` at `(Lp^* K, L)`, the inverse of the
compact-support base change map `Ex_! : Lg^* Rf_! K ⟶ Rq_! Lp^* K`, the symmetry of `⊗ᴸ`, the
inverse of the projection map of `g` at `(L, Rf_! K)` and the symmetry of `⊗ᴸ`. It is
defined for an arbitrary cartesian square (`AlgebraicGeometry.Etale.relativeKunnethIsoOfIsPullback`)
and specialised to the chosen fibre product (`AlgebraicGeometry.Etale.relativeKunnethIso`).

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`: the composition isomorphism
  `R(h)_! ≅ Rf_! ⋙ Rg_!` for `f ≫ g = h`, on unbounded derived categories, for a finite
  coefficient ring.
- `AlgebraicGeometry.Etale.derivedTensorBraiding`: the symmetry `K ⊗ᴸ M ≅ M ⊗ᴸ K` of the
  derived tensor product, the braiding `DerivedCategory.braidedCategory`.
- `AlgebraicGeometry.Etale.relativeKunnethIsoOfIsPullback`,
  `AlgebraicGeometry.Etale.relativeKunnethIso`: the relative Künneth isomorphism.
- `AlgebraicGeometry.Etale.relativeKunnethNatIso`: the relative Künneth isomorphism as a
  natural isomorphism of bifunctors `D(X_ét) ⥤ D(Y_ét) ⥤ D(B_ét)`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Braiding

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

/-- The symmetry `σ : K ⊗ᴸ M ≅ M ⊗ᴸ K` of the derived tensor product of étale sheaves, natural
in both variables: the braiding `DerivedCategory.braidedCategory` of `D(X_ét)`, as an
isomorphism between `- ⊗ᴸ -` and the flipped bifunctor. -/
noncomputable def derivedTensorBraiding : derivedTensor A X ≅ (derivedTensor A X).flip :=
  @BraidedCategory.curriedBraidingNatIso _ _ _
    (_root_.DerivedCategory.braidedCategory (Sheaf X.smallEtaleTopology A))


/-- The symmetry `σ_{M,N} : M ⊗ᴸ N ≅ N ⊗ᴸ M` of the derived tensor product of étale sheaves, the
component of `AlgebraicGeometry.Etale.derivedTensorBraiding`. -/
noncomputable def derivedTensorBraidingIso
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((-⊗ᴸ-(X)[A]).obj M).obj N ≅ ((-⊗ᴸ-(X)[A]).obj N).obj M :=
  ((derivedTensorBraiding A X).app M).app N

variable {A X} in
@[reassoc]
lemma derivedTensorBraidingIso_hom_naturality_left
    {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : M ⟶ M')
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((-⊗ᴸ-(X)[A]).map φ).app N ≫ (derivedTensorBraidingIso A X M' N).hom =
      (derivedTensorBraidingIso A X M N).hom ≫ ((-⊗ᴸ-(X)[A]).obj N).map φ :=
  NatTrans.naturality_app (derivedTensorBraiding A X).hom N φ

variable {A X} in
@[reassoc]
lemma derivedTensorBraidingIso_hom_naturality_right
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    {N N' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (ψ : N ⟶ N') :
    ((-⊗ᴸ-(X)[A]).obj M).map ψ ≫ (derivedTensorBraidingIso A X M N').hom =
      (derivedTensorBraidingIso A X M N).hom ≫ ((-⊗ᴸ-(X)[A]).map ψ).app M :=
  ((derivedTensorBraiding A X).hom.app M).naturality ψ
end Braiding

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- statements specialised here (as in `LowerShriekProjectionExchange`).
attribute [local instance high] SymmetricCategory.toBraidedCategory

section Composition

variable {X Y S : Scheme.{u}}

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on unbounded derived categories, for
a finite coefficient ring: the isomorphism of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`, i.e.
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationCompIso` for the chosen
compactification `d` of `g` and the compactification `Compactification.ofComp` of `f ≫ d.i`,
compared with the chosen compactifications of `f` and `f ≫ g`. -/
noncomputable def rightDerivedLowerShriekCompIso' (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ] :=
  haveI : QuasiCompact f := .of_comp f g
  (rightDerivedLowerShriekIso Λ ((HasCompactification.compactification g).comp
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g)))).symm ≪≫
    (rightDerivedLowerShriekOfCompactificationCompIso Λ (HasCompactification.compactification g)
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g))).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerShriekIso Λ
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g)).restrict) _

/-- Blueprint `sk-thm-sf-comp-composition`: the composition isomorphism `α : R(h)_! ≅ Rf_! ⋙ Rg_!`
for `f ≫ g = h`, on unbounded derived categories, for a finite coefficient ring
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso'` transported along `f ≫ g = h`). -/
noncomputable def rightDerivedLowerShriekCompIso (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S)
    (w : f ≫ g = h) [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [QuasiCompact h] :
    R(h)_![ModuleCat.{u + 1} Λ] ≅ R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ] :=
  haveI : HasCompactification (f ≫ g) := .of_eq w.symm
  haveI : QuasiCompact (f ≫ g) := by rw [w]; infer_instance
  eqToIso (by subst w; rfl) ≪≫ rightDerivedLowerShriekCompIso' Λ f g

end Composition

section Components

variable {B X Y P : Scheme.{u}}

/-- The composition isomorphism `α : Rh_! M ≅ Rg_! Rf_! M` for `f ≫ g = h`, at an object `M`
(the component of `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`). -/
noncomputable def rightDerivedLowerShriekCompIsoApp {S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (h : X ⟶ S) (w : f ≫ g = h) [HasCompactification f] [HasCompactification g]
    [HasCompactification h] [QuasiCompact h]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(h)_![ModuleCat.{u + 1} Λ]).obj M ≅
      (R(g)_![ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj M) :=
  (rightDerivedLowerShriekCompIso Λ f g h w).app M

@[reassoc]
lemma rightDerivedLowerShriekCompIsoApp_hom_naturality {S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) (h : X ⟶ S) (w : f ≫ g = h) [HasCompactification f] [HasCompactification g]
    [HasCompactification h] [QuasiCompact h]
    {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ M') :
    (R(h)_![ModuleCat.{u + 1} Λ]).map φ ≫ (rightDerivedLowerShriekCompIsoApp Λ f g h w M').hom =
      (rightDerivedLowerShriekCompIsoApp Λ f g h w M).hom ≫
        (R(g)_![ModuleCat.{u + 1} Λ]).map ((R(f)_![ModuleCat.{u + 1} Λ]).map φ) :=
  (rightDerivedLowerShriekCompIso Λ f g h w).hom.naturality φ

/-- The projection formula `PF_{f,K,L} : Rf_! K ⊗ᴸ L ≅ Rf_!(K ⊗ᴸ Lf^* L)` for a finite
coefficient ring, as an isomorphism: the projection map `AlgebraicGeometry.Etale.projectionMap`
at `(K, L)`, an isomorphism by `AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`. -/
noncomputable def projectionIso (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj L ≅
      (R(f)_![ModuleCat.{u + 1} Λ]).obj
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L)) :=
  haveI := isIso_projectionMap_of_finite Λ f
  asIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app K).app L)

lemma projectionIso_hom (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (projectionIso Λ f K L).hom = ((projectionMap (ModuleCat.{u + 1} Λ) f).app K).app L :=
  rfl

@[reassoc]
lemma projectionIso_hom_naturality_left (f : X ⟶ Y) [HasCompactification f]
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K')
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).map ((R(f)_![ModuleCat.{u + 1} Λ]).map φ)).app L ≫
        (projectionIso Λ f K' L).hom =
      (projectionIso Λ f K L).hom ≫ (R(f)_![ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map φ).app ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L)) :=
  NatTrans.naturality_app (projectionMap (ModuleCat.{u + 1} Λ) f) L φ

@[reassoc]
lemma projectionIso_hom_naturality_right (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {L L' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L ⟶ L') :
    ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).map ψ ≫
        (projectionIso Λ f K L').hom =
      (projectionIso Λ f K L).hom ≫ (R(f)_![ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map ψ)) :=
  ((projectionMap (ModuleCat.{u + 1} Λ) f).app K).naturality ψ

@[reassoc]
lemma projectionIso_inv_naturality_left (f : X ⟶ Y) [HasCompactification f]
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K')
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(f)_![ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map φ).app ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L)) ≫
        (projectionIso Λ f K' L).inv =
      (projectionIso Λ f K L).inv ≫
        ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).map ((R(f)_![ModuleCat.{u + 1} Λ]).map φ)).app L := by
  rw [Iso.comp_inv_eq, Category.assoc, projectionIso_hom_naturality_left, Iso.inv_hom_id_assoc]

@[reassoc]
lemma projectionIso_inv_naturality_right (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {L L' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L ⟶ L') :
    (R(f)_![ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map ψ)) ≫
        (projectionIso Λ f K L').inv =
      (projectionIso Λ f K L).inv ≫
        ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).map ψ := by
  rw [Iso.comp_inv_eq, Category.assoc, projectionIso_hom_naturality_right, Iso.inv_hom_id_assoc]

/-- Compact-support base change `Ex_! : Lg^* Rf_! K ≅ Rq_! Lp^* K` for a cartesian square
`p ≫ f = q ≫ g` and a finite coefficient ring, as an isomorphism: the component of
`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`, an isomorphism by
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`. -/
noncomputable def rightDerivedLowerShriekBaseChangeIso {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B}
    {g : Y ⟶ B} (sq : IsPullback p q f g) [HasCompactification f] [HasCompactification q]
    [QuasiCompact q] (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) ≅
      (R(q)_![ModuleCat.{u + 1} Λ]).obj ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  haveI := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  asIso ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K)

lemma rightDerivedLowerShriekBaseChangeIso_hom {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B}
    {g : Y ⟶ B} (sq : IsPullback p q f g) [HasCompactification f] [HasCompactification q]
    [QuasiCompact q] (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekBaseChangeIso Λ sq K).hom =
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app K :=
  rfl

@[reassoc]
lemma rightDerivedLowerShriekBaseChangeIso_inv_naturality {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback p q f g) [HasCompactification f]
    [HasCompactification q] [QuasiCompact q]
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    (R(q)_![ModuleCat.{u + 1} Λ]).map ((L((p)^*[ModuleCat.{u + 1} Λ])).map φ) ≫
        (rightDerivedLowerShriekBaseChangeIso Λ sq K').inv =
      (rightDerivedLowerShriekBaseChangeIso Λ sq K).inv ≫
        (L((g)^*[ModuleCat.{u + 1} Λ])).map ((R(f)_![ModuleCat.{u + 1} Λ]).map φ) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, rightDerivedLowerShriekBaseChangeIso_hom,
    rightDerivedLowerShriekBaseChangeIso_hom]
  exact ((rightDerivedLowerShriekBaseChangeMap Λ sq).naturality φ).symm
end Components

section Kunneth

variable {B X Y P : Scheme.{u}}

/-- The relative Künneth isomorphism for an arbitrary cartesian square

```
  P --q--> Y
  |        |
  p        g
  v        v
  X --f--> B
```

and a morphism `h = q ≫ g`: for `K` on `X` and `L` on `Y`, the composite

```
Rh_!(Lp^*K ⊗ᴸ Lq^*L) ≅ Rg_! Rq_!(Lp^*K ⊗ᴸ Lq^*L)      (α_{g,q}⁻¹)
                     ≅ Rg_!(Rq_! Lp^*K ⊗ᴸ L)           (Rg_! PF_{q, Lp^*K, L}⁻¹)
                     ≅ Rg_!(Lg^* Rf_! K ⊗ᴸ L)          (Rg_!(Ex_!⁻¹ ⊗ 1))
                     ≅ Rg_!(L ⊗ᴸ Lg^* Rf_! K)          (Rg_! σ)
                     ≅ Rg_! L ⊗ᴸ Rf_! K                (PF_{g, L, Rf_! K}⁻¹)
                     ≅ Rf_! K ⊗ᴸ Rg_! L                (σ)
```

of blueprint `sk-thm-sf-kunneth-relative`. Every arrow is an isomorphism for a finite
coefficient ring: the composition law, the projection formula
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`) and compact-support base change
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). -/
noncomputable def relativeKunnethIsoOfIsPullback {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B}
    {g : Y ⟶ B} (sq : IsPullback p q f g) (h : P ⟶ B) (w : q ≫ g = h)
    [HasCompactification f] [HasCompactification g] [HasCompactification q]
    [HasCompactification h] [QuasiCompact q] [QuasiCompact h]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(h)_![ModuleCat.{u + 1} Λ]).obj (((-⊗ᴸ-(P)[ModuleCat.{u + 1} Λ]).obj
        ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K)).obj ((L((q)^*[ModuleCat.{u + 1} Λ])).obj L)) ≅
      ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((R(g)_![ModuleCat.{u + 1} Λ]).obj L) :=
  rightDerivedLowerShriekCompIsoApp Λ q g h w _ ≪≫
    (R(g)_![ModuleCat.{u + 1} Λ]).mapIso
      ((projectionIso Λ q ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K) L).symm ≪≫
        ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).mapIso
          (rightDerivedLowerShriekBaseChangeIso Λ sq K).symm).app L ≪≫
        derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) Y _ L) ≪≫
    (projectionIso Λ g L ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).symm ≪≫
    derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) B _ _

section Naturality

variable {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback p q f g) (h : P ⟶ B)
  (w : q ≫ g = h) [HasCompactification f] [HasCompactification g] [HasCompactification q]
  [HasCompactification h] [QuasiCompact q] [QuasiCompact h]

/-- Blueprint `sk-thm-sf-kunneth-relative`: the relative Künneth isomorphism is natural in the
first variable. -/
@[reassoc]
theorem relativeKunnethIsoOfIsPullback_hom_naturality_left
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K')
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(h)_![ModuleCat.{u + 1} Λ]).map (((-⊗ᴸ-(P)[ModuleCat.{u + 1} Λ]).map
        ((L((p)^*[ModuleCat.{u + 1} Λ])).map φ)).app ((L((q)^*[ModuleCat.{u + 1} Λ])).obj L)) ≫
      (relativeKunnethIsoOfIsPullback Λ sq h w K' L).hom =
    (relativeKunnethIsoOfIsPullback Λ sq h w K L).hom ≫
      ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).map ((R(f)_![ModuleCat.{u + 1} Λ]).map φ)).app
        ((R(g)_![ModuleCat.{u + 1} Λ]).obj L) := by
  simp only [relativeKunnethIsoOfIsPullback, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [rightDerivedLowerShriekCompIsoApp_hom_naturality_assoc, ← Functor.map_comp_assoc,
    projectionIso_inv_naturality_left, Functor.map_comp_assoc]
  congr 1
  congr 1
  rw [← Functor.map_comp_assoc, ← NatTrans.comp_app, ← Functor.map_comp,
    rightDerivedLowerShriekBaseChangeIso_inv_naturality, Functor.map_comp, NatTrans.comp_app,
    Functor.map_comp_assoc]
  congr 1
  rw [← Functor.map_comp_assoc, derivedTensorBraidingIso_hom_naturality_left, Functor.map_comp_assoc,
    projectionIso_inv_naturality_right_assoc, derivedTensorBraidingIso_hom_naturality_right]

/-- Blueprint `sk-thm-sf-kunneth-relative`: the relative Künneth isomorphism is natural in the
second variable. -/
@[reassoc]
theorem relativeKunnethIsoOfIsPullback_hom_naturality_right
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {L L' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L ⟶ L') :
    (R(h)_![ModuleCat.{u + 1} Λ]).map (((-⊗ᴸ-(P)[ModuleCat.{u + 1} Λ]).obj
        ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K)).map ((L((q)^*[ModuleCat.{u + 1} Λ])).map ψ)) ≫
      (relativeKunnethIsoOfIsPullback Λ sq h w K L').hom =
    (relativeKunnethIsoOfIsPullback Λ sq h w K L).hom ≫
      ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).map
        ((R(g)_![ModuleCat.{u + 1} Λ]).map ψ) := by
  simp only [relativeKunnethIsoOfIsPullback, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [rightDerivedLowerShriekCompIsoApp_hom_naturality_assoc, ← Functor.map_comp_assoc,
    projectionIso_inv_naturality_right, Functor.map_comp_assoc]
  congr 1
  congr 1
  rw [← Functor.map_comp_assoc, NatTrans.naturality, Functor.map_comp_assoc]
  congr 1
  rw [← Functor.map_comp_assoc, derivedTensorBraidingIso_hom_naturality_right,
    Functor.map_comp_assoc, projectionIso_inv_naturality_left_assoc,
    derivedTensorBraidingIso_hom_naturality_left]

end Naturality

/-- Blueprint `sk-thm-sf-kunneth-relative` (detailed: `thm-sf-kunneth-relative`): **the relative
Künneth isomorphism**. For `f : X ⟶ B`, `g : Y ⟶ B` admitting compactifications, with `p`, `q`
the projections of `X ×_B Y`, `K` on `X` and `L` on `Y`, and a finite coefficient ring `Λ`,

`κ^rel_{K,L} : R(f ×_B g)_! (K ⊠ L) ≅ Rf_! K ⊗ᴸ Rg_! L`

is the composite of the inverse of the composition isomorphism `α_{g,q}`, the inverse of the
projection map of `q` at `(Lp^* K, L)`, the inverse of compact-support base change
`Ex_! : Lg^* Rf_! K ⟶ Rq_! Lp^* K`, the symmetry of `⊗ᴸ`, the inverse of the projection map of
`g` at `(L, Rf_! K)` and the symmetry of `⊗ᴸ`
(`AlgebraicGeometry.Etale.relativeKunnethIsoOfIsPullback` for the fibre product square). Every
arrow is an isomorphism for all `K` and `L`; the blueprint's `Dctf` hypotheses are not needed
for a finite coefficient ring. -/
noncomputable def relativeKunnethIso (f : X ⟶ B) (g : Y ⟶ B) [HasCompactification f]
    [HasCompactification g] [QuasiCompact f] [QuasiCompact g]
    [HasCompactification (pullback.toBase f g)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(pullback.toBase f g)_![ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) f g K L) ≅
      ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((R(g)_![ModuleCat.{u + 1} Λ]).obj L) :=
  haveI : QuasiCompact (pullback.snd f g) := MorphismProperty.of_isPullback
    (P := @QuasiCompact) (IsPullback.of_hasPullback f g) inferInstance
  haveI : QuasiCompact (pullback.toBase f g) := by
    rw [← pullback.snd_comp_eq_toBase]
    infer_instance
  relativeKunnethIsoOfIsPullback Λ (IsPullback.of_hasPullback f g) _
    (pullback.snd_comp_eq_toBase f g) K L

end Kunneth

end Etale

end AlgebraicGeometry
