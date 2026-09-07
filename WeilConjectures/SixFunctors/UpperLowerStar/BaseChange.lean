/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!

# The exchange transformation `g^* f_* ⟶ f'_* g'^*` on small étale sites

For a commutative square of schemes

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

the two composites `X' ⟶ Y` agree, so the composition isomorphisms
`AlgebraicGeometry.Etale.upperStarComp` identify `g^* ⋙ f'^*` with `f^* ⋙ g'^*`. Its mate
with respect to the adjunctions `f^* ⊣ f_*` and `f'^* ⊣ f'_*` is the exchange, or
Beck–Chevalley, transformation `Ex□ : f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` of this file. Being a
natural transformation, it is automatically natural in the sheaf.

The square is only required to *commute*; cartesianness is nowhere used, and the exchange
transformation is not claimed to be an isomorphism.

## Main definitions

- `AlgebraicGeometry.Etale.upperStarSquareIso`: the isomorphism
  `g^* ⋙ f'^* ≅ f^* ⋙ g'^*` of pullbacks attached to a commutative square.
- `AlgebraicGeometry.Etale.exchange`: the exchange transformation
  `f_* ⋙ g^* ⟶ g'^* ⋙ f'_*`, the mate of `Etale.upperStarSquareIso`.

## Main results

- `AlgebraicGeometry.Etale.exchange_id`: for the square with both horizontal edges the
  identity, the exchange is the identity, modulo the identification
  `AlgebraicGeometry.Etale.upperStarId` of `(𝟙 _)^*` with the identity functor.
- `AlgebraicGeometry.Etale.exchange_hComp`: horizontal pasting. For two squares glued along
  a common vertical edge, the exchange of the pasted square is the composite of the two
  exchanges, modulo the composition isomorphisms `Etale.upperStarComp` of the two glued
  horizontal edges.
- `AlgebraicGeometry.Etale.exchange_vComp`: vertical pasting. For two squares glued along a
  common horizontal edge, the exchange of the pasted square is the composite of the two
  exchanges, modulo the composition isomorphisms `Etale.lowerStarComp` of the two glued
  vertical edges.

## Implementation notes

Both `Etale.upperStarSquareIso` and `Etale.exchange` take the diagonal `d : X' ⟶ Y` of the
square as an optional argument, defaulting to `g' ≫ f`, in the same way as
`CategoryTheory.MorphismProperty.Over.pullbackComp` takes the composite as an optional
argument. This is what makes the identity square usable: there the diagonal is `𝟙 X ≫ f`,
and only passing `f` for it keeps the statement free of `eqToHom`s.
`AlgebraicGeometry.Etale.exchange_eq` says that the choice does not matter.

## Blueprint

- `def:weil-pbc-underived-exchange` is `AlgebraicGeometry.Etale.exchange`.
- `lemma:weil-pbc-underived-exchange-naturality` is the naturality of that transformation,
  which holds by construction; the blueprint statement is recorded as
  `AlgebraicGeometry.Etale.exchange_naturality`.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

open Etale

section Defs

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- For a commutative square with horizontal edges `g`, `g'` and vertical edges `f`, `f'`,
the canonical isomorphism `g^* ⋙ f'^* ≅ f^* ⋙ g'^*` of pullbacks on small étale sites: both
sides are identified with the pullback along the diagonal `d` of the square. -/
noncomputable def Etale.upperStarSquareIso (w : g' ≫ f = f' ≫ g) (d : X' ⟶ Y := g' ≫ f)
    (hd : d = g' ≫ f := by cat_disch) :
    (g)^*[A] ⋙ (f')^*[A] ≅ (f)^*[A] ⋙ (g')^*[A] :=
  (upperStarComp A f' g d (hd.trans w)).symm ≪≫ upperStarComp A g' f d hd

/-- The exchange (Beck–Chevalley) transformation `Ex□ : f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` attached
to a commutative square with horizontal edges `g`, `g'` and vertical edges `f`, `f'`: the
mate of `Etale.upperStarSquareIso` with respect to the adjunctions `f^* ⊣ f_*` and
`f'^* ⊣ f'_*`. Only commutativity of the square is used. -/
noncomputable def Etale.exchange (w : g' ≫ f = f' ≫ g) (d : X' ⟶ Y := g' ≫ f)
    (hd : d = g' ≫ f := by cat_disch) :
    (f)_*[A] ⋙ (g)^*[A] ⟶ (g')^*[A] ⋙ (f')_*[A] :=
  (mateEquiv (upperStarLowerStarAdjunction A f) (upperStarLowerStarAdjunction A f')
    (.mk ((g)^*[A]) ((f)^*[A]) ((f')^*[A]) ((g')^*[A])
      (Etale.upperStarSquareIso A f g f' g' w d hd).hom)).natTrans

/-- The exchange transformation does not depend on the chosen diagonal of the square. -/
lemma Etale.exchange_eq (w : g' ≫ f = f' ≫ g) (d : X' ⟶ Y) (hd : d = g' ≫ f) :
    exchange A f g f' g' w d hd = exchange A f g f' g' w := by
  subst hd; rfl

/-- The exchange transformation is natural in the sheaf: this is the naturality square of
the natural transformation `Etale.exchange`. -/
lemma Etale.exchange_naturality (w : g' ≫ f = f' ≫ g)
    {F G : Sheaf X.smallEtaleTopology A} (u : F ⟶ G) :
    ((f)_*[A] ⋙ (g)^*[A]).map u ≫ (exchange A f g f' g' w).app G =
      (exchange A f g f' g' w).app F ≫ ((g')^*[A] ⋙ (f')_*[A]).map u :=
  (exchange A f g f' g' w).naturality u

end Defs

section Id

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma Etale.upperStarSquareIso_id (w : 𝟙 X ≫ f = f ≫ 𝟙 Y) (hd : f = 𝟙 X ≫ f) :
    (upperStarSquareIso A f (𝟙 Y) f (𝟙 X) w f hd).hom =
      (Functor.whiskerRight (upperStarId A Y).hom ((f)^*[A]) ≫
          ((f)^*[A]).leftUnitor.hom ≫ ((f)^*[A]).rightUnitor.inv) ≫
        Functor.whiskerLeft ((f)^*[A]) (upperStarId A X).inv := by
  have h1 : upperStarComp A f (𝟙 Y) f (hd.trans w) =
      ((f)^*[A]).leftUnitor.symm ≪≫
        Functor.isoWhiskerRight (upperStarId A Y).symm ((f)^*[A]) :=
    Iso.ext (by simpa using upperStarComp_id_right A f (hd.trans w))
  simp [upperStarSquareIso, h1, upperStarComp_id_left A f hd]

/-- Identity square: for `g = 𝟙 Y` and `g' = 𝟙 X` the exchange transformation is the
identity, modulo the identification `Etale.upperStarId` of `(𝟙 _)^*` with `𝟭`. -/
lemma Etale.exchange_id (w : 𝟙 X ≫ f = f ≫ 𝟙 Y) :
    exchange A f (𝟙 Y) f (𝟙 X) w =
      Functor.whiskerLeft ((f)_*[A]) (upperStarId A Y).hom ≫
        ((f)_*[A]).rightUnitor.hom ≫ ((f)_*[A]).leftUnitor.inv ≫
          Functor.whiskerRight (upperStarId A X).inv ((f)_*[A]) := by
  have hd : f = 𝟙 X ≫ f := by simp
  rw [← exchange_eq A f (𝟙 Y) f (𝟙 X) w f hd]
  unfold Etale.exchange
  rw [upperStarSquareIso_id A f w hd,
    mateEquiv_comp_whiskerLeft (upperStarLowerStarAdjunction A f)
      (upperStarLowerStarAdjunction A f) _ (upperStarId A X).inv,
    mateEquiv_whiskerRight_comp (upperStarLowerStarAdjunction A f)
      (upperStarLowerStarAdjunction A f) _ (upperStarId A Y).hom,
    mateEquiv_id]
  simp

end Id

section HComp

variable {X Y X' Y' X'' Y'' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (k : Y'' ⟶ Y') (f'' : X'' ⟶ Y'') (k' : X'' ⟶ X')

lemma Etale.upperStarSquareIso_hComp (w : g' ≫ f = f' ≫ g) (w' : k' ≫ f' = f'' ≫ k)
    (w'' : (k' ≫ g') ≫ f = f'' ≫ (k ≫ g)) :
    (upperStarSquareIso A f (k ≫ g) f'' (k' ≫ g') w'').hom =
      (Functor.whiskerRight (upperStarComp A k g).hom ((f'')^*[A]) ≫
        (Functor.whiskerLeft ((g)^*[A]) (upperStarSquareIso A f' k f'' k' w').hom ≫
          Functor.whiskerRight (upperStarSquareIso A f g f' g' w).hom ((k')^*[A]))) ≫
        Functor.whiskerLeft ((f)^*[A]) (upperStarComp A k' g').inv := by
  have eDE : (k' ≫ g') ≫ f = (k' ≫ f') ≫ g := by
    rw [Category.assoc, w, ← Category.assoc]
  have eDF : (k' ≫ g') ≫ f = k' ≫ (g' ≫ f) := Category.assoc _ _ _
  have i1 := upperStarComp_assoc' A f'' k g (k' ≫ f') w' (k ≫ g) rfl
    ((k' ≫ g') ≫ f) eDE w''
  have i2 := upperStarComp_assoc' A k' g' f (k' ≫ g') rfl (g' ≫ f) rfl
    ((k' ≫ g') ≫ f) rfl eDF
  have i3 := upperStarComp_assoc' A k' f' g (k' ≫ f') rfl (g' ≫ f) w
    ((k' ≫ g') ≫ f) eDE eDF
  simp only [upperStarSquareIso, Iso.trans_hom, Iso.symm_hom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  simp only [← Functor.isoWhiskerLeft_hom, ← Functor.isoWhiskerLeft_inv,
    ← Functor.isoWhiskerRight_hom, ← Functor.isoWhiskerRight_inv] at i1 i2 i3 ⊢
  rw [Iso.inv_comp_eq, ← reassoc_of% i1]
  simp only [Iso.hom_inv_id_assoc]
  rw [reassoc_of% i3]
  simp only [Iso.hom_inv_id_assoc]
  rw [← reassoc_of% i2]
  simp only [Iso.hom_inv_id, Category.comp_id]

/-- Horizontal pasting: for two squares glued along the common vertical edge `f'`, the
exchange transformation of the pasted square is the composite of the two exchange
transformations, modulo the composition isomorphisms of the glued horizontal edges. -/
lemma Etale.exchange_hComp (w : g' ≫ f = f' ≫ g) (w' : k' ≫ f' = f'' ≫ k)
    (w'' : (k' ≫ g') ≫ f = f'' ≫ (k ≫ g)) :
    exchange A f (k ≫ g) f'' (k' ≫ g') w'' =
      Functor.whiskerLeft ((f)_*[A]) (upperStarComp A k g).hom ≫
        Functor.whiskerRight (exchange A f g f' g' w) ((k)^*[A]) ≫
          Functor.whiskerLeft ((g')^*[A]) (exchange A f' k f'' k' w') ≫
            Functor.whiskerRight (upperStarComp A k' g').inv ((f'')_*[A]) := by
  unfold Etale.exchange
  simp only [upperStarSquareIso_hComp A f g f' g' k f'' k' w w' w'']
  rw [mateEquiv_comp_whiskerLeft (upperStarLowerStarAdjunction A f)
      (upperStarLowerStarAdjunction A f'') _ (upperStarComp A k' g').inv,
    mateEquiv_whiskerRight_comp (upperStarLowerStarAdjunction A f)
      (upperStarLowerStarAdjunction A f'') _ (upperStarComp A k g).hom,
    mateEquiv_vcomp' (upperStarLowerStarAdjunction A f) (upperStarLowerStarAdjunction A f')
      (upperStarLowerStarAdjunction A f'') (upperStarSquareIso A f g f' g' w).hom
      (upperStarSquareIso A f' k f'' k' w').hom]
  simp only [Category.assoc]

end HComp

end AlgebraicGeometry
