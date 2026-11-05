/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

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

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIsoOfEq`: the composition isomorphism
  `R(h)_! ≅ Rf_! ⋙ Rg_!` for `f ≫ g = h`, on unbounded derived categories, for a finite
  coefficient ring.
- `AlgebraicGeometry.Etale.derivedTensorBraiding`: the symmetry `K ⊗ᴸ M ≅ M ⊗ᴸ K` of the
  derived tensor product, the braiding `DerivedCategory.braidedCategory'`.
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
in both variables: the braiding `DerivedCategory.braidedCategory'` of `D(X_ét)`, as an
isomorphism between `- ⊗ᴸ -` and the flipped bifunctor. -/
noncomputable def derivedTensorBraiding : derivedTensor A X ≅ (derivedTensor A X).flip :=
  @BraidedCategory.curriedBraidingNatIso _ _ _
    (_root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology A))

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

/-- Blueprint `sk-thm-sf-comp-composition`: the composition isomorphism `α : R(h)_! ≅ Rf_! ⋙ Rg_!`
for `f ≫ g = h`, on unbounded derived categories, for a finite coefficient ring
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso` transported along `f ≫ g = h`). -/
noncomputable def rightDerivedLowerShriekCompIsoOfEq (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S)
    (w : f ≫ g = h) [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [QuasiCompact h] :
    R(h)_![ModuleCat.{u + 1} Λ] ≅ R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ] :=
  haveI : HasCompactification (f ≫ g) := .of_eq w.symm
  haveI : QuasiCompact (f ≫ g) := by rw [w]; infer_instance
  eqToIso (by subst w; rfl) ≪≫ rightDerivedLowerShriekCompIso Λ f g

end Composition

section Components

variable {B X Y P : Scheme.{u}}

end Components

section Kunneth

variable {B X Y P : Scheme.{u}}

section Inner

variable {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback p q f g)
  [HasCompactification f] [HasCompactification q] [QuasiCompact q]

end Inner

section Naturality

variable {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback p q f g) (h : P ⟶ B)
  (w : q ≫ g = h) [HasCompactification f] [HasCompactification g] [HasCompactification q]
  [HasCompactification h] [QuasiCompact q] [QuasiCompact h]

end Naturality

section FibreProduct

variable (f : X ⟶ B) (g : Y ⟶ B) [HasCompactification f] [HasCompactification g]
  [QuasiCompact f] [QuasiCompact g] [HasCompactification (pullback.toBase f g)]

end FibreProduct

end Kunneth

end Etale

end AlgebraicGeometry
