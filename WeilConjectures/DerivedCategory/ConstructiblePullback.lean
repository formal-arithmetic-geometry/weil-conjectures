/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!

# The derived pullback preserves bounded constructible complexes

For a morphism of schemes `g : Z ⟶ Y`, the pullback `g^*` on étale sheaves is exact, so
it induces a functor `(Etale.upperStar A g).mapDerivedCategory` between the derived
categories of étale sheaves. This file records two statements about this derived
pullback, both stated with `sorry`:

- `Etale.DerivedCategory.bounded_upperStar_mapDerivedCategory`: it preserves
  boundedness for the canonical t-structures, since the pullback on sheaves is exact
  and hence the derived pullback is t-exact;
- `Etale.DerivedCategory.constructibleHomology_upperStar_mapDerivedCategory`: it
  preserves constructibility of the homology sheaves, since the homology of the
  derived pullback is the pullback of the homology and the pullback of a constructible
  étale sheaf along a morphism of schemes is constructible.

Together (`Etale.DerivedCategory.boundedConstructible_upperStar_mapDerivedCategory`)
they show that the derived pullback sends `Dᵇc(Y, A)` into `Dᵇc(Z, A)`. This is the
geometric input needed to restrict the Frobenius pullback endofunctor to the bounded
constructible subcategory in `WeilConjectures.WeilSheaf.Defs`.

-/

@[expose] public section

universe w u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]
  [∀ (T : Scheme.{u}) (U : T.Etale), HasWeakSheafify (T.smallEtaleTopology.over U) A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  [∀ (T : Scheme.{u}) (φ : T ⟶ Y) (P : Y.Etaleᵒᵖ ⥤ A),
    (MorphismProperty.Over.pullback @Etale ⊤ φ).op.HasLeftKanExtension P]
  [∀ (T : Scheme.{u}) (φ : T ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ A),
    (MorphismProperty.Over.pullback @Etale ⊤ φ).op.HasLeftKanExtension P]
  [HasDerivedCategory.{w} (Sheaf Y.smallEtaleTopology A)]
  [HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology A)]

/-- The derived pullback along `g : Z ⟶ Y` preserves boundedness for the canonical
t-structures: the pullback on sheaves is exact, so the derived pullback is t-exact. -/
theorem Etale.DerivedCategory.bounded_upperStar_mapDerivedCategory
    {M : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hM : DerivedCategory.TStructure.t.bounded M) :
    DerivedCategory.TStructure.t.bounded
      ((Etale.upperStar A g).mapDerivedCategory.obj M) :=
  sorry

/-- The derived pullback along `g : Z ⟶ Y` preserves constructibility of the homology
sheaves: the homology of the derived pullback is the pullback of the homology, and the
pullback of a constructible étale sheaf is constructible. -/
theorem Etale.DerivedCategory.constructibleHomology_upperStar_mapDerivedCategory
    {M : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hM : Etale.DerivedCategory.constructibleHomology A Y M) :
    Etale.DerivedCategory.constructibleHomology A Z
      ((Etale.upperStar A g).mapDerivedCategory.obj M) :=
  sorry

/-- The derived pullback along `g : Z ⟶ Y` preserves bounded constructible objects,
combining `Etale.DerivedCategory.bounded_upperStar_mapDerivedCategory` and
`Etale.DerivedCategory.constructibleHomology_upperStar_mapDerivedCategory`. -/
theorem Etale.DerivedCategory.boundedConstructible_upperStar_mapDerivedCategory
    {M : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hM : Etale.DerivedCategory.boundedConstructible A Y M) :
    Etale.DerivedCategory.boundedConstructible A Z
      ((Etale.upperStar A g).mapDerivedCategory.obj M) :=
  ⟨Etale.DerivedCategory.bounded_upperStar_mapDerivedCategory A g hM.1,
    Etale.DerivedCategory.constructibleHomology_upperStar_mapDerivedCategory A g hM.2⟩

end AlgebraicGeometry

end
