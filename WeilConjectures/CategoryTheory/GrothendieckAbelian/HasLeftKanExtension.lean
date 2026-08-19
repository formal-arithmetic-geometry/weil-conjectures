/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!

# Left Kan extensions for presheaves on the small sites (sorried)

Left Kan extensions along the opposites of base change and of the localization functors
exist for `A`-valued presheaves on the small sites of `P`-schemes, for a Grothendieck
abelian category `A` with `Hom`-types in the universe `u` of the base schemes: the sites
are essentially small and `A` is cocomplete.

Moreover the left Kan extension along the opposite of base change is left exact: the
indexing comma categories of the pointwise left Kan extensions are cofiltered — base
change preserves the finite limits of the étale slice — so the Kan extension is computed
by filtered colimits, which are exact in `A` by AB5.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Left Kan extensions along the opposite of base change by an *arbitrary* morphism
`g : W ⟶ U` exist for `A`-valued presheaves on the small sites of `P`-schemes: the sites
are essentially small for the étale-like properties `P` of interest and the Grothendieck
abelian category `A` is cocomplete. -/
instance hasLeftKanExtension_op_overPullback (A : Type u') [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A] (P : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    {W U : Scheme.{u}} (g : W ⟶ U) (F : (P.Over ⊤ U)ᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback P ⊤ g).op.HasLeftKanExtension F :=
  sorry

/-- Left Kan extensions along the opposite of the localization functor of `h : P f` exist
for `A`-valued presheaves on the small sites of `P`-schemes: the sites are essentially
small for the étale-like properties `P` of interest and the Grothendieck abelian category
`A` is cocomplete. -/
instance hasLeftKanExtension_op_overMap (A : Type u') [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A] (P : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    {V U : Scheme.{u}} {f : V ⟶ U} (h : P f) (F : (P.Over ⊤ V)ᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasLeftKanExtension F :=
  sorry

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry

/-- The left Kan extension along the opposite of base change by an *arbitrary* morphism
`g : Z ⟶ Y` is left exact for a Grothendieck abelian coefficient category: the indexing
comma categories of the pointwise left Kan extensions are cofiltered (base change
preserves the finite limits of the étale slice), so the Kan extension is computed by
filtered colimits, which are exact in `A` by AB5. -/
instance Etale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian
    (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    PreservesFiniteLimits ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan :
      (Y.Etaleᵒᵖ ⥤ A) ⥤ Z.Etaleᵒᵖ ⥤ A) :=
  sorry

end AlgebraicGeometry
