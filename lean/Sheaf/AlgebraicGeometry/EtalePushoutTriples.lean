module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Compatible etale schemes over a span

Source: Stacks Project, More on Morphisms, Tag 07RV,
`lemma-equivalence-categories-schemes-over-pushout`
(blueprint: def-sfb-etale-pushout-triples).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Etale triples over `S ← T → T'`: two etale schemes and an isomorphism of
etale schemes over `T` between their pullbacks. Morphisms are pairs making the
comparison square commute. An invertible arrow is equivalent to a specified iso;
its inverse is unique. The category is the full subcategory of the comma category
where the comparison arrow is invertible.

Source: Stacks Project, Tag 07RV (blueprint: def-sfb-etale-pushout-triples). -/
abbrev EtalePushoutTriples {T S T' : Scheme.{u}} (a : T ⟶ S) (i : T ⟶ T') :=
  ObjectProperty.FullSubcategory
    (fun D : Comma (MorphismProperty.Over.pullback @Etale ⊤ a)
      (MorphismProperty.Over.pullback @Etale ⊤ i) => IsIso D.hom)

/-- Canonical comparison between iterated pullbacks around a commuting square,
using the composition comparisons for base change. It identifies both restrictions
with pullback along the same composite map from `T`.

Source: Stacks Project, Tag 07RV (blueprint: def-sfb-etale-pushout-triples). -/
noncomputable def etalePushoutComparison
    {T S T' P : Scheme.{u}} (a : T ⟶ S) (i : T ⟶ T')
    (j : S ⟶ P) (b : T' ⟶ P) (h : a ≫ j = i ≫ b) :
    MorphismProperty.Over.pullback @Etale ⊤ j ⋙
        MorphismProperty.Over.pullback @Etale ⊤ a ≅
      MorphismProperty.Over.pullback @Etale ⊤ b ⋙
        MorphismProperty.Over.pullback @Etale ⊤ i :=
  (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) a j).symm ≪≫
    MorphismProperty.Over.pullbackCongr (P := @Etale) (Q := ⊤) h ≪≫
    MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) i b

/-- Pullback from etale schemes over `P` to compatible etale triples. The comparison
is the canonical iterated-base-change isomorphism; morphisms are pulled back on both sides.

Source: Stacks Project, Tag 07RV (blueprint: def-sfb-etale-pushout-triples). -/
noncomputable def etalePushoutRestriction
    {T S T' P : Scheme.{u}} (a : T ⟶ S) (i : T ⟶ T')
    (j : S ⟶ P) (b : T' ⟶ P) (h : a ≫ j = i ≫ b) :
    P.Etale ⥤ EtalePushoutTriples a i where
  obj W :=
    { obj :=
        { left := (MorphismProperty.Over.pullback @Etale ⊤ j).obj W
          right := (MorphismProperty.Over.pullback @Etale ⊤ b).obj W
          hom := (etalePushoutComparison a i j b h).hom.app W }
      property := by dsimp; infer_instance }
  map f := ObjectProperty.homMk
    { left := (MorphismProperty.Over.pullback @Etale ⊤ j).map f
      right := (MorphismProperty.Over.pullback @Etale ⊤ b).map f
      w := (etalePushoutComparison a i j b h).hom.naturality f }
  map_id W := by ext <;> simp
  map_comp f g := by ext <;> simp

end AlgebraicGeometry
