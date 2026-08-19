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

# Left Kan extensions for presheaves on the small sites (partly sorried)

Left Kan extensions along the opposites of base change and of the localization functors
exist for `A`-valued presheaves on the small sites of `P`-schemes, for a Grothendieck
abelian category `A` with `Hom`-types in the universe `u` of the base schemes.

For the localization functor of `h : P f` with `f` a *monomorphism* this is proved here:
the indexing comma category of the pointwise left Kan extension at `W : P.Over ⊤ U` is
governed by the type `CategoryTheory.GrothendieckTopology.LiftIndex` of factorizations of
the structure morphism of `W` through `f`. For a monomorphism `f` a lift induces a
terminal object of the comma category, and if no lift exists the comma category is empty;
hence all pointwise left Kan extensions with values in a category with an initial object
exist. This generalizes the étale-specific argument of
`WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Etale` to an arbitrary morphism
property `P` satisfying `[P.HasOfPostcompProperty P]`, which supplies the cancellation
`P (α ≫ f) → P f → P α`. All uses of the localization lower shriek in the `SixFunctors`
folder are along open immersions, which are monomorphisms.

The remaining sorried instances concern base change along an *arbitrary* morphism
`g : W ⟶ U`: there the indexing comma categories are cofiltered but only essentially
small — essential smallness of the small sites is not yet available in Mathlib (only the
small *affine* sites are known to be essentially small) — so the existence of the
pointwise left Kan extensions and their left exactness (by AB5, filtered colimits being
exact in `A`) remain sorried. For an étale `g` both are proved in
`WeilConjectures.SixFunctors.UpperLowerStar.Etale` via the adjunction
`MorphismProperty.Over.mapPullbackAdj`, without any smallness assumption.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

section LiftIndex

variable {P : MorphismProperty Scheme.{u}} [P.IsMultiplicative] [P.HasOfPostcompProperty P]
  {V U : Scheme.{u}}

/-- The type of lifts of `W : P.Over ⊤ U` through `f : V ⟶ U`: factorizations of the
structure morphism of `W` through `f`. It indexes the colimit computing the presheaf-level
left Kan extension along the localization functor of `h : P f` at `W`. -/
private def LiftIndex (f : V ⟶ U) (W : P.Over ⊤ U) : Type u :=
  {α : W.left ⟶ V // α ≫ f = W.hom}

namespace LiftIndex

variable {f : V ⟶ U} {W : P.Over ⊤ U}

omit [P.IsMultiplicative] in
/-- The lift of a `P`-scheme over `U` through `f` with `P f` satisfies `P`, by the
cancellation property `P.HasOfPostcompProperty P`. -/
private lemma prop_val (h : P f) (α : LiftIndex f W) : P α.1 :=
  MorphismProperty.of_postcomp (W := P) (W' := P) _ f h (by rw [α.2]; exact W.prop)

/-- The `P`-scheme over `V` determined by a lift of `W : P.Over ⊤ U` through `f`. -/
private def toOver (h : P f) (α : LiftIndex f W) : P.Over ⊤ V :=
  MorphismProperty.Over.mk ⊤ α.1 (α.prop_val h)

/-- The comparison morphism from `W` to the image of `α.toOver` in `P.Over ⊤ U`; its
underlying morphism is the identity. -/
private def homToComp (h : P f) (α : LiftIndex f W) :
    W ⟶ (MorphismProperty.Over.map ⊤ h).obj (α.toOver h) :=
  MorphismProperty.Over.homMk (𝟙 W.left) ((Category.id_comp _).trans α.2)

/-- The object of the comma category indexing the pointwise left Kan extension at `W`
associated with a lift `α`; for a monomorphism `f` it is terminal, see
`LiftIndex.isTerminalCostructuredArrow`. -/
private def costructuredArrow (h : P f) (α : LiftIndex f W) :
    CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W) :=
  CostructuredArrow.mk (α.homToComp h).op

/-- The lift of `W` extracted from an object of the indexing comma category. -/
private def ofCostructuredArrow (h : P f) (W : P.Over ⊤ U)
    (s : CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W)) :
    LiftIndex f W :=
  ⟨s.hom.unop.left ≫ s.left.unop.hom, by
    have hw : s.hom.unop.left ≫
        ((MorphismProperty.Over.map ⊤ h).obj s.left.unop).hom = W.hom :=
      MorphismProperty.Over.w s.hom.unop
    rw [Category.assoc]
    exact hw⟩

omit [P.HasOfPostcompProperty P] in
/-- If `W` has no lift through `f`, the indexing comma category is empty. -/
private lemma isEmpty_costructuredArrow (h : P f) (W : P.Over ⊤ U)
    (hempty : IsEmpty (LiftIndex f W)) :
    IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W)) :=
  ⟨fun s => hempty.elim (ofCostructuredArrow h W s)⟩

/-- For a monomorphism `f`, the comma object associated with a lift `α` of `W` is
terminal: the pointwise left Kan extension formula collapses to a single value. -/
private noncomputable def isTerminalCostructuredArrow (h : P f) [Mono f]
    (α : LiftIndex f W) :
    IsTerminal (α.costructuredArrow h) :=
  IsTerminal.ofUniqueHom
    (fun s =>
      CostructuredArrow.homMk
        (Quiver.Hom.op
          (MorphismProperty.Over.homMk s.hom.unop.left
            (by
              have hs : s.hom.unop.left ≫ s.left.unop.hom ≫ f = W.hom :=
                MorphismProperty.Over.w s.hom.unop
              exact (cancel_mono f).mp
                (((Category.assoc _ _ _).trans hs).trans α.2.symm)) :
            α.toOver h ⟶ s.left.unop))
        (by
          apply Quiver.Hom.unop_inj
          apply MorphismProperty.Over.Hom.ext
          exact Category.id_comp _))
    (fun s m => by
      ext
      apply Quiver.Hom.unop_inj
      apply MorphismProperty.Over.Hom.ext
      have hw := m.w
      apply_fun (fun z => z.unop.left) at hw
      exact (Category.id_comp _).symm.trans hw)

end LiftIndex

end LiftIndex

/-- Left Kan extensions along the opposite of base change by an *arbitrary* morphism
`g : W ⟶ U` exist for `A`-valued presheaves on the small sites of `P`-schemes: the sites
are essentially small for the étale-like properties `P` of interest and the Grothendieck
abelian category `A` is cocomplete. For an étale `g` this is proved in
`WeilConjectures.SixFunctors.UpperLowerStar.Etale` via the adjunction with the
localization functor. -/
instance hasLeftKanExtension_op_overPullback (A : Type u') [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A] (P : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    {W U : Scheme.{u}} (g : W ⟶ U) (F : (P.Over ⊤ U)ᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback P ⊤ g).op.HasLeftKanExtension F :=
  sorry

/-- Along the localization functor of `h : P f` with `f` a monomorphism, all pointwise
left Kan extensions with values in a category with an initial object exist: the indexing
comma categories are either empty or admit a terminal object. -/
instance hasPointwiseLeftKanExtension_op_overMap (A : Type u') [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A] (P : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    {V U : Scheme.{u}} {f : V ⟶ U} (h : P f) [Mono f] (F : (P.Over ⊤ V)ᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasPointwiseLeftKanExtension F := by
  intro W
  by_cases hn : Nonempty (LiftIndex f W.unop)
  · obtain ⟨α⟩ := hn
    have : HasTerminal (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op W) :=
      (α.isTerminalCostructuredArrow h).hasTerminal
    infer_instance
  · have : IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op W) :=
      LiftIndex.isEmpty_costructuredArrow h W.unop (not_nonempty_iff.mp hn)
    have : HasColimitsOfShape
        (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op W) A :=
      hasColimitsOfShape_of_equivalence (equivalenceOfIsEmpty (Discrete PEmpty.{1}) _)
    infer_instance

/-- Left Kan extensions along the opposite of the localization functor of `h : P f` with
`f` a monomorphism exist for `A`-valued presheaves on the small sites of `P`-schemes: the
indexing comma categories are either empty or admit a terminal object, see
`hasPointwiseLeftKanExtension_op_overMap`. -/
instance hasLeftKanExtension_op_overMap (A : Type u') [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A] (P : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    {V U : Scheme.{u}} {f : V ⟶ U} (h : P f) [Mono f] (F : (P.Over ⊤ V)ᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasLeftKanExtension F :=
  inferInstance

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry

/-- The left Kan extension along the opposite of base change by an *arbitrary* morphism
`g : Z ⟶ Y` is left exact for a Grothendieck abelian coefficient category: the indexing
comma categories of the pointwise left Kan extensions are cofiltered (base change
preserves the finite limits of the étale slice), so the Kan extension is computed by
filtered colimits, which are exact in `A` by AB5. For an étale `g` this is proved in
`WeilConjectures.SixFunctors.UpperLowerStar.Etale` via the adjunction with the
localization functor. -/
instance Etale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian
    (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    PreservesFiniteLimits ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan :
      (Y.Etaleᵒᵖ ⥤ A) ⥤ Z.Etaleᵒᵖ ⥤ A) :=
  sorry

end AlgebraicGeometry
