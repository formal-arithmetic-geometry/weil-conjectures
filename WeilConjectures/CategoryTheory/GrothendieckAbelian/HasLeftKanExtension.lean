/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!

# Left Kan extensions for presheaves on the small sites (base change sorried)

Left Kan extensions along the opposites of base change and of the localization functors
exist for `A`-valued presheaves on the small étale and the small pro-étale sites, for a
Grothendieck abelian category `A` with `Hom`-types in the universe `u + 1`, one above the
universe `u` of the base schemes.

The instances for the localization functors are proved from the scheme-side combinatorics
below, namely the type `AlgebraicGeometry.SmallSite.LiftIndex` of factorizations of the
structure morphism of `W : P.Over ⊤ U` through `f`, which governs the indexing comma
category of the pointwise left Kan extension along the localization functor of `h : P f`,
and the dichotomy `SmallSite.mem_essImage_or_isEmpty_costructuredArrow_op_overMap`: for a
monomorphism `f`, every `W` either lies in the essential image of the localization functor
(a lift induces a terminal object of the comma category) or has empty indexing comma
category. That dichotomy is what makes the pointwise left Kan extensions exist over a
category with an initial object (`SmallSite.hasPointwiseLeftKanExtension_op_overMap`) and
makes the presheaf-level left Kan extension left exact
(`SmallSite.preservesFiniteLimits_op_lan_overMap`), being pointwise either an evaluation or
a zero object. The cancellation `P (α ≫ f) → P f → P α` it uses is
`MorphismProperty.HasOfPostcompProperty P P`, available both for `P = @Etale` and for
`P = @WeaklyEtale`. All uses of the localization lower shriek in the `SixFunctors` folder
are along open immersions, which are monomorphisms.

Base change along an *arbitrary* morphism `g : Z ⟶ Y` has no monomorphism to exploit, so
neither the existence of the left Kan extensions nor their left exactness comes from the
combinatorics above. Both are sorried here, for both sites:

- existence holds because the small étale and small pro-étale sites are essentially small
  in `u + 1` and `A` is cocomplete for `u + 1`-small diagrams, so the pointwise colimit
  formula applies over the (again essentially small) indexing comma categories;
- left exactness holds because base change preserves the finite limits of the slice, so
  the indexing comma categories are cofiltered and the Kan extension is a filtered colimit,
  which is exact in `A` by AB5.

For an étale `g` both are proved in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and for a weakly étale `g` in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`, via the adjunction
`MorphismProperty.Over.mapPullbackAdj`, without any smallness assumption.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.SmallSite

section LiftIndex

variable {P : MorphismProperty Scheme.{u}} {V U : Scheme.{u}}

/-- The type of lifts of `W : P.Over ⊤ U` through `f : V ⟶ U`: factorizations of the
structure morphism of `W` through `f`. It indexes the colimit computing the presheaf-level
left Kan extension along the localization functor of `h : P f`. -/
private def LiftIndex (f : V ⟶ U) (W : P.Over ⊤ U) : Type u :=
  {α : W.left ⟶ V // α ≫ f = W.hom}

namespace LiftIndex

variable [P.IsMultiplicative] [P.HasOfPostcompProperty P] {f : V ⟶ U} {W : P.Over ⊤ U}

omit [P.IsMultiplicative] in
/-- The lift of a `P`-scheme over `U` through `f` with `P f` satisfies `P`, by the
cancellation property `MorphismProperty.HasOfPostcompProperty P P`. -/
private lemma prop_val (h : P f) (α : LiftIndex f W) : P α.1 :=
  MorphismProperty.of_postcomp (W := P) (W' := P) α.1 f h (by rw [α.2]; exact W.prop)

/-- The `P`-scheme over `V` determined by a lift of `W : P.Over ⊤ U` through `f`. -/
private def toOver (h : P f) (α : LiftIndex f W) : P.Over ⊤ V :=
  MorphismProperty.Over.mk ⊤ α.1 (α.prop_val h)

/-- The comparison morphism from `W` to the image of `α.toOver` in `P.Over ⊤ U`; its
underlying morphism is the identity. -/
private def homToComp (h : P f) (α : LiftIndex f W) :
    W ⟶ (MorphismProperty.Over.map ⊤ h).obj (α.toOver h) :=
  MorphismProperty.Over.homMk (𝟙 W.left) ((Category.id_comp _).trans α.2)

/-- A lift of `W` through `f` identifies `W` with the image of a `P`-scheme over `V`
under the localization functor: the comparison morphism `LiftIndex.homToComp` is the
identity on underlying schemes. -/
private def isoComp (h : P f) (α : LiftIndex f W) :
    W ≅ (MorphismProperty.Over.map ⊤ h).obj (α.toOver h) where
  hom := α.homToComp h
  inv := MorphismProperty.Over.homMk (𝟙 W.left) ((Category.id_comp _).trans α.2.symm)
  hom_inv_id := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp _
  inv_hom_id := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp _

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

section OverMap

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {P : MorphismProperty Scheme.{u}} [P.IsMultiplicative] [P.HasOfPostcompProperty P]
  {V U : Scheme.{u}} {f : V ⟶ U}

/-- Along the localization functor of `h : P f` with `f` a monomorphism, all pointwise
left Kan extensions with values in a category with an initial object exist: the indexing
comma categories are either empty or admit a terminal object. -/
instance hasPointwiseLeftKanExtension_op_overMap (h : P f) [Mono f]
    (F : (P.Over ⊤ V)ᵒᵖ ⥤ A) :
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

/-- Every `P`-scheme over `U` either lies in the essential image of the localization
functor of `h : P f`, or has empty indexing comma category: a lift of `W` through `f`
identifies `W` with the image of a `P`-scheme over `V`, and if no lift exists the comma
category is empty. This is the dichotomy underlying the left exactness of the
presheaf-level lower shriek. -/
lemma mem_essImage_or_isEmpty_costructuredArrow_op_overMap (h : P f) (W : (P.Over ⊤ U)ᵒᵖ) :
    (MorphismProperty.Over.map ⊤ h).op.essImage W ∨
      IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op W) := by
  by_cases hn : Nonempty (LiftIndex f W.unop)
  · obtain ⟨α⟩ := hn
    exact Or.inl ⟨op (α.toOver h), ⟨(α.isoComp h).op⟩⟩
  · exact Or.inr (LiftIndex.isEmpty_costructuredArrow h W.unop (not_nonempty_iff.mp hn))

/-- The presheaf-level left Kan extension along the opposite of the localization functor
of `h : P f` with `f` a monomorphism is left exact: by the dichotomy
`mem_essImage_or_isEmpty_costructuredArrow_op_overMap` it is pointwise either an evaluation
or a zero object. -/
lemma preservesFiniteLimits_op_lan_overMap (h : P f) [Mono f] :
    PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ h).op.lan :
      ((P.Over ⊤ V)ᵒᵖ ⥤ A) ⥤ (P.Over ⊤ U)ᵒᵖ ⥤ A) :=
  Functor.preservesFiniteLimits_lan_of_essImage_or_isEmpty _
    (mem_essImage_or_isEmpty_costructuredArrow_op_overMap h)

end OverMap

end AlgebraicGeometry.SmallSite

/-! ### The small étale site -/

namespace AlgebraicGeometry.Etale

/-- Left Kan extensions along the opposite of base change by an *arbitrary* morphism
`g : Z ⟶ Y` exist for `A`-valued presheaves on the small étale sites: the sites are
essentially small and the Grothendieck abelian category `A` is cocomplete. For an étale `g`
this is proved in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` via the
adjunction with the localization functor. -/
instance hasLeftKanExtension_op_overPullback (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {Z Y : Scheme.{u}} (g : Z ⟶ Y) (F : Y.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasLeftKanExtension F :=
  sorry

/-- Along the localization functor of `h : Etale f` with `f` a monomorphism, all pointwise
left Kan extensions with values in a category with an initial object exist: the indexing
comma categories are either empty or admit a terminal object. -/
instance hasPointwiseLeftKanExtension_op_overMap (A : Type u') [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {V U : Scheme.{u}} {f : V ⟶ U}
    (h : Etale f) [Mono f] (F : V.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasPointwiseLeftKanExtension F :=
  SmallSite.hasPointwiseLeftKanExtension_op_overMap A h F

/-- Left Kan extensions along the opposite of the localization functor of `h : Etale f`
with `f` a monomorphism exist for `A`-valued presheaves on the small étale sites: the
indexing comma categories are either empty or admit a terminal object, see
`hasPointwiseLeftKanExtension_op_overMap`. -/
instance hasLeftKanExtension_op_overMap (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {V U : Scheme.{u}} {f : V ⟶ U} (h : Etale f) [Mono f]
    (F : V.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasLeftKanExtension F :=
  inferInstance

/-- Every étale scheme over `U` either lies in the essential image of the localization
functor of `h : Etale f`, or has empty indexing comma category. -/
lemma mem_essImage_or_isEmpty_costructuredArrow_op_overMap {V U : Scheme.{u}} {f : V ⟶ U}
    (h : Etale f) (W : U.Etaleᵒᵖ) :
    (MorphismProperty.Over.map ⊤ h).op.essImage W ∨
      IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op W) :=
  SmallSite.mem_essImage_or_isEmpty_costructuredArrow_op_overMap h W

/-- The presheaf-level left Kan extension along the opposite of the localization functor
of `h : Etale f` with `f` a monomorphism is left exact: by the dichotomy
`mem_essImage_or_isEmpty_costructuredArrow_op_overMap` it is pointwise either an evaluation
or a zero object. -/
instance preservesFiniteLimits_op_lan_overMap (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {V U : Scheme.{u}} {f : V ⟶ U} (h : Etale f) [Mono f] :
    PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ h).op.lan :
      (V.Etaleᵒᵖ ⥤ A) ⥤ U.Etaleᵒᵖ ⥤ A) :=
  SmallSite.preservesFiniteLimits_op_lan_overMap A h

/-- The left Kan extension along the opposite of base change by an *arbitrary* morphism
`g : Z ⟶ Y` is left exact for a Grothendieck abelian coefficient category: the indexing
comma categories of the pointwise left Kan extensions are cofiltered (base change
preserves the finite limits of the étale slice), so the Kan extension is computed by
filtered colimits, which are exact in `A` by AB5. For an étale `g` this is proved in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` via the adjunction with the
localization functor. -/
instance preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    PreservesFiniteLimits ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan :
      (Y.Etaleᵒᵖ ⥤ A) ⥤ Z.Etaleᵒᵖ ⥤ A) :=
  sorry

end AlgebraicGeometry.Etale

/-! ### The small pro-étale site -/

namespace AlgebraicGeometry.ProEtale

/-- Left Kan extensions along the opposite of base change by an *arbitrary* morphism
`g : Z ⟶ Y` exist for `A`-valued presheaves on the small pro-étale sites: the sites are
essentially small and the Grothendieck abelian category `A` is cocomplete. For a weakly
étale `g` this is proved in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs` via
the adjunction with the localization functor. -/
instance hasLeftKanExtension_op_overPullback (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {Z Y : Scheme.{u}} (g : Z ⟶ Y) (F : Y.ProEtᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.HasLeftKanExtension F :=
  sorry

/-- Along the localization functor of `h : WeaklyEtale f` with `f` a monomorphism, all
pointwise left Kan extensions with values in a category with an initial object exist: the
indexing comma categories are either empty or admit a terminal object. -/
instance hasPointwiseLeftKanExtension_op_overMap (A : Type u') [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {V U : Scheme.{u}} {f : V ⟶ U}
    (h : WeaklyEtale f) [Mono f] (F : V.ProEtᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasPointwiseLeftKanExtension F :=
  SmallSite.hasPointwiseLeftKanExtension_op_overMap A h F

/-- Left Kan extensions along the opposite of the localization functor of
`h : WeaklyEtale f` with `f` a monomorphism exist for `A`-valued presheaves on the small
pro-étale sites, see `hasPointwiseLeftKanExtension_op_overMap`. -/
instance hasLeftKanExtension_op_overMap (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {V U : Scheme.{u}} {f : V ⟶ U} (h : WeaklyEtale f)
    [Mono f] (F : V.ProEtᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasLeftKanExtension F :=
  inferInstance

/-- Every weakly étale scheme over `U` either lies in the essential image of the
localization functor of `h : WeaklyEtale f`, or has empty indexing comma category. -/
lemma mem_essImage_or_isEmpty_costructuredArrow_op_overMap {V U : Scheme.{u}} {f : V ⟶ U}
    (h : WeaklyEtale f) (W : U.ProEtᵒᵖ) :
    (MorphismProperty.Over.map ⊤ h).op.essImage W ∨
      IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op W) :=
  SmallSite.mem_essImage_or_isEmpty_costructuredArrow_op_overMap h W

/-- The presheaf-level left Kan extension along the opposite of the localization functor
of `h : WeaklyEtale f` with `f` a monomorphism is left exact: by the dichotomy
`mem_essImage_or_isEmpty_costructuredArrow_op_overMap` it is pointwise either an evaluation
or a zero object. -/
instance preservesFiniteLimits_op_lan_overMap (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {V U : Scheme.{u}} {f : V ⟶ U} (h : WeaklyEtale f)
    [Mono f] :
    PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ h).op.lan :
      (V.ProEtᵒᵖ ⥤ A) ⥤ U.ProEtᵒᵖ ⥤ A) :=
  SmallSite.preservesFiniteLimits_op_lan_overMap A h

/-- The left Kan extension along the opposite of base change by an *arbitrary* morphism
`g : Z ⟶ Y` is left exact for a Grothendieck abelian coefficient category: the indexing
comma categories of the pointwise left Kan extensions are cofiltered (base change
preserves the finite limits of the pro-étale slice), so the Kan extension is computed by
filtered colimits, which are exact in `A` by AB5. For a weakly étale `g` this is proved in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs` via the adjunction
with the localization functor. -/
instance preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    PreservesFiniteLimits ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan :
      (Y.ProEtᵒᵖ ⥤ A) ⥤ Z.ProEtᵒᵖ ⥤ A) :=
  sorry

end AlgebraicGeometry.ProEtale
