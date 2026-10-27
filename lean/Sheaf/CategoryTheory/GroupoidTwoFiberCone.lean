module

public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
public import Mathlib.CategoryTheory.Comma.Basic

/-! # Two-fibre-product cones of fibred groupoids

Source: Stacks Project, Tags 003R and 04Y2
(blueprint: def-sfb-groupoid-two-fibre-cone).

A cone is a two-fibre product when its canonical functor to the comma category is
an equivalence in every fibre. For groupoid targets the comma arrow is automatically
invertible, so these are precisely the triples and commuting pairs of Tag 003R.
This description allows any choice of the two-fibre product, without choosing objects
from a bare existence assertion.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w

open CategoryTheory Opposite
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor

/-- Invertible modifications, with the category of strong transformations explicit.
This is Mathlib's `Iso`, with no extra data or new equivalence relation.
Source: Stacks Project, Tag 003R (blueprint: def-sfb-groupoid-two-fibre-cone). -/
abbrev StrongTrans.Iso {C : Type w} [SmallCategory C]
    {P Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    (a b : StrongTrans P Q) :=
  @CategoryTheory.Iso (StrongTrans P Q) (StrongTrans.homCategory (F := P) (G := Q)) a b

/-- The fibre natural transformation underlying an invertible modification.
Source: Stacks Project, Tag 003R (blueprint: def-sfb-groupoid-two-fibre-cone). -/
def StrongTrans.Iso.homNatTrans {C : Type w} [SmallCategory C]
    {P Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {a b : StrongTrans P Q} (e : StrongTrans.Iso a b) (T : C) :
    (a.app (.mk (op T))).toFunctor ⟶ (b.app (.mk (op T))).toFunctor :=
  ((@CategoryTheory.Iso.hom (StrongTrans P Q)
    (StrongTrans.homCategory (F := P) (G := Q)) a b e).as.app (.mk (op T))).toNatTrans

/-- A cone with a specified invertible comparison over the identity of the base.
Source: Stacks Project, Tag 003R (blueprint: def-sfb-groupoid-two-fibre-cone). -/
structure GroupoidTwoFiberCone {C : Type w} [SmallCategory C]
    {X Y Z : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    (f : StrongTrans X Y) (g : StrongTrans Z Y)
    (P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}) where
  /-- First projection. -/
  fst : StrongTrans P X
  /-- Second projection. -/
  snd : StrongTrans P Z
  /-- The comparison between the two composites. -/
  cell : StrongTrans.Iso (StrongTrans.vcomp fst f) (StrongTrans.vcomp snd g)

/-- The canonical fibre functor sends an object to its projections and comparison,
and an arrow to its pair of projections.
Source: Stacks Project, Tag 003R (blueprint: def-sfb-groupoid-two-fibre-cone). -/
def GroupoidTwoFiberCone.fiberComparison {C : Type w} [SmallCategory C]
    {X Y Z P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {f : StrongTrans X Y} {g : StrongTrans Z Y} (p : GroupoidTwoFiberCone f g P)
    (T : C) : P.obj (.mk (op T)) ⥤
      Comma (f.app (.mk (op T))).toFunctor (g.app (.mk (op T))).toFunctor where
  obj x :=
    { left := (p.fst.app (.mk (op T))).toFunctor.obj x
      right := (p.snd.app (.mk (op T))).toFunctor.obj x
      hom := (StrongTrans.Iso.homNatTrans p.cell T).app x }
  map a :=
    { left := (p.fst.app (.mk (op T))).toFunctor.map a
      right := (p.snd.app (.mk (op T))).toFunctor.map a
      w := (StrongTrans.Iso.homNatTrans p.cell T).naturality a }

/-- The cone represents the fibrewise category of triples and commuting pairs.
The groupoid requirements make the ordinary comma category the iso-comma category.
Source: Stacks Project, Tag 003R (blueprint: def-sfb-groupoid-two-fibre-cone). -/
def GroupoidTwoFiberCone.IsTwoFiberProduct {C : Type w} [SmallCategory C]
    {X Y Z P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {f : StrongTrans X Y} {g : StrongTrans Z Y} (p : GroupoidTwoFiberCone f g P) : Prop :=
  (∀ T : C, IsGroupoid (X.obj (.mk (op T)))) ∧
  (∀ T : C, IsGroupoid (Y.obj (.mk (op T)))) ∧
  (∀ T : C, IsGroupoid (Z.obj (.mk (op T)))) ∧
  (∀ T : C, IsGroupoid (P.obj (.mk (op T)))) ∧
  ∀ T : C, (p.fiberComparison T).IsEquivalence

/-- A map of two-fibre cones with its projection comparisons. The equation is the
compatibility with the comparison 2-cell, evaluated in each fibre.
Source: Stacks Project, Tag 04Y2 via 04Y1
(blueprint: def-sfb-groupoid-two-fibre-cone). -/
structure GroupoidTwoFiberCone.Comparison {C : Type w} [SmallCategory C]
    {X Y Z P X' Y' Z' P' : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {f : StrongTrans X Y} {g : StrongTrans Z Y}
    {f' : StrongTrans X' Y'} {g' : StrongTrans Z' Y'}
    (p : GroupoidTwoFiberCone f g P) (q : GroupoidTwoFiberCone f' g' P')
    (k : StrongTrans P P') (iX : StrongTrans X X') (iY : StrongTrans Y Y')
    (iZ : StrongTrans Z Z')
    (ef : StrongTrans.Iso (StrongTrans.vcomp iX f') (StrongTrans.vcomp f iY))
    (eg : StrongTrans.Iso (StrongTrans.vcomp iZ g') (StrongTrans.vcomp g iY)) where
  /-- Compatibility with the first projection. -/
  left : StrongTrans.Iso (StrongTrans.vcomp k q.fst) (StrongTrans.vcomp p.fst iX)
  /-- Compatibility with the second projection. -/
  right : StrongTrans.Iso (StrongTrans.vcomp k q.snd) (StrongTrans.vcomp p.snd iZ)
  /-- Compatibility with the comparison isomorphism. -/
  comm (T : C) (x : P.obj (.mk (op T))) :
    (f'.app (.mk (op T))).toFunctor.map
        ((StrongTrans.Iso.homNatTrans left T).app x) ≫
      (StrongTrans.Iso.homNatTrans ef T).app
        ((p.fst.app (.mk (op T))).toFunctor.obj x) ≫
      (iY.app (.mk (op T))).toFunctor.map
        ((StrongTrans.Iso.homNatTrans p.cell T).app x) =
    (StrongTrans.Iso.homNatTrans q.cell T).app
        ((k.app (.mk (op T))).toFunctor.obj x) ≫
      (g'.app (.mk (op T))).toFunctor.map
        ((StrongTrans.Iso.homNatTrans right T).app x) ≫
      (StrongTrans.Iso.homNatTrans eg T).app
        ((p.snd.app (.mk (op T))).toFunctor.obj x)

/-- A map of cones on the same cospan, preserving both projections and the 2-cell.
Source: Stacks Project, Tag 04Y2 via 04Y1
(blueprint: def-sfb-groupoid-two-fibre-cone). -/
structure GroupoidTwoFiberCone.SameComparison {C : Type w} [SmallCategory C]
    {X Y Z P Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {f : StrongTrans X Y} {g : StrongTrans Z Y}
    (p : GroupoidTwoFiberCone f g P) (q : GroupoidTwoFiberCone f g Q)
    (h : StrongTrans P Q) where
  /-- First projection comparison. -/
  left : StrongTrans.Iso (StrongTrans.vcomp h q.fst) p.fst
  /-- Second projection comparison. -/
  right : StrongTrans.Iso (StrongTrans.vcomp h q.snd) p.snd
  /-- Compatibility with the comparison 2-cell. -/
  comm (T : C) (x : P.obj (.mk (op T))) :
    (f.app (.mk (op T))).toFunctor.map
        ((StrongTrans.Iso.homNatTrans left T).app x) ≫
      (StrongTrans.Iso.homNatTrans p.cell T).app x =
    (StrongTrans.Iso.homNatTrans q.cell T).app
        ((h.app (.mk (op T))).toFunctor.obj x) ≫
      (g.app (.mk (op T))).toFunctor.map
        ((StrongTrans.Iso.homNatTrans right T).app x)

end CategoryTheory.Pseudofunctor
