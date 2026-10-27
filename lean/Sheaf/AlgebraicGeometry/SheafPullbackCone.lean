module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The explicit compatible-pair presheaf pullback cone

Source: Stacks Project, Spaces, Tags 04T9 and 02X2, the fibre product of sheaves
and its universal property (blueprint: def-trf-sheaf-pullback-cone).

This is the existing explicit construction, moved from `SheafPullbackDiagonal`.
It applies to arbitrary presheaves, with literal compatible pairs as sections.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite ConcreteCategory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The presheaf with sections `(x,y)` satisfying `f(x) = g(y)`, with componentwise
restriction. The section type is Mathlib's explicit type pullback; its restriction
maps and projections are constructed directly, without chosen limiting lifts.
Source: Stacks, Spaces, Tags 04T9 and 02X2
(blueprint: def-trf-sheaf-pullback-cone). -/
abbrev sheafPullbackCone {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) : PullbackCone f g :=
  PullbackCone.mk (W := {
    obj T := Types.PullbackObj (f.app T) (g.app T)
    map {T U} a := ↾fun p ↦ ⟨(F.map a p.val.1, G.map a p.val.2), by
      change f.app U (F.map a p.val.1) = g.app U (G.map a p.val.2)
      calc
        f.app U (F.map a p.val.1) = H.map a (f.app T p.val.1) :=
          congr_hom (f.naturality a) p.val.1
        _ = H.map a (g.app T p.val.2) := congrArg (H.map a) p.property
        _ = g.app U (G.map a p.val.2) :=
          (congr_hom (g.naturality a) p.val.2).symm⟩
    map_id T := by
      apply ConcreteCategory.ext
      apply TypeCat.Fun.ext
      funext p
      apply Subtype.ext
      exact Prod.ext (congr_hom (F.map_id T) p.val.1)
        (congr_hom (G.map_id T) p.val.2)
    map_comp a b := by
      apply ConcreteCategory.ext
      apply TypeCat.Fun.ext
      funext p
      apply Subtype.ext
      exact Prod.ext (congr_hom (F.map_comp a b) p.val.1)
        (congr_hom (G.map_comp a b) p.val.2) })
    { app T := ↾fun p ↦ p.val.1
      naturality := by intros; rfl }
    { app T := ↾fun p ↦ p.val.2
      naturality := by intros; rfl }
    (by
      apply NatTrans.ext
      funext T
      apply ConcreteCategory.ext
      apply TypeCat.Fun.ext
      funext p
      exact p.property)

end AlgebraicGeometry.AlgebraicSpace
