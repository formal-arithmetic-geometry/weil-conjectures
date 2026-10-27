# AlgebraicGeometry.AlgebraicSpace.sheafPullbackCone

## Reason

Restore the quarantined zero-hole definition assigned by coord/rework.tsv. The archived
module currently compiles alone, so the original global-build failure has no reproducible
single-file diagnostic. This delivery also replaces the generic pointwise limit assembly
with a direct construction of the presheaf stated in the node: literal compatible pairs,
componentwise restriction, and coordinate projections. All functor, naturality and cone
laws are proved directly. There is no chosen data and no postponed proof.

The old public import of Sheaf.CategoryTheory.SiteCoveringAxioms is unused. Remove it
and Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks; import
Mathlib.CategoryTheory.Comma.Over.Basic explicitly for Over. Keep the scheme and explicit
type pullback imports. No mathematical statement, universe, declaration name, binder or
result type changes. The node retains its definition, statement dependencies and empty
proof dependency list; its Lean note records the restoration. Target meanings are unchanged.

## Old

Public imports: Mathlib.AlgebraicGeometry.Scheme,
Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks,
Mathlib.CategoryTheory.Limits.Types.Pullbacks,
Sheaf.CategoryTheory.SiteCoveringAxioms.

```lean
abbrev sheafPullbackCone {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) : PullbackCone f g :=
  PullbackCone.combine f g (fun T ↦ Types.pullbackCone (f.app T) (g.app T))
    (fun T ↦ (Types.pullbackLimitCone (f.app T) (g.app T)).isLimit)
```

## New

Public imports: Mathlib.AlgebraicGeometry.Scheme,
Mathlib.CategoryTheory.Limits.Types.Pullbacks,
Mathlib.CategoryTheory.Comma.Over.Basic.

```lean
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
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SheafPullbackCone --uses
AlgebraicGeometry.AlgebraicSpace.sheafPullbackCone` reports `unknown module(s)` because
its source is quarantined. A full import/name search in live and quarantined Lean and DAG
nodes finds exactly the two direct consumers below; neither has a claim at inspection.
Both are compiled unchanged against the new definition as sandbox-only checks. Their
files are not delivered or withdrawn; their independent rework assignments remain open.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SheafPullbackDiagonal | unclaimed; quarantined | Literal subtype sections and projections preserved; original theorem needs no adaptation. Its own SiteCoveringAxioms import is retained. |
| Sheaf.AlgebraicGeometry.PresheafPullbackEtalePointLifting | unclaimed; quarantined | Nested cones and the field-point p.val expressions preserve their exact types; original theorem needs no adaptation. |

The two DAG parents retain their statement dependencies on def-trf-sheaf-pullback-cone.
The owning unit sk-i-curve-zero has no realized entry for this definition; its route
is unchanged. The quarantine archive is preserved.

## Status

landed 20261023T102516-L-2912642 2026-10-23 (merge of deliver/C3/Sheaf.AlgebraicGeometry.SheafPullbackCone)
