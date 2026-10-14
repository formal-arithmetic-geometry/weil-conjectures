/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.OpenCoverTensorPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Sheaf.AlgebraicGeometry.LocalMapPairCompatibility

/-! # Detecting pairwise compatibility on the base change of the overlap

Source: Stacks Project, Tag 01ZR (3), first proof by Zariski gluing.
(blueprint: lem-pc-local-map-pair-overlap-base-change). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.openCoverTensorPullbackComparison

/-- The overlap defect is the difference of the two sides of the descent square
on the universal overlap. Its source and target are actual pullbacks of modules.
Source: Stacks Project, Tag 01ZR (3), first proof by Zariski gluing.
(blueprint: lem-pc-local-map-pair-overlap-base-change). -/
noncomputable def localMapPairOverlapDefect
    {X : Scheme.{u}} (U : X.OpenCover.{u}) (F G : X.Modules)
    (r : ∀ x, (Scheme.Modules.pullback (U.f x)).obj F ⟶
      (Scheme.Modules.pullback (U.f x)).obj G) (a b : U.I₀) :
    (Scheme.Modules.pullback (pullback.fst (U.f a) (U.f b))).obj
        ((Scheme.Modules.pullback (U.f a)).obj F) ⟶
      (Scheme.Modules.pullback (pullback.snd (U.f a) (U.f b))).obj
        ((Scheme.Modules.pullback (U.f b)).obj G) :=
  let Q := modulesPseudofunctor.toDescentData U.f
  let g₁ := pullback.fst (U.f a) (U.f b)
  let g₂ := pullback.snd (U.f a) (U.f b)
  let t := g₁ ≫ U.f a
  let A := (Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback (U.f a)).obj F)
  let B := (Scheme.Modules.pullback g₂).obj ((Scheme.Modules.pullback (U.f b)).obj G)
  (show A ⟶ B from (Scheme.Modules.pullback g₁).map (r a) ≫
      (Q.obj G).hom t g₁ g₂ rfl pullback.condition.symm) -
    (show A ⟶ B from (Q.obj F).hom t g₁ g₂ rfl pullback.condition.symm ≫
      (Scheme.Modules.pullback g₂).map (r b))

/-- Pairwise compatibility after an arbitrary base change is equivalent to
vanishing of the pulled back, explicitly constructed overlap defect.
Source: Stacks Project, Tag 01ZR (3), first proof by Zariski gluing;
Mathlib pseudofunctor composition and descent naturality.
(blueprint: lem-pc-local-map-pair-overlap-base-change).

Proof: Let W be the universal overlap of charts a and b, with structural map t.
The pullback W times_X Y is canonically the overlap of the base changed charts.
Pull back the two composites defining the defect to this scheme. Pullback
composition, congruence along the pullback squares, and the unique comparison
between tensor and native pullback identify them, after conjugation by their
invertible source and target comparisons, with the two descent-square composites
for the transported local maps. Naturality moves each local map through the
comparisons, and the pseudofunctor associativity identity identifies the middle
transition maps. Additivity identifies zero of the difference with equality.
If the universal square commutes, pull it back along the unique map from any
universal test into the overlap; descent pullHom naturality gives that test's
square. Conversely evaluate compatibility on the universal overlap and cancel
the invertible comparisons. No compactness, finiteness, affineness or limit is
used. The same argument includes empty overlaps, identity base changes and zero
modules; it uses only canonical universal lifts, never chosen existence data. -/
theorem localMapPairOverlapDefect_baseChange_iff
    {X Y : Scheme.{u}} (U : X.OpenCover.{u}) (F G : X.Modules)
    (r₀ : ∀ x, (Scheme.Modules.pullback (U.f x)).obj F ⟶
      (Scheme.Modules.pullback (U.f x)).obj G) (a b : U.I₀) (q : Y ⟶ X) :
    let W := pullback (U.f a) (U.f b)
    let t : W ⟶ X := pullback.fst (U.f a) (U.f b) ≫ U.f a
    let V := U.pullback₁ q
    let Q := modulesPseudofunctor.toDescentData V.f
    let C := Scheme.Modules.tensorPullback q
    let r : ∀ x, (Q.obj (C.obj F)).obj x ⟶ (Q.obj (C.obj G)).obj x := fun x ↦
      let e := Scheme.Modules.openCoverTensorPullbackComparison q U x
      e.inv.app F ≫ (Scheme.Modules.pullback (U.pullbackHom q x)).map (r₀ x) ≫
        e.hom.app G
    Pseudofunctor.DescentData.PairCompatibility r a b ↔
      (Scheme.Modules.pullback (pullback.fst t q)).map
        (localMapPairOverlapDefect U F G r₀ a b) = 0 := by sorry

end AlgebraicGeometry
