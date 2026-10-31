/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.MonoschemeToricRealization
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.Algebra.Category.Grp.Basic

/-! # Descent data for normalized blowup towers with their ordered centers

Source: ILO, Travaux de Gabber, VIII 2.2.3--2.2.11 and 5.5.3--5.5.5
(blueprint: def-per-normalized-tower-descent-data).

The tower and the normalized blowup are the existing constructions. Descent is expressed
by the existing Yoneda transport datum at every level. Its naturality and cocycle are the
usual scheme isomorphisms on double overlaps and their equation on triple overlaps.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Monoscheme.NormalizedTower

/-- The actual composite of the arrows to level zero, including the identity for length zero.
Source: ILO VIII 2.2.5 (blueprint: def-per-normalized-tower-descent-data). -/
def toFirst {n : ℕ} (T : NormalizedTower.{u} n) (i : Fin (n + 1)) :
    T.level i ⟶ T.level 0 :=
  Fin.induction (𝟙 (T.level 0)) (fun j f ↦ T.arrow j ≫ f) i

/-- Admissible centers have nowhere dense zero sets. Coherence is already part of each
`IsNormalizedBlowup` in `NormalizedTower.blowup` (finite generation on affine opens).
Source: ILO VIII 2.2.5, 2.3.2 (blueprint: def-per-normalized-tower-descent-data). -/
def HasNowhereDenseCenters {n : ℕ} (T : NormalizedTower.{u} n) : Prop :=
  ∀ i : Fin n, IsNowhereDense ((T.center i).support : Set (T.level i.castSucc))

/-- A map between synchronized towers preserves arrows and the actual extended ideals.
Source: ILO VIII 2.2.7--2.2.8 (blueprint: def-per-normalized-tower-descent-data). -/
structure CenterMap {n : ℕ} (T S : NormalizedTower.{u} n) where
  map : ∀ i, T.level i ⟶ S.level i
  commutes : ∀ i : Fin n, T.arrow i ≫ map i.castSucc = map i.succ ≫ S.arrow i
  centers : ∀ i : Fin n, T.center i = (S.center i).comap (map i.castSucc)

/-- A synchronized isomorphism keeps the ordered centers, including unit-ideal stages.
Source: ILO VIII 2.2.3--2.2.5, 5.5.3
(blueprint: def-per-normalized-tower-descent-data). -/
structure CenterIso {n : ℕ} (T S : NormalizedTower.{u} n) where
  iso : ∀ i, T.level i ≅ S.level i
  commutes : ∀ i : Fin n,
    T.arrow i ≫ (iso i.castSucc).hom = (iso i.succ).hom ≫ S.arrow i
  centers : ∀ i : Fin n, T.center i = (S.center i).comap (iso i.castSucc).hom

/-- Scheme pullback of all levels, retaining all the centers and stage labels. The
cartesian condition is imposed on every level, rather than on an arbitrary comparison map.
Source: ILO VIII 2.2.8 (blueprint: def-per-normalized-tower-descent-data). -/
def CenterMap.IsCartesian {n : ℕ} {T S : NormalizedTower.{u} n}
    (c : CenterMap T S) : Prop :=
  ∀ i, IsPullback (c.map i) (T.toFirst i) (S.toFirst i) (c.map 0)

/-- Descent on each scheme level, commuting with the arrows and identifying the center
ideals on the overlaps. `Over.DescentDatum` includes naturality, diagonal and cocycle laws.
The universal overlap for level i is `T_i ×_X U`; its two maps to `T_i` are the first
projection and the datum's `toHom`. Comparing ideal pullbacks along them is precisely
identification of the two center ideals in the usual double-overlap presentation.
Source: ILO VIII 2.2.11, 5.5.5 (blueprint: def-per-normalized-tower-descent-data). -/
structure DescentData {n : ℕ} {X : Scheme.{u}} (T : NormalizedTower.{u} n)
    (uMap : T.level 0 ⟶ X) where
  level : ∀ i, Over.DescentDatum uMap (Over.mk (T.toFirst i))
  arrows : ∀ (i : Fin n) (W : Scheme.{u}) (f g : W ⟶ T.level 0)
    (h : f ≫ uMap = g ≫ uMap)
    (a : Over.mk f ⟶ Over.mk (T.toFirst i.succ))
    (b : Over.mk f ⟶ Over.mk (T.toFirst i.castSucc)),
    a.left ≫ T.arrow i = b.left →
      ((level i.succ).transport f g h a).left ≫ T.arrow i =
        ((level i.castSucc).transport f g h b).left
  centers : ∀ i : Fin n,
    (T.center i).comap (pullback.fst (T.toFirst i.castSucc ≫ uMap) uMap) =
      (T.center i).comap (level i.castSucc).toHom

/-- The orbit relation of the supplied descent isomorphisms on all scheme-valued points.
Source: ILO VIII 2.2.11 (blueprint: def-per-normalized-tower-descent-data). -/
def DescentData.Related {n : ℕ} {X : Scheme.{u}} {T : NormalizedTower.{u} n}
    {uMap : T.level 0 ⟶ X} (D : DescentData T uMap) (i : Fin (n + 1))
    {W : Scheme.{u}} (x y : W ⟶ T.level i) : Prop :=
  ∃ (f g : W ⟶ T.level 0) (h : f ≫ uMap = g ≫ uMap)
    (a : Over.mk f ⟶ Over.mk (T.toFirst i)),
    a.left = x ∧ ((D.level i).transport f g h a).left = y

/-- A global tower realizes the given datum when its comparison is cartesian and
identifies precisely the points related by that datum. Invariance, together with the
cartesian squares, says that the induced overlap isomorphism is the specified one.
Source: ILO VIII 2.2.11 (blueprint: def-per-normalized-tower-descent-data). -/
def DescentData.Realizes {n : ℕ} {X : Scheme.{u}} {T : NormalizedTower.{u} n}
    {uMap : T.level 0 ⟶ X} (D : DescentData T uMap) (S : NormalizedTower.{u} n)
    (e : S.level 0 ≅ X) (c : CenterMap T S) : Prop :=
  c.map 0 ≫ e.hom = uMap ∧ c.IsCartesian ∧
    ∀ (i : Fin (n + 1)) (W : Scheme.{u}) (x y : W ⟶ T.level i),
      D.Related i x y → x ≫ c.map i = y ≫ c.map i

/-- The subset of the initial scheme consisting of images of all ordered centers.
Source: ILO VIII 2.2.5 (blueprint: def-per-normalized-tower-descent-data). -/
def centerImages {n : ℕ} (T : NormalizedTower.{u} n) : Set (T.level 0) :=
  ⋃ i : Fin n, (T.toFirst i.castSucc) '' ((T.center i).support : Set (T.level i.castSucc))

/-- An action on the tower, written on all scheme-valued points. Naturality is the Yoneda
condition; for a representable group this is an actual scheme group action, and for a
constant group presheaf it is an ordinary group action. The centers are invariant as
ideals, rather than just as closed subsets. No action on the base is assumed trivial.
Source: ILO VIII 5.5.5 (blueprint: def-per-normalized-tower-descent-data). -/
structure Action (G : Scheme.{u}ᵒᵖ ⥤ GrpCat.{v}) {n : ℕ}
    (T : NormalizedTower.{u} n) where
  act : ∀ (i : Fin (n + 1)) (W : Scheme.{u}),
    G.obj (op W) → (W ⟶ T.level i) → (W ⟶ T.level i)
  one : ∀ i W x, act i W 1 x = x
  mul : ∀ i W g h x, act i W (g * h) x = act i W g (act i W h x)
  naturality : ∀ i (W V : Scheme.{u}) (k : V ⟶ W) g x,
    k ≫ act i W g x = act i V ((G.map k.op) g) (k ≫ x)
  arrows : ∀ (i : Fin n) W g x,
    act i.succ W g x ≫ T.arrow i = act i.castSucc W g (x ≫ T.arrow i)
  centers : ∀ (i : Fin n) W g x,
    (T.center i).comap (act i.castSucc W g x) = (T.center i).comap x

/-- Compatibility with descent means invariance of its actual transport relation.
This includes the level-zero datum and therefore descends the base action as well.
Source: ILO VIII 5.5.5 (blueprint: def-per-normalized-tower-descent-data). -/
def Action.Compatible {G : Scheme.{u}ᵒᵖ ⥤ GrpCat.{v}} {n : ℕ}
    {X : Scheme.{u}} {T : NormalizedTower.{u} n} {uMap : T.level 0 ⟶ X}
    (A : Action G T) (D : DescentData T uMap) : Prop :=
  ∀ i W g (x y : W ⟶ T.level i), D.Related i x y →
    D.Related i (A.act i W g x) (A.act i W g y)

end AlgebraicGeometry.Monoscheme.NormalizedTower
