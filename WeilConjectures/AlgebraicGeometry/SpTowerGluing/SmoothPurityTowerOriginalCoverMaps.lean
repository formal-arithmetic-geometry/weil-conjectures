/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerPairOpenRestriction
public import WeilConjectures.AlgebraicGeometry.SmoothPurityRingedBinaryDescent
public import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData

/-! # Canonical original-coordinate open-cover maps

Source: latest smooth-purity blueprint, Local pairs, Gluing and Uniformity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The actual restriction compositor with its specified composite-open equality.
Source: latest smooth-purity blueprint, Gluing, nested source opens
(blueprint: def-sp-tower-original-cover-maps). -/
def originalRestrictionComp {W U X : Scheme.{u}}
    (a : W ⟶ U) (j : U ⟶ X) (i : W ⟶ X) (w : a ≫ j = i) :
    SpTowerCalculus.etalePullback l E b o q j ⋙
        SpTowerCalculus.etalePullback l E b o q a ≅
      SpTowerCalculus.etalePullback l E b o q i :=
  spActualRestrictionComp l E b o j a (q.abelian X) (q.abelian U) (q.abelian W) ≪≫
    eqToIso (congrArg (fun f ↦ SpTowerCalculus.etalePullback l E b o q f) w)

/-- The nested-open counit in original coefficient-tower coordinates.
Source: latest smooth-purity blueprint, Gluing, the actual open-cover triangle
(blueprint: def-sp-tower-original-cover-maps). -/
def originalOpenAlpha {W U X : Scheme.{u}}
    (a : W ⟶ U) (j : U ⟶ X) (i : W ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion i]
    (w : a ≫ j = i)
    (H : spDerivedCoefficientTowers l E X (q.abelian X)) :
    (SpTowerCalculus.openExtension l E b o q i).obj
        ((SpTowerCalculus.etalePullback l E b o q i).obj H) ⟶
      (SpTowerCalculus.openExtension l E b o q j).obj
        ((SpTowerCalculus.etalePullback l E b o q j).obj H) :=
  TowerOpenCover.nestedCounit (openAdjunction l E b o q j)
    (openAdjunction l E b o q i)
    (originalRestrictionComp l E b o q a j i w) H

/-- Transport a local counit to compact support of the extended restricted object.
Source: latest smooth-purity blueprint, Gluing, the two open summands
(blueprint: def-sp-tower-original-cover-maps). -/
def originalOpenCounit
    {X Y U : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (j : U ⟶ X) [IsOpenImmersion j]
    (H : spDerivedCoefficientTowers l E X (q.abelian X))
    (K : spDerivedCoefficientTowers l E Y (q.abelian Y))
    (HU : spDerivedCoefficientTowers l E U (q.abelian U))
    (e : (SpTowerCalculus.etalePullback l E b o q j).obj H ≅ HU)
    (epsU : (SpTowerCalculus.F l E b o q (c.precomp j)).obj HU ⟶ K) :
    (SpTowerCalculus.F l E b o q c).obj
        ((SpTowerCalculus.openExtension l E b o q j).obj
          ((SpTowerCalculus.etalePullback l E b o q j).obj H)) ⟶ K :=
  (SpTowerCalculus.openComposition l E b o q j c).hom.app _ ≫
    (SpTowerCalculus.F l E b o q (c.precomp j)).map e.hom ≫ epsU

end AlgebraicGeometry.ProEtale.SpTowerGluing
