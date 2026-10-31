/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleCoefficientTransportInterfaces

/-!
# Interfaces for strict étale isomorphic-stage projections

The records and their normalized projection composition are separated from the
existence theorem so the construction can be proved in independent stages.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- The normalized open and proper faces of a quotient projection square.
Source: Zheng, Construction 5.15 and Lemma 5.22
(blueprint: def-pur-strict-etale-isomorphic-stage-projection-interfaces). -/
structure StrictEtaleQuotientProjection
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O ell c) where
  openProjection : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PX.scalar h).derived ⋙ S.levelDerivedOpen n ≅
      S.levelDerivedOpen m ⋙ (S.PZ.scalar h).derived
  proper : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PZ.scalar h).derived ⋙ (S.properDerived.level n).direct ≅
      (S.properDerived.level m).direct ⋙ (S.PY.scalar h).derived
  open_mate : ∀ {m n : ℕ} (h : n ≤ m),
    (mateEquiv (S.levelDerivedOpenAdjunction m) (S.levelDerivedOpenAdjunction n)
      (.mk _ _ _ _ (openProjection h).hom)).natTrans = (S.openDerived.derivedTensor h).inv
  proper_mate : ∀ {m n : ℕ} (h : n ≤ m),
    (proper h).inv =
      (mateEquiv (S.properDerived.level m).adjunction (S.properDerived.level n).adjunction
        (.mk _ _ _ _ (S.properDerived.derivedTensor h).hom)).natTrans

/-- Compose the open and proper quotient faces.
Source: Zheng, Construction 5.15
(blueprint: def-pur-strict-etale-isomorphic-stage-projection-interfaces). -/
def StrictEtaleQuotientProjection.projection
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S : StrictEtaleCompactSupport O ell c} (Q : StrictEtaleQuotientProjection S)
    {m n : ℕ} (h : n ≤ m) :
    (S.PX.scalar h).derived ⋙ S.levelFunctor n ≅
      S.levelFunctor m ⋙ (S.PY.scalar h).derived :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (Q.openProjection h) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Q.proper h) ≪≫
      (Functor.associator _ _ _).symm

/-- Left-adjoint projection faces and their evaluation and quotient cubes.
Source: Zheng, Constructions 4.1 and 5.15, Lemma 5.22
(blueprint: def-pur-strict-etale-isomorphic-stage-projection-interfaces). -/
structure StrictEtaleTransportProjection
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ) where
  compact : StrictEtaleCompactSupportTransport a c SA SB TX TY TZ
  level : ∀ n, SA.levelFunctor (index n) ⋙ (TY.level n).derived ≅
    (TX.level n).derived ⋙ SB.levelFunctor n
  quotientX : StrictEtaleTransportQuotient TX
  quotientY : StrictEtaleTransportQuotient TY
  evaluation : ∀ n K,
    (TY.derivedEvaluation n).hom.app (SA.functor.obj K) ≫
      (TY.level n).derived.map ((SA.evaluation (index n)).hom.app K) ≫
      (level n).hom.app ((SA.PX.evaluation (index n)).obj K) =
    (SB.PY.evaluation n).map (compact.projection.hom.app K) ≫
      (SB.evaluation n).hom.app (TX.derived.obj K) ≫
      (SB.levelFunctor n).map ((TX.derivedEvaluation n).hom.app K)
  quotient_cube : ∀ (QA : StrictEtaleQuotientProjection SA)
    (QB : StrictEtaleQuotientProjection SB) {m n : ℕ} (h : n ≤ m) K,
    (SB.levelFunctor n).map ((quotientX.derived h).hom.app K) ≫
      (QB.projection h).hom.app ((TX.level m).derived.obj K) ≫
      (SB.PY.scalar h).derived.map ((level m).inv.app K) =
    (level n).inv.app ((SA.PX.scalar (index.monotone h)).derived.obj K) ≫
      (TY.level n).derived.map ((QA.projection (index.monotone h)).hom.app K) ≫
      (quotientY.derived h).hom.app ((SA.levelFunctor (index m)).obj K)


end AlgebraicGeometry
