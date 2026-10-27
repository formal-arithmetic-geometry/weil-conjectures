/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SmoothPurityBaseChangeData

/-! # Tensor part of tower purity base change
(blueprint: lem-sp-tower-factor-tensor). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SmoothPurityBaseChange

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
  (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
  (q : SpTowerCalculus.Coordinates ell E b)

/-- The tensor/counit factor commutes with the actual exceptional exchange.
Only the canonical unit comparison is used; the orientation square is independent.
Source: latest blueprint purity-bc-factors proof (2)
(blueprint: lem-sp-tower-factor-tensor).

Proof: identify the supplied adjoints with the ones furnished by tower exceptional
base change using uniqueness of right adjoints, compatibly with their counits.
Their unit mate is invertible: its evaluations are the finite smooth exceptional
exchanges, and evaluation is conservative on objects. Use tower_smooth_domains
to place the pulled-back and primed tensor sources in the full uniform
constructible finite-Tor domains of the two adjunctions.
The supplied WordComparison equations identify s with the strict coefficient-unit
pullback comparison: both maps are between degree-zero sheaf towers, so equality
is detected by exact evaluation. Rewrite the tensor maps by their inverse
projection/counit transpose definitions and the exchange by its counit mate.
Apply compact_projection_base_change to the fixed compactification and its pulled-back
compactification. Naturality of projection and the unit exchange transports the
projection isomorphism to the mixed tensor source. Apply the restricted
tensorCounitExchangeCalculus to these data. The source isomorphism is exactly
towerTensorComparison, including the realization counits. Its first conclusion,
composed with the inverse source comparison, is the equation below. All equalities
are proved before finite evaluation in the ambient ordinary derived tower category. -/
theorem tower_factor_tensor
    (D : FiniteFieldDatum.{u}) (_hne : ell ≠ D.p)
    (X Y X' Y' : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsNoetherian X'.left] [IsNoetherian Y'.left]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.left]
    [IsSeparated f.left] [QuasiCompact f.left] [HasCompactification f.left]
    [QuasiCompact f'.left] [HasCompactification f'.left]
    (c : Compactification f.left) (a : SpTowerMate.Data ell E b o q sq c)
    (x : SpTowerShriek.OpenExchange ell E b o)
    (hb : IsIso (SpTowerMate.beta ell E b o q a x))
    (w : SpChartAdmissibility.Twists ell E X.left)
    (w' : SpChartAdmissibility.Twists ell E X'.left)
    (P : TowerPurityAt ell E b o q c d w a.support_closed a.right
      a.adjunction a.levels)
    (P' : TowerPurityAt ell E b o q (c.ofIsPullback sq) d w' a.support_closed'
      a.right' a.adjunction' a.levels')
    (gv : ∀ n : ℕ, SpTowerP1.GeometricCoordinates ell E n v.left)
    (s : (SpTowerShriek.pull ell E b (o.geometry v.left)).obj
        (SpTowerGamma.unit ell E Y.left) ≅ SpTowerGamma.unit ell E Y'.left)
    (hs : ∀ n : ℕ, SpTowerP1.WordComparison ell E n
        (SpTowerP1.pullWord ell E n b (o.geometry v.left) (gv n)
          (SpTowerP1.unitWord ell E n Y.left (P.coefficientsY n)))
        (SpTowerP1.unitWord ell E n Y'.left (P'.coefficientsY n)) s.hom
        (((Etale.ordinaryFinitePullback (SpTowerP1.levelRing ell E n) v.left).mapIso
          (Etale.singleFunctorObjUnitIso
            (ModuleCat.{u + 1} (SpTowerP1.levelRing ell E n)) Y.left) ≪≫
          Etale.leftDerivedUpperStarUnitIso
            (ModuleCat.{u + 1} (SpTowerP1.levelRing ell E n)) v.left ≪≫
          (Etale.singleFunctorObjUnitIso
            (ModuleCat.{u + 1} (SpTowerP1.levelRing ell E n)) Y'.left).symm).hom)) :
      ∀ K : SpTowerCalculus.C ell E b q Y.left,
        (SpTowerShriek.pull ell E b (o.geometry u'.left)).map
            (towerTensorMap ell E b o q c d w a.support_closed a.right
              a.adjunction a.levels P K) ≫ towerExchange ell E b o q a x hb K =
          (towerTensorComparison ell E b o q a K _).hom ≫
            (SpTowerShriek.tensor ell E b X'.left).map
              (Prod.mkHom (𝟙 _)
                (towerUnitExchange ell E b o q a x hb P.unit_mem P'.unit_mem s)) ≫
            towerTensorMap ell E b o q (c.ofIsPullback sq) d w' a.support_closed'
              a.right' a.adjunction' a.levels' P' ((SpTowerMate.V ell E b o q a).obj K) := by sorry

end AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
