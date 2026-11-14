/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernPullbackData
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Projective.TowerClassProjective
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernOrdinaryScalarPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarPullbackCounitLift

/-! # Pullback of scalar extension from integral quotient coefficients
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem scalar_shift_endpoint
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (S : C ⥤ D) (S' : C' ⥤ D') (P : C ⥤ C') (Q : D ⥤ D')
    [S.CommShift ℤ] [S'.CommShift ℤ] [P.CommShift ℤ] [Q.CommShift ℤ]
    (κ : S ⋙ Q ⟶ P ⋙ S') [NatTrans.CommShift κ ℤ]
    {M : C} {M' : C'} {V : D} {V' : D'}
    (t : P.obj M ⟶ M') (v : S.obj M ⟶ V) (v' : S'.obj M' ⟶ V')
    (w : Q.obj V ⟶ V')
    (h : κ.app M ≫ S'.map t ≫ v' = Q.map v ≫ w) (n : ℤ) :
    κ.app (M⟦n⟧) ≫
        S'.map ((P.commShiftIso n).hom.app M ≫ t⟦n⟧') ≫
        (S'.commShiftIso n).hom.app M' ≫ v'⟦n⟧' =
      Q.map ((S.commShiftIso n).hom.app M ≫ v⟦n⟧') ≫
        (Q.commShiftIso n).hom.app V ≫ w⟦n⟧' := by
  have hc := κ.shift_app_comm n M
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hc
  calc
    _ = κ.app (M⟦n⟧) ≫ S'.map ((P.commShiftIso n).hom.app M) ≫
        (S'.commShiftIso n).hom.app (P.obj M) ≫ (S'.map t)⟦n⟧' ≫ v'⟦n⟧' := by
      simp only [Functor.map_comp, Category.assoc]
      rw [S'.commShiftIso_hom_naturality_assoc]
    _ = Q.map ((S.commShiftIso n).hom.app M) ≫
        (Q.commShiftIso n).hom.app (S.obj M) ≫
        (κ.app M ≫ S'.map t ≫ v')⟦n⟧' := by
      simp only [Functor.map_comp]
      rw [← reassoc_of% hc]
    _ = Q.map ((S.commShiftIso n).hom.app M) ≫
        (Q.commShiftIso n).hom.app (S.obj M) ≫
        (Q.map v ≫ w)⟦n⟧' := by rw [h]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [Q.commShiftIso_hom_naturality_assoc]

/-- Construct the intermediate R inverse image and the R-to-A scalar comparison.
The endpoint equations start on R-modules, not on integral complexes. In particular
they contain no integral reduction functor, unitIso of Chern data, or rootIso of
Chern data. They can be used with any reduction model after its separate comparison. -/
theorem tower_chernScalar_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hX : IsUnit (l : Γ(X, ⊤))) (_hY : IsUnit (l : Γ(Y, ⊤)))
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (_nY : cY.Normalized l E) (_nX : cX.Normalized l E)
    (θ₀ : CoefficientPullback l E b f g) (θ₁ : LinePullback l E f g cY cX) :
    ∃ d : IntegralCoefficientPullback l E f cY cX,
    ∃ κ : cY.scalar.T ⋙ SpTowerShriek.pull l E b g ⟶
        d.pull.mapDerivedCategory ⋙ cX.scalar.T,
      κ.app (unit Y (Rrings l Y)) ≫ cX.scalar.T.map d.derivedUnit.hom ≫
          cX.scalarUnit.hom =
        (SpTowerShriek.pull l E b g).map cY.scalarUnit.hom ≫
          (θ₀.derivedIso l E).hom ∧
      κ.app (((DerivedCategory.singleFunctor (Systems Y (Rrings l Y)) 0).obj
          cY.rootModule)⟦(2 : ℤ)⟧) ≫
          cX.scalar.T.map (d.derivedRoot 2).hom ≫ scalarRootTarget cX =
        (SpTowerShriek.pull l E b g).map (scalarRootTarget cY) ≫
          ((SpTowerShriek.pull l E b g).commShiftIso (2 : ℤ)).hom.app (line l E cY) ≫
          ((θ₁.derivedIso l E).hom)⟦(2 : ℤ)⟧' := by
  obtain ⟨d, α, eY, eX, hflat, heY, heX, hα₀, hα₁⟩ :=
    tower_chernOrdinaryScalar_pullback l E f _hX _hY b g cY cX _nY _nX θ₀ θ₁
  obtain ⟨κ, hshift, hκ⟩ := tower_scalarPullback_counitLift l E g cY cX d α hflat
  have : NatTrans.CommShift κ ℤ := hshift
  have endpoint (M : Systems Y (Rrings l Y)) (M' : Systems X (Rrings l X))
      (N : Systems Y (Arings l E Y)) (N' : Systems X (Arings l E X))
      (t : d.pull.obj M ⟶ M')
      (aY : cY.scalar.model.E.obj M ⟶ N) (aX : cX.scalar.model.E.obj M' ⟶ N')
      (w : g.pull.obj N ⟶ N')
      (hw : α.hom.app M ≫ cX.scalar.model.E.map t ≫ aX = g.pull.map aY ≫ w) :
      κ.app ((DerivedCategory.singleFunctor (Systems Y (Rrings l Y)) 0).obj M) ≫
          cX.scalar.T.map ((d.pull.mapDerivedCategorySingleFunctor 0).hom.app M ≫
            (DerivedCategory.singleFunctor (Systems X (Rrings l X)) 0).map t) ≫
          (scalarSingleCounit cX).app M' ≫
          (DerivedCategory.singleFunctor (Systems X (Arings l E X)) 0).map aX =
        (SpTowerShriek.pull l E b g).map ((scalarSingleCounit cY).app M ≫
          (DerivedCategory.singleFunctor (Systems Y (Arings l E Y)) 0).map aY) ≫
          (g.pull.mapDerivedCategorySingleFunctor 0).hom.app N ≫
          (DerivedCategory.singleFunctor (Systems X (Arings l E X)) 0).map w := by
    have ht := (scalarSingleCounit cX).naturality t
    simp only [Functor.comp_map] at ht
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% ht, reassoc_of% (hκ M)]
    have hm := congrArg
      (DerivedCategory.singleFunctor (Systems X (Arings l E X)) 0).map hw
    simp only [Functor.map_comp] at hm
    rw [hm]
    erw [← (g.pull.mapDerivedCategorySingleFunctor 0).hom.naturality_assoc aY]
    rfl
  refine ⟨d, κ, ?_, ?_⟩
  · have h := endpoint (coefficient Y (Rrings l Y)) (coefficient X (Rrings l X))
      (coefficient Y (Arings l E Y)) (coefficient X (Arings l E X))
      d.unitIso.hom eY eX θ₀.iso.hom hα₀
    simpa only [unit, IntegralCoefficientPullback.derivedUnit, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom,
      Category.assoc, heY, heX, CoefficientPullback.derivedIso] using h
  · have hordinary : α.hom.app cY.rootModule ≫ cX.scalar.model.E.map d.rootIso.hom ≫
        𝟙 _ = g.pull.map (𝟙 _) ≫ θ₁.iso.hom := by
      rw [Category.comp_id]
      erw [g.pull.map_id]
      simpa only [Category.id_comp] using hα₁
    have h := endpoint cY.rootModule cX.rootModule (lineModule l E cY)
      (lineModule l E cX) d.rootIso.hom (𝟙 _) (𝟙 _) θ₁.iso.hom hordinary
    have hroot :
        κ.app ((DerivedCategory.singleFunctor (Systems Y (Rrings l Y)) 0).obj
            cY.rootModule) ≫
          cX.scalar.T.map ((d.pull.mapDerivedCategorySingleFunctor 0).hom.app
            cY.rootModule ≫
            (DerivedCategory.singleFunctor (Systems X (Rrings l X)) 0).map
              d.rootIso.hom) ≫ lineComparison l E cX =
        (SpTowerShriek.pull l E b g).map (lineComparison l E cY) ≫
          (θ₁.derivedIso l E).hom := by
      erw [(DerivedCategory.singleFunctor (Systems X (Arings l E X)) 0).map_id,
        (DerivedCategory.singleFunctor (Systems Y (Arings l E Y)) 0).map_id] at h
      erw [Category.comp_id, Category.comp_id] at h
      simp only [SpTowerShriek.S, lineModule,
        LinePullback.derivedIso,
        Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, scalarSingleCounit,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        lineComparison] at h ⊢
      (convert h using 1; rfl)
    have hs := scalar_shift_endpoint cY.scalar.T cX.scalar.T
      d.pull.mapDerivedCategory (SpTowerShriek.pull l E b g) κ
      ((d.pull.mapDerivedCategorySingleFunctor 0).hom.app cY.rootModule ≫
        (DerivedCategory.singleFunctor (Systems X (Rrings l X)) 0).map d.rootIso.hom)
      (lineComparison l E cY) (lineComparison l E cX) (θ₁.derivedIso l E).hom hroot 2
    simp only [D, WeilConjectures.SemilinearSections.D, SpTowerShriek.S,
      IntegralCoefficientPullback.derivedRoot, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom,
      scalarRootTarget, Category.assoc, Functor.map_comp] at hs ⊢
    (convert hs using 1; rfl)

end AlgebraicGeometry.ProEtale.SpTowerClasses
