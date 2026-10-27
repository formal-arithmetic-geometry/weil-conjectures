/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.Paper.LisseCompletedSystemData

/-! # Site comparison for normalized finite free towers -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CompletedLisse
variable (l : ℕ) [Fact l.Prime]

/-- Forget the actions in a continuous-coefficient reduction tower.
Source: BS 6.8.4(1) (blueprint: lem-per-normalized-tower-site-comparison). -/
def towerAbFunctor (P : Base.{u} l) :
    IntegralReductionTower l P.E P.X ⥤
      (ℕᵒᵖ ⥤ Sheaf (ProEt.topology P.X) AddCommGrpCat.{u + 1}) :=
  ObjectProperty.ι _ ⋙
    (Functor.whiskeringRight _ _ _).obj (SheafOfModules.toSheaf
      (integralLisseRing l P.E P.X))

/-- Actual inverse image of the underlying etale diagrams, including their maps.
Source: BS 5.1.5, 6.8.4(1)
(blueprint: lem-per-normalized-tower-site-comparison). -/
def systemAbFunctor (P : Base.{u} l) :
    Systems l P ⥤ (ℕᵒᵖ ⥤ Sheaf (ProEt.topology P.X) AddCommGrpCat.{u + 1}) where
  obj := proEtaleDiagram l P
  map f := Functor.whiskerRight
    (Functor.whiskerRight f.hom.hom
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l P)) AddCommGrpCat)))
        (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} P.X)
  map_id F := by
    apply NatTrans.ext
    funext n
    change (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} P.X).map
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l P)) AddCommGrpCat)).map
        (𝟙 (F.obj.obj.obj n))) = 𝟙 _
    exact ((sheafCompose _
      (forget₂ (ModuleCat.{u + 1} (Integers l P)) AddCommGrpCat) ⋙
        supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} P.X).map_id
          (F.obj.obj.obj n))
  map_comp f g := by
    apply NatTrans.ext
    funext n
    change (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} P.X).map
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l P)) AddCommGrpCat)).map
        (f.hom.hom.app n ≫ g.hom.hom.app n)) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl

/-- The finite-level site comparison retains the actual abelian diagrams and scalar maps.
Source: BS 5.1.5, 6.8.4(1)
(blueprint: lem-per-normalized-tower-site-comparison). -/
structure NormalizedTowerSiteComparison (P : Base.{u} l) where
  equivalence : IntegralReductionTower l P.E P.X ≌ Systems l P
  diagramIso : equivalence.functor ⋙ systemAbFunctor l P ≅ towerAbFunctor l P
  scalar (F : IntegralReductionTower l P.E P.X) (n : ℕ) (a : Integers l P) :
    (SheafOfModules.toSheaf (integralLisseRing l P.E P.X)).map
        (integralLisseScalar l P.E P.X (F.obj.obj (op n)) a) ≫
          (diagramIso.inv.app F).app (op n) =
      (diagramIso.inv.app F).app (op n) ≫
        (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} P.X).map
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l P)) AddCommGrpCat)).map
            (a • 𝟙 ((equivalence.functor.obj F).obj.obj.obj (op n))))

/-- Finite site comparison induces an equivalence on normalized free reduction towers.
Source: Bhatt--Scholze, Corollary 5.1.5 and Proposition 6.8.4(1), pp.35,59
(blueprint: lem-per-normalized-tower-site-comparison).

Proof: identify each continuous finite coefficient ring with the constant quotient ring.
Constant-ring module sheafification identifies its modules with fixed-ring module sheaves.
Apply finiteLocalSystemsTwist to descend each finite locally free level. A constant local
model of the descended object is free precisely when its geometric stalk is free; intersect
its chart with a free chart upstairs and apply the constant-sheaf stalk identification.
Empty charts impose no condition. The comparison inverse image is fully faithful, so
transitions and all their equations descend uniquely. It preserves cokernels; checking
at geometric stalks identifies their quotient condition with the normalization in
IsLisseIntegralDiagram. This constructs the two inverse functors and their unit and counit.
The underlying abelian comparison is the canonical inverse-image comparison, which commutes
with the constant scalar endomorphisms. These comparisons give diagramIso and scalar. -/
theorem normalized_tower_site_comparison (P : Base.{u} l) :
    Nonempty (NormalizedTowerSiteComparison l P) := by sorry

end AlgebraicGeometry.ProEtale.CompletedLisse
