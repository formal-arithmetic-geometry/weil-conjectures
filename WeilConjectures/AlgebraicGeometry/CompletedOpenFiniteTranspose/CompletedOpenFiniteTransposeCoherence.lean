/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerRealizationComparisons
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Sheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearEvaluationDerivedAdjunction
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.AlgebraicGeometry.Constant.ConstantTowerSquareNormalization
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization

/-! # Finite reduction and the strict open transpose

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, finite-exchange paragraph;
Stacks 03DI, 03CY, 03DJ, 06YY and 07A4.
(blueprint: lem-cbc-completed-open-finite-transpose-coherence).

All objects below belong to derived categories of strict towers. The published
section-normalized comparisons are reused, including their quotient transitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
-- Keep localized comparison constructions folded while elaborating their equations.
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryCompIso
  Functor.mapDerivedCategoryNatIso
namespace AlgebraicGeometry.Scheme.CompletedOpenFiniteTranspose

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U T' T : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ T'}
  {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']

/-- The source Q: reduce the open extension, then pull the entire strict tower back.
Source: blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
abbrev source :=
  cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d ⋙
    completedTowerPullback g d

/-- The open object C: strict derived pullback of the reduction tower of K.
Source: blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
abbrev corner := completedReductionTower U d ⋙ completedTowerPullback v d

/-- M is scalar restriction of the strict reduction tower, without completeness.
Source: blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
abbrev restricted := completedReductionTower U d ⋙ exchangeTowerRes d U

/-- H is constant-coefficient inverse image of M.
Source: blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
abbrev openTarget := restricted d (U := U) ⋙ ProEtale.StrictTower.G A v

/-- N is constant-coefficient inverse image of the open extension of M.
Source: blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
abbrev ambientTarget :=
  restricted d (U := U) ⋙ ProEtale.StrictTower.J A j ⋙ ProEtale.StrictTower.G A g

/-- The fixed comparison a uses the normalized pullback transport, scalar comparison,
and quotient/open identification, in that order. No isomorphism is freely chosen.
Source: blueprint finite-exchange paragraph; Stacks 099N and 03DI
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
def sourceComparison (K : d.derived U) :
    (exchangeTowerRes d T').obj ((source d (j := j) (g := g)).obj K) ≅
      (ambientTarget d (j := j) (g := g)).obj K :=
  (exchangeTowerRes d T').mapIso
      ((cbcDatumTowerTransport d g).app
        ((completedReductionTower T d).obj
          ((cbcDerivedOpenShriek d j inferInstance).obj K))) ≪≫
    (exchangeResPull d g).app _ ≪≫
    (ProEtale.StrictTower.G A g).mapIso (cbcRealizationQuotientOpen d j K)

/-- The fixed finite-reduction/scalar comparison d at the open corner.
Source: blueprint finite-exchange paragraph; Stacks 099N
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
def cornerComparison (K : d.derived U) :
    (exchangeTowerRes d U').obj ((corner d (v := v)).obj K) ≅
      (openTarget d (v := v)).obj K :=
  (exchangeTowerRes d U').mapIso
      ((cbcDatumTowerTransport d v).app ((completedReductionTower U d).obj K)) ≪≫
    (exchangeResPull d v).app _

/-- b = J(d)e, with e the published presheaf-identity scalar/open comparison.
Source: Stacks 03DI and 03CY, blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
def extensionComparison (K : d.derived U) :
    (exchangeTowerRes d T').obj
        ((cbcRealizationJ d j').obj ((corner d (v := v)).obj K)) ≅
      (ProEtale.StrictTower.J A j').obj ((openTarget d (v := v)).obj K) :=
  (cbcRealizationTowerScalarOpen d j').app _ ≪≫
    (ProEtale.StrictTower.J A j').mapIso (cornerComparison d (v := v) K)

/-- The transported arrow Psi(x), with the canonical scalar/restriction map c inserted.
Source: blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
def psi (K : d.derived U)
    (x : (corner d (v := v)).obj K ⟶
      (d.towerPull j').obj ((source d (j := j) (g := g)).obj K)) :
    (openTarget d (v := v)).obj K ⟶
      (ProEtale.StrictTower.G A j').obj ((ambientTarget d (j := j) (g := g)).obj K) :=
  (cornerComparison d (v := v) K).inv ≫ (exchangeTowerRes d U').map x ≫
    (exchangeResPull d j').hom.app ((source d (j := j) (g := g)).obj K) ≫
    (ProEtale.StrictTower.G A j').map (sourceComparison d (j := j) (g := g) K).hom

/-- The specified inverse-image square compositor for constant strict towers.
Source: Stacks 07A7; the unit-preserving compositors of strict tower operations
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
def constantSquare (sq : OpenImmersionSquare v j' j g) :
    ProEtale.StrictTower.G A j ⋙ ProEtale.StrictTower.G A v ≅
      ProEtale.StrictTower.G A g ⋙ ProEtale.StrictTower.G A j' :=
  (ProEtale.StrictTower.gComp A v j).symm ≪≫
    eqToIso (congrArg (fun f ↦ ProEtale.StrictTower.G A f) sq.w) ≪≫
    ProEtale.StrictTower.gComp A j' g

/-- The special x is pullback of the completed open unit, followed by the canonical
square compositor and the inverse quotient/open source identification. The actual
K-flat pullback presentations are transported by their universal counits.
Source: Stacks 03DI and 07A7, blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
def unitArrow (sq : OpenImmersionSquare v j' j g) (K : d.derived U) :
    (corner d (v := v)).obj K ⟶
      (d.towerPull j').obj ((source d (j := j) (g := g)).obj K) :=
  (cbcDatumTowerTransport d v).hom.app ((completedReductionTower U d).obj K) ≫
    (d.towerPull v).map
      ((cbcRealizationTowerAdj d j).unit.app ((completedReductionTower U d).obj K)) ≫
    ({ RY := d.completedRing T,
        RX := d.completedRing U,
        RY' := d.completedRing T',
        RX' := d.completedRing U',
        cf := d.integralRingIso j,
        cg := d.integralRingIso g,
        cg' := d.integralRingIso v,
        cf' := d.integralRingIso j',
        coherent := d.integral_coherent sq.toChosenCartesianSquare } :
        StrictTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app
      ((cbcRealizationJ d j).obj ((completedReductionTower U d).obj K)) ≫
    (d.towerPull j').map
      ((d.towerPull g).map (cbcRealizationReduction d j K).inv ≫
        (cbcDatumTowerTransport d g).inv.app
          ((completedReductionTower T d).obj
            ((cbcDerivedOpenShriek d j inferInstance).obj K)))

attribute [local irreducible] constantSquare

private theorem scalarTranspose
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {r : C ⥤ E} {s : D ⥤ F} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L ⋙ s ≅ r ⋙ L') (c : R ⋙ r ≅ s ⋙ R')
    (he : ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)).natTrans = e.inv)
    {X : C} {Y : D} (x : X ⟶ R.obj Y) :
    e.inv.app X ≫ s.map ((a.homEquiv X Y).symm x) =
      L'.map (r.map x ≫ c.hom.app Y) ≫ b.counit.app (s.obj Y) := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp, ← Category.assoc]
  erw [← e.inv.naturality x]
  simp only [Functor.comp_map, Category.assoc]
  have hc := mateEquiv_counit_symm a b (TwoSquare.mk _ _ _ _ c.hom) Y
  change L'.map (c.hom.app Y) ≫ b.counit.app (s.obj Y) =
    (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)).natTrans.app _) ≫
      s.map (a.counit.app Y) at hc
  rw [he] at hc
  rw [← hc, Functor.map_comp, Category.assoc]

private theorem termwiseMate
    {C D E F I : Type*} [Category C] [Category D] [Category E] [Category F]
    [Category I] {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {r : C ⥤ E} {s : D ⥤ F} (a : L ⊣ R) (b : L' ⊣ R')
    (c : R ⋙ r ≅ s ⋙ R') (M : I ⥤ C) (n : I) :
    (((mateEquiv (a.whiskerRight I) (b.whiskerRight I)).symm
      (TwoSquare.mk _ _ _ _
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight I _ _).mapIso c ≪≫
            (Functor.whiskeringRightObjCompIso _ _).symm).hom)).natTrans.app M).app n =
      (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)).natTrans.app (M.obj n)) := by
  simp [mateEquiv, Adjunction.whiskerRight]

private theorem localizedMate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {r : C ⥤ E} {s : D ⥤ F}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (a : L ⊣ R) (b : L' ⊣ R') (e : L ⋙ s ≅ r ⋙ L') (c : R ⋙ r ≅ s ⋙ R')
    (he : ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)).natTrans = e.inv) :
    ((mateEquiv
      (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory)
      (b.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R'.rightDerivedFunctorIsoMapDerivedCategory)).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso c).hom)).natTrans =
      (Functor.mapDerivedCategorySquareIso e).inv := by
  have : IsIso ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)).natTrans := by
    rw [he]
    infer_instance
  have hd := (exact_localization_inverse_mate a b c).2.1
  have hi : asIso ((mateEquiv a b).symm
      (TwoSquare.mk _ _ _ _ c.hom)).natTrans = e.symm := Iso.ext he
  rw [hi] at hd
  rw [ProEtale.SemilinearProperOpen.exact_adjunction_eq a,
    ProEtale.SemilinearProperOpen.exact_adjunction_eq b]
  simpa only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc] using hd

private theorem scalarMate {V W : Scheme.{u}} (i : V ⟶ W) [IsOpenImmersion i] :
    ((mateEquiv (cbcRealizationTowerAdj d i)
      (ProEtale.StrictTower.jAdj A i)).symm
      (TwoSquare.mk _ _ _ _ (exchangeResPull d i).hom)).natTrans =
      (cbcRealizationTowerScalarOpen d i).inv := by
  let a := (cbcRealizationOpenAdj d i).whiskerRight ℕᵒᵖ
  let b := (ProEtale.StrictTower.moduleJAdj A i).whiskerRight ℕᵒᵖ
  let e := Functor.whiskeringRightObjCompIso _ _ ≪≫
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (cbcRealizationScalarOpen d i) ≪≫
    (Functor.whiskeringRightObjCompIso _ _).symm
  have hm : ((mateEquiv a b).symm
      (TwoSquare.mk _ _ _ _ (exchangeModuleResPull d i).hom)).natTrans = e.inv := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    have h := termwiseMate (cbcRealizationOpenAdj d i)
      (ProEtale.StrictTower.moduleJAdj A i) (exchangeOrdinaryResPull d i) M n
    exact h
  have hd := localizedMate a b e (exchangeModuleResPull d i) hm
  simp only [cbcRealizationTowerAdj, ProEtale.StrictTower.jAdj, exchangeResPull,
    cbcRealizationTowerScalarOpen, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, e, a, b, Category.assoc] at hd ⊢
  dsimp only [cbcRealizationJ, cbcRealizationTowerJ, cbcRealizationRes,
    exchangeTowerRes, exchangeTowerModuleRes, exchangeTowerModulePull,
    AdicCoefficientDatum.towerModulePull, AdicCoefficientDatum.towerPull,
    ProEtale.StrictTower.J, ProEtale.StrictTower.towerJ, ProEtale.StrictTower.G,
    ProEtale.StrictTower.towerPullback, exchangeConstantPull, exchangeTowerPull,
    ProEtale.StrictTower.modulePullback, ProEtale.StrictTower.Modules,
    ProEtale.StrictTower.coefficients, ProEtale.StrictTower.constantRingIso,
    exchangeConstantIso, proEtaleConstantComparison, exchangeConstantRing,
    adicLisseConstantRing, exchangeTowers, pbcTowers, ProEtale.StrictTower.Towers,
    pbcModules, proEtaleRingModules, reductionTowerCategory, reductionModuleRing,
    pbcAdicCompletion, pbcTowers_hasDerivedCategory, exchangeTowers_hasDerived,
    ProEtale.StrictTower.towers_hasDerivedCategory, reductionTowerHasDerivedCategory] at hd ⊢
  exact hd

private theorem scalarUnit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {r : C ⥤ E} {s : D ⥤ F} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L ⋙ s ≅ r ⋙ L') (c : R ⋙ r ≅ s ⋙ R')
    (he : ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)).natTrans = e.inv)
    (X : C) :
    r.map (a.unit.app X) ≫ c.hom.app (L.obj X) ≫ R'.map (e.hom.app X) =
      b.unit.app (r.obj X) := by
  have hu := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ c.hom) X
  change r.map (a.unit.app X) ≫ c.hom.app (L.obj X) =
    b.unit.app (r.obj X) ≫ R'.map
      (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)).natTrans.app X) at hu
  rw [he] at hu
  rw [reassoc_of% hu, ← R'.map_comp, Iso.inv_hom_id_app]
  erw [R'.map_id, Category.comp_id]

private theorem sourceTransport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (r : C ⥤ C') (s : D ⥤ D') (P : D ⥤ C) (Q : D' ⥤ C')
    (c : P ⋙ r ≅ s ⋙ Q) {X₀ : C} {Y₀ Y : D} {N : D'}
    (δ : X₀ ≅ P.obj Y₀) (ρ : Y₀ ≅ Y) (ε : s.obj Y ≅ N) :
    r.mapIso (δ ≪≫ P.mapIso ρ) ≪≫ (c.app Y ≪≫ Q.mapIso ε) =
      r.mapIso δ ≪≫ c.app Y₀ ≪≫ Q.mapIso (s.mapIso ρ ≪≫ ε) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Iso.app_hom, Category.assoc]
  have hn := c.hom.naturality ρ.hom
  dsimp only [Functor.comp_map] at hn
  simpa only [Category.assoc] using
    congrArg (fun f ↦ r.map δ.hom ≫ f ≫ Q.map ε.hom) hn

private theorem transportArrow
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (r : C ⥤ C') (s : D ⥤ D') (P : D ⥤ C) (Q : D' ⥤ C')
    (c : P ⋙ r ≅ s ⋙ Q)
    {X₀ X : C} {Y₀ Y : D} {H : C'} {N : D'}
    (δ : X₀ ≅ X) (α : Y₀ ≅ Y) (β : r.obj X ≅ H) (a : s.obj Y ≅ N)
    (x : X ⟶ P.obj Y) :
    (r.mapIso δ ≪≫ β).inv ≫ r.map (δ.hom ≫ x ≫ P.map α.inv) ≫
        c.hom.app Y₀ ≫ Q.map (s.mapIso α ≪≫ a).hom =
      β.inv ≫ r.map x ≫ c.hom.app Y ≫ Q.map a.hom := by
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← r.map_comp_assoc, Iso.inv_hom_id]
  erw [r.map_id, Category.id_comp]
  have hn := c.hom.naturality α.inv
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← Q.map_comp_assoc, ← s.map_comp, Iso.inv_hom_id]
  erw [s.map_id, Q.map_id, Category.id_comp]

private theorem restrictionSquare (sq : OpenImmersionSquare v j' j g)
    (Y : DerivedCategory (exchangeTowers T (d.completedRing T))) :
    (exchangeTowerRes d U').map
        ((d.integralTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app Y) ≫
      (exchangeResPull d j').hom.app ((d.towerPull g).obj Y) ≫
      (ProEtale.StrictTower.G A j').map ((exchangeResPull d g).hom.app Y) =
    (exchangeResPull d v).hom.app ((d.towerPull j).obj Y) ≫
      (ProEtale.StrictTower.G A v).map ((exchangeResPull d j).hom.app Y) ≫
      (exchangeConstantSquare (A := A) sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app
        ((exchangeTowerRes d T).obj Y) := by
  let σ := (d.integralTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare
  let τ := (exchangeConstantSquare (A := A) sq.toChosenCartesianSquare).exchangeTowerSquare
  let l := (ProEtale.StrictTower.G A j').mapIso ((exchangeResPull d g).app Y).symm ≪≫
    ((exchangeResPull d j').app ((d.towerPull g).obj Y)).symm
  let p := (exchangeTowerRes d U').mapIso (σ.app Y)
  let q := (τ.app ((exchangeTowerRes d T).obj Y)) ≪≫
    (ProEtale.StrictTower.G A v).mapIso ((exchangeResPull d j).app Y).symm ≪≫
      ((exchangeResPull d v).app ((d.towerPull j).obj Y)).symm
  have hh := congrArg (fun z ↦ z.app Y) (exchangeResPull_square d sq.toChosenCartesianSquare)
  have h : (l ≪≫ p).hom = q.hom := by
    simp only [l, p, q, σ, τ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
      ] at hh ⊢
    with_unfolding_all exact hh
  have hi := congrArg Iso.inv (Iso.ext h : l ≪≫ p = q)
  simpa only [l, p, q, σ, τ, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc] using hi

attribute [local irreducible] cbcDatumTowerTransport cbcRealizationReduction
  cbcRealizationTowerScalarOpen exchangeResPull

end AlgebraicGeometry.Scheme.CompletedOpenFiniteTranspose
