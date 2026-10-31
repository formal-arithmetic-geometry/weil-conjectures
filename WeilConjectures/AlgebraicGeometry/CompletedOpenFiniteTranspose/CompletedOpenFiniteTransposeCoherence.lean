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
public import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.ProperBaseChange.ConstantCompletionEquivalence
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

private theorem constantSquare_normalization (sq : OpenImmersionSquare v j' j g)
    (M : ProEtale.StrictTower.Derived A T) :
    (exchangeConstantSquare (A := A) sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app M =
      (constantSquare (A := A) sq).hom.app M := by
  have h := exchangeConstantTowerSquare_inv A v j' j g sq.toChosenCartesianSquare
    (constantSquare (A := A) sq) (by unfold constantSquare; rfl)
  exact congrArg (fun η ↦ η.app M) h

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


private theorem transportTranspose
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {r : C ⥤ E} {s : D ⥤ F} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L ⋙ s ≅ r ⋙ L') (c : R ⋙ r ≅ s ⋙ R')
    (he : ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)).natTrans = e.inv)
    {X : C} {Y : D} {H : E} {N : F}
    (β : r.obj X ≅ H) (α : s.obj Y ≅ N) (x : X ⟶ R.obj Y) :
    (e.app X ≪≫ L'.mapIso β).inv ≫ s.map ((a.homEquiv X Y).symm x) ≫ α.hom =
      L'.map (β.inv ≫ r.map x ≫ c.hom.app Y ≫ R'.map α.hom) ≫ b.counit.app N := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
  rw [reassoc_of% scalarTranspose a b e c he x]
  have hn := b.counit.naturality α.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← hn]
  simp only [Functor.map_comp, Category.assoc]

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

private theorem transportArrowCompared
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (r : C ⥤ C') (s : D ⥤ D') (P : D ⥤ C) (Q : D' ⥤ C')
    (c : P ⋙ r ≅ s ⋙ Q)
    {X₀ X : C} {Y₀ Y : D} {H : C'} {N : D'}
    (δ : X₀ ≅ X) (α : Y₀ ≅ Y) (β : r.obj X ≅ H) (a : s.obj Y ≅ N)
    (x : X ⟶ P.obj Y) (β₀ : r.obj X₀ ≅ H) (a₀ : s.obj Y₀ ≅ N)
    (x₀ : X₀ ⟶ P.obj Y₀) (hβ : β₀ = r.mapIso δ ≪≫ β)
    (ha : s.mapIso α ≪≫ a = a₀) (hx : x₀ = δ.hom ≫ x ≫ P.map α.inv) :
    β₀.inv ≫ r.map x₀ ≫ c.hom.app Y₀ ≫ Q.map a₀.hom =
      β.inv ≫ r.map x ≫ c.hom.app Y ≫ Q.map a.hom := by
  rw [hβ, ← ha, hx]
  exact transportArrow r s P Q c δ α β a x

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

private theorem normalizedRestrictionSquare (sq : OpenImmersionSquare v j' j g)
    (κ : ProEtale.StrictTower.G A j ⋙ ProEtale.StrictTower.G A v ≅
      ProEtale.StrictTower.G A g ⋙ ProEtale.StrictTower.G A j')
    (normalization : ∀ M : ProEtale.StrictTower.Derived A T,
      (exchangeConstantSquare (A := A) sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app M =
        κ.hom.app M)
    (Z : DerivedCategory (exchangeTowers T (d.completedRing T))) :
    (exchangeTowerRes d U').map
        ((d.integralTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app Z) ≫
      (exchangeResPull d j').hom.app ((d.towerPull g).obj Z) ≫
      (ProEtale.StrictTower.G A j').map ((exchangeResPull d g).hom.app Z) =
    (exchangeResPull d v).hom.app ((d.towerPull j).obj Z) ≫
      (ProEtale.StrictTower.G A v).map ((exchangeResPull d j).hom.app Z) ≫
      κ.hom.app ((exchangeTowerRes d T).obj Z) := by
  exact (restrictionSquare d sq Z).trans (congrArg (fun z ↦
    (exchangeResPull d v).hom.app ((d.towerPull j).obj Z) ≫
      (ProEtale.StrictTower.G A v).map ((exchangeResPull d j).hom.app Z) ≫ z)
    (normalization ((exchangeTowerRes d T).obj Z)))

-- Keep the compositor as a parameter while checking naturality, so the kernel
-- does not expand the derived localization hidden in its construction.
private theorem scalarSquareUnit (sq : OpenImmersionSquare v j' j g)
    (κ : ProEtale.StrictTower.G A j ⋙ ProEtale.StrictTower.G A v ≅
      ProEtale.StrictTower.G A g ⋙ ProEtale.StrictTower.G A j')
    (hc : ∀ Z : DerivedCategory (exchangeTowers T (d.completedRing T)),
      (exchangeTowerRes d U').map
          ((d.integralTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app Z) ≫
        (exchangeResPull d j').hom.app ((d.towerPull g).obj Z) ≫
        (ProEtale.StrictTower.G A j').map ((exchangeResPull d g).hom.app Z) =
      (exchangeResPull d v).hom.app ((d.towerPull j).obj Z) ≫
        (ProEtale.StrictTower.G A v).map ((exchangeResPull d j).hom.app Z) ≫
        κ.hom.app ((exchangeTowerRes d T).obj Z))
    (X : DerivedCategory (exchangeTowers U (d.completedRing U))) :
    (exchangeResPull d v).inv.app X ≫
      (exchangeTowerRes d U').map
        ((d.towerPull v).map ((cbcRealizationTowerAdj d j).unit.app X) ≫
          (d.integralTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app
            ((cbcRealizationJ d j).obj X)) ≫
      (exchangeResPull d j').hom.app ((d.towerPull g).obj ((cbcRealizationJ d j).obj X)) ≫
      (ProEtale.StrictTower.G A j').map
        ((exchangeResPull d g).hom.app ((cbcRealizationJ d j).obj X) ≫
          (ProEtale.StrictTower.G A g).map ((cbcRealizationTowerScalarOpen d j).hom.app X)) =
      (ProEtale.StrictTower.G A v).map
          ((ProEtale.StrictTower.jAdj A j).unit.app ((exchangeTowerRes d U).obj X)) ≫
        κ.hom.app
          ((ProEtale.StrictTower.J A j).obj ((exchangeTowerRes d U).obj X)) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc ((cbcRealizationJ d j).obj X)]
  have hn := (exchangeResPull d v).hom.naturality
    ((cbcRealizationTowerAdj d j).unit.app X)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, Iso.inv_hom_id_app_assoc]
  have hk := κ.hom.naturality
    ((cbcRealizationTowerScalarOpen d j).hom.app X)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hk
  rw [← hk]
  have hu := scalarUnit (cbcRealizationTowerAdj d j) (ProEtale.StrictTower.jAdj A j)
    (cbcRealizationTowerScalarOpen d j) (exchangeResPull d j) (scalarMate d j) X
  have hh := congrArg (fun z ↦ (ProEtale.StrictTower.G A v).map z ≫
    κ.hom.app
      ((ProEtale.StrictTower.J A j).obj ((exchangeTowerRes d U).obj X))) hu
  simp only [Functor.map_comp, Category.assoc] at hh
  dsimp only [exchangeConstantPull, exchangeTowerPull, exchangeTowerModulePull,
    ProEtale.StrictTower.G, ProEtale.StrictTower.towerPullback,
    ProEtale.StrictTower.modulePullback, ProEtale.StrictTower.Modules,
    ProEtale.StrictTower.coefficients, ProEtale.StrictTower.constantRingIso,
    exchangeConstantIso, proEtaleConstantComparison, exchangeConstantRing,
    adicLisseConstantRing, exchangeTowers, pbcTowers, ProEtale.StrictTower.Towers,
    pbcModules, proEtaleRingModules, reductionTowerCategory, reductionModuleRing,
    pbcAdicCompletion, pbcTowers_hasDerivedCategory, exchangeTowers_hasDerived,
    ProEtale.StrictTower.towers_hasDerivedCategory, reductionTowerHasDerivedCategory] at hh ⊢
  exact hh


private theorem scalarSquareUnitFixed (sq : OpenImmersionSquare v j' j g)
    (normalization : ∀ M : ProEtale.StrictTower.Derived A T,
      (exchangeConstantSquare (A := A) sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app M =
        (constantSquare (A := A) sq).hom.app M)
    (X : DerivedCategory (exchangeTowers U (d.completedRing U))) :
    ((exchangeResPull d v).inv.app X ≫
      (exchangeTowerRes d U').map
        ((d.towerPull v).map ((cbcRealizationTowerAdj d j).unit.app X) ≫
          (d.integralTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app
            ((cbcRealizationJ d j).obj X)) ≫
      (exchangeResPull d j').hom.app ((d.towerPull g).obj ((cbcRealizationJ d j).obj X)) ≫
      (ProEtale.StrictTower.G A j').map
        (((exchangeResPull d g).app ((cbcRealizationJ d j).obj X) ≪≫
          (ProEtale.StrictTower.G A g).mapIso
            ((cbcRealizationTowerScalarOpen d j).app X)).hom) :
      (ProEtale.StrictTower.G A v).obj ((exchangeTowerRes d U).obj X) ⟶
        (ProEtale.StrictTower.G A j').obj
          ((ProEtale.StrictTower.G A g).obj
            ((ProEtale.StrictTower.J A j).obj ((exchangeTowerRes d U).obj X)))) =
      (ProEtale.StrictTower.G A v).map
          ((ProEtale.StrictTower.jAdj A j).unit.app ((exchangeTowerRes d U).obj X)) ≫
        (constantSquare (A := A) sq).hom.app
          ((ProEtale.StrictTower.J A j).obj ((exchangeTowerRes d U).obj X)) := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using
    scalarSquareUnit d sq (constantSquare (A := A) sq)
    (normalizedRestrictionSquare d sq (constantSquare (A := A) sq) normalization) X

private theorem scalarSquareUnitAt (sq : OpenImmersionSquare v j' j g)
    (normalization : ∀ M : ProEtale.StrictTower.Derived A T,
      (exchangeConstantSquare (A := A) sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app M =
        (constantSquare (A := A) sq).hom.app M)
    (X : DerivedCategory (exchangeTowers U (d.completedRing U)))
    (M : ProEtale.StrictTower.Derived A U) (hM : (exchangeTowerRes d U).obj X = M) :
    eqToHom (congrArg (ProEtale.StrictTower.G A v).obj hM.symm) ≫
      ((exchangeResPull d v).inv.app X ≫
      (exchangeTowerRes d U').map
        ((d.towerPull v).map ((cbcRealizationTowerAdj d j).unit.app X) ≫
          (d.integralTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app
            ((cbcRealizationJ d j).obj X)) ≫
      (exchangeResPull d j').hom.app ((d.towerPull g).obj ((cbcRealizationJ d j).obj X)) ≫
      (ProEtale.StrictTower.G A j').map
        (((exchangeResPull d g).app ((cbcRealizationJ d j).obj X) ≪≫
          (ProEtale.StrictTower.G A g).mapIso
            ((cbcRealizationTowerScalarOpen d j).app X)).hom) :
      (ProEtale.StrictTower.G A v).obj ((exchangeTowerRes d U).obj X) ⟶
        (ProEtale.StrictTower.G A j').obj
          ((ProEtale.StrictTower.G A g).obj
            ((ProEtale.StrictTower.J A j).obj ((exchangeTowerRes d U).obj X)))) ≫
        eqToHom (congrArg (ProEtale.StrictTower.J A j ⋙ ProEtale.StrictTower.G A g ⋙
          ProEtale.StrictTower.G A j').obj hM) =
      (ProEtale.StrictTower.G A v).map
          ((ProEtale.StrictTower.jAdj A j).unit.app M) ≫
        (constantSquare (A := A) sq).hom.app
          ((ProEtale.StrictTower.J A j).obj M) := by
  cases hM
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact scalarSquareUnitFixed d sq normalization X

private theorem transportedNaturality
    {C D E D' E' : Type*} [Category C] [Category D] [Category E]
    [Category D'] [Category E']
    (F : C ⥤ D) (H : C ⥤ E) (r : D ⥤ D') (s : E ⥤ E')
    (P : D ⥤ E) (Q : D' ⥤ E') (F' : C ⥤ D') (H' : C ⥤ E')
    (a : F ⋙ r ≅ F') (b : H ⋙ s ≅ H') (c : P ⋙ s ≅ r ⋙ Q)
    {K L : C} (f : K ⟶ L) (x : H.obj K ⟶ P.obj (F.obj K))
    (y : H.obj L ⟶ P.obj (F.obj L))
    (h : H.map f ≫ y = x ≫ P.map (F.map f)) :
    H'.map f ≫ (b.inv.app L ≫ s.map y ≫ c.hom.app (F.obj L) ≫ Q.map (a.hom.app L)) =
    (b.inv.app K ≫ s.map x ≫ c.hom.app (F.obj K) ≫ Q.map (a.hom.app K)) ≫
      Q.map (F'.map f) := by
  rw [← Category.assoc, b.inv.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← s.map_comp_assoc, h, s.map_comp, Category.assoc]
  have hc := c.hom.naturality (F.map f)
  dsimp only [Functor.comp_map] at hc
  have ha := a.hom.naturality f
  dsimp only [Functor.comp_map] at ha
  rw [reassoc_of% hc, ← Q.map_comp, ha, Q.map_comp]

private def reductionOpenNatIso :
    completedReductionTower U d ⋙ cbcRealizationJ d j ≅
      cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d :=
  NatIso.ofComponents (fun K ↦ (cbcRealizationReduction d j K).symm)
    (fun f ↦ (cbcRealizationReductionInv_properties d j).2 _ _ f)

attribute [local irreducible] cbcDatumTowerTransport cbcRealizationReduction
  cbcRealizationTowerScalarOpen exchangeResPull

private def quotientOpenNatIso :
    cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d ⋙
        exchangeTowerRes d T ≅ restricted d (U := U) ⋙ ProEtale.StrictTower.J A j :=
  Functor.isoWhiskerRight (reductionOpenNatIso d (j := j)).symm (exchangeTowerRes d T) ≪≫
    Functor.isoWhiskerLeft (completedReductionTower U d) (cbcRealizationTowerScalarOpen d j)

private def sourceNatIso :
    source d (j := j) (g := g) ⋙ exchangeTowerRes d T' ≅
      ambientTarget d (j := j) (g := g) :=
  Functor.isoWhiskerLeft (cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d)
      (Functor.isoWhiskerRight (cbcDatumTowerTransport d g) (exchangeTowerRes d T')) ≪≫
    Functor.isoWhiskerLeft
      (cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d)
      (exchangeResPull d g) ≪≫
    Functor.isoWhiskerRight (quotientOpenNatIso d (j := j)) (ProEtale.StrictTower.G A g)

private def cornerNatIso :
    corner d (v := v) ⋙ exchangeTowerRes d U' ≅ openTarget d (v := v) :=
  Functor.isoWhiskerLeft (completedReductionTower U d)
      (Functor.isoWhiskerRight (cbcDatumTowerTransport d v) (exchangeTowerRes d U')) ≪≫
    Functor.isoWhiskerLeft (completedReductionTower U d) (exchangeResPull d v)

private def unitNatTrans (sq : OpenImmersionSquare v j' j g) :
    corner d (v := v) ⟶ source d (j := j) (g := g) ⋙ d.towerPull j' :=
  Functor.whiskerLeft (completedReductionTower U d) (cbcDatumTowerTransport d v).hom ≫
    Functor.whiskerLeft (completedReductionTower U d)
      (Functor.whiskerRight (cbcRealizationTowerAdj d j).unit (d.towerPull v)) ≫
    Functor.whiskerLeft (completedReductionTower U d)
      (Functor.whiskerLeft (cbcRealizationJ d j)
        ({ RY := d.completedRing T,
           RX := d.completedRing U,
           RY' := d.completedRing T',
           RX' := d.completedRing U',
           cf := d.integralRingIso j,
           cg := d.integralRingIso g,
           cg' := d.integralRingIso v,
           cf' := d.integralRingIso j',
           coherent := d.integral_coherent sq.toChosenCartesianSquare } :
          StrictTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare.inv) ≫
    Functor.whiskerRight
      (Functor.whiskerRight (reductionOpenNatIso d (j := j)).hom (d.towerPull g))
      (d.towerPull j') ≫
    Functor.whiskerLeft
      (cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d)
      (Functor.whiskerRight (cbcDatumTowerTransport d g).inv (d.towerPull j'))


/-- Finite reduction preserves the two specified open transposes, including the
normalization on pullback of the open unit. These are whole strict-tower equalities.
Source: Stacks 03DI, 03CY, 03DJ, 06YY and 07A4; blueprint main-20261015,
lem-cbc-completed-extension-zero-comparison.proof.md, finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence).

Proof: the ordinary scalar/open comparison is its defining inverse mate. Whiskering
this equation over the tower and exact localization preserve it, with the specified
units and counits. Naturality of the scalar/open comparison and of the constant
counit then gives the first identity after conjugation by the fixed source and
corner comparisons.

For the second identity, cancel the actual/datum pullback transports and the
quotient/open comparison by naturality. The remaining arrow is the scalar image
of the pulled-back open unit followed by the integral square compositor. The
scalar-restriction square rewrites this as the scalar image of the open unit
followed by the constant square compositor. Naturality moves that compositor
past the scalar/open comparison; the mate equation identifies the remaining
scalar image of the unit with the constant unit. The proved normalization of
the constant ringed square identifies its inverse component with constantSquare.
All operations take place on whole strict towers, so their transition maps and
derived arrows are already retained; no new flat replacement is needed. -/
theorem completedOpenFiniteTransposeCoherence
    (sq : OpenImmersionSquare v j' j g) (K : d.derived U) :
    (∀ x : (corner d (v := v)).obj K ⟶
        (d.towerPull j').obj ((source d (j := j) (g := g)).obj K),
      (extensionComparison d (j' := j') (v := v) K).inv ≫
          (exchangeTowerRes d T').map
            (((cbcRealizationTowerAdj d j').homEquiv _ _).symm x) ≫
          (sourceComparison d (j := j) (g := g) K).hom =
        (ProEtale.StrictTower.J A j').map (psi d (j := j) (g := g) K x) ≫
          (ProEtale.StrictTower.jAdj A j').counit.app
            ((ambientTarget d (j := j) (g := g)).obj K)) ∧
    psi d (j := j) (g := g) K (unitArrow d sq K) =
      (ProEtale.StrictTower.G A v).map
          ((ProEtale.StrictTower.jAdj A j).unit.app ((restricted d (U := U)).obj K)) ≫
        (constantSquare (A := A) sq).hom.app
          ((ProEtale.StrictTower.J A j).obj ((restricted d (U := U)).obj K)) := by
  constructor
  · intro x
    exact transportTranspose (cbcRealizationTowerAdj d j')
      (ProEtale.StrictTower.jAdj A j') (cbcRealizationTowerScalarOpen d j')
      (exchangeResPull d j') (scalarMate d j')
      (cornerComparison d (v := v) K) (sourceComparison d (j := j) (g := g) K) x
  · let X : DerivedCategory (exchangeTowers U (d.completedRing U)) :=
      (completedReductionTower U d).obj K
    let Y := (cbcRealizationJ d j).obj X
    let σ := (d.integralTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare
    let α : (source d (j := j) (g := g)).obj K ≅ (d.towerPull g).obj Y :=
      (cbcDatumTowerTransport d g).app
        ((completedReductionTower T d).obj ((cbcDerivedOpenShriek d j inferInstance).obj K)) ≪≫
      (d.towerPull g).mapIso (cbcRealizationReduction d j K)
    let a : (exchangeTowerRes d T').obj ((d.towerPull g).obj Y) ≅
        (ProEtale.StrictTower.G A g).obj
          ((ProEtale.StrictTower.J A j).obj ((exchangeTowerRes d U).obj X)) :=
      (exchangeResPull d g).app Y ≪≫
      (ProEtale.StrictTower.G A g).mapIso ((cbcRealizationTowerScalarOpen d j).app X)
    have ha : (exchangeTowerRes d T').mapIso α ≪≫ a =
        sourceComparison d (j := j) (g := g) K := by
      exact sourceTransport (exchangeTowerRes d T') (exchangeTowerRes d T)
        (d.towerPull g) (ProEtale.StrictTower.G A g) (exchangeResPull d g)
        ((cbcDatumTowerTransport d g).app
          ((completedReductionTower T d).obj ((cbcDerivedOpenShriek d j inferInstance).obj K)))
        (cbcRealizationReduction d j K) ((cbcRealizationTowerScalarOpen d j).app X)
    have hunit : unitArrow d sq K =
        ((cbcDatumTowerTransport d v).app X).hom ≫
          ((d.towerPull v).map ((cbcRealizationTowerAdj d j).unit.app X) ≫
            σ.inv.app Y) ≫ (d.towerPull j').map α.inv := by
      simp only [unitArrow, α, X, Y, σ, AdicCoefficientDatum.integralTowerRingedSquare,
        Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom,
        Functor.map_comp, Category.assoc]
    have hpsi : psi d (j := j) (g := g) K (unitArrow d sq K) =
        ((exchangeResPull d v).inv.app X ≫
          (exchangeTowerRes d U').map
            ((d.towerPull v).map ((cbcRealizationTowerAdj d j).unit.app X) ≫ σ.inv.app Y) ≫
          (exchangeResPull d j').hom.app ((d.towerPull g).obj Y) ≫
          (ProEtale.StrictTower.G A j').map a.hom :
            (ProEtale.StrictTower.G A v).obj ((restricted d (U := U)).obj K) ⟶
              (ProEtale.StrictTower.G A j').obj
                ((ambientTarget d (j := j) (g := g)).obj K)) := by
      exact transportArrowCompared (exchangeTowerRes d U') (exchangeTowerRes d T')
        (d.towerPull j') (ProEtale.StrictTower.G A j') (exchangeResPull d j')
        ((cbcDatumTowerTransport d v).app X) α ((exchangeResPull d v).app X) a
        ((d.towerPull v).map ((cbcRealizationTowerAdj d j).unit.app X) ≫ σ.inv.app Y)
        (cornerComparison d (v := v) K) (sourceComparison d (j := j) (g := g) K)
        (unitArrow d sq K) rfl ha hunit
    have h0 := scalarSquareUnitAt d sq (constantSquare_normalization sq) X
      ((restricted d (U := U)).obj K) rfl
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h0
    exact hpsi.trans h0


/-- Naturality in K and in an arbitrary derived arrow x. The hypothesis is exactly
commutativity of the input arrow square, allowing roofs in the derived category.
The second identity is naturality of the specified pulled-back open unit.
Source: Stacks 03DI and 06XN, blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence).
Proof: every constituent of sourceComparison, cornerComparison and psi is a
component of the specified natural scalar, quotient/open or pullback comparison.
Move f past these components and apply functoriality; the assumed input square
then gives the first identity. Naturality of the open unit, the inverse-image
square compositor and the quotient/open comparison gives the second identity.
These are the naturality assertions of Step 7, after strict derived descent. -/
theorem completedOpenFiniteTransposeCoherence_naturality
    (sq : OpenImmersionSquare v j' j g) (K L : d.derived U) (f : K ⟶ L)
    (x : (corner d (v := v)).obj K ⟶
      (d.towerPull j').obj ((source d (j := j) (g := g)).obj K))
    (y : (corner d (v := v)).obj L ⟶
      (d.towerPull j').obj ((source d (j := j) (g := g)).obj L))
    (hxy : (corner d (v := v)).map f ≫ y =
      x ≫ (d.towerPull j').map ((source d (j := j) (g := g)).map f)) :
    (openTarget d (v := v)).map f ≫ psi d (j := j) (g := g) L y =
      psi d (j := j) (g := g) K x ≫
        (ProEtale.StrictTower.G A j').map
          ((ambientTarget d (j := j) (g := g)).map f) ∧
    (corner d (v := v)).map f ≫ unitArrow d sq L =
      unitArrow d sq K ≫ (d.towerPull j').map ((source d (j := j) (g := g)).map f) := by
  constructor
  · exact transportedNaturality
      (source d (j := j) (g := g)) (corner d (v := v))
      (exchangeTowerRes d T') (exchangeTowerRes d U')
      (d.towerPull j') (ProEtale.StrictTower.G A j')
      (ambientTarget d (j := j) (g := g)) (openTarget d (v := v))
      (sourceNatIso d (j := j) (g := g)) (cornerNatIso d (v := v))
      (exchangeResPull d j') f x y hxy
  · simpa only [unitNatTrans, unitArrow, reductionOpenNatIso,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatIso.ofComponents_hom_app, NatIso.ofComponents, Iso.symm_hom,
      Functor.comp_obj, Functor.comp_map,
      Functor.map_comp,
      Category.assoc] using (unitNatTrans d sq).naturality f

/-- The scalar/open comparison before complexes or derived localization: the
identity of the underlying sheafified extension presheaves at every strict index.
Source: Stacks 03DI and 03CY
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
def strictScalarOpen {V W : Scheme.{u}} (i : V ⟶ W) [IsOpenImmersion i] :
    cbcRealizationTowerJ d i ⋙ exchangeTowerModuleRes d W ≅
      exchangeTowerModuleRes d V ⋙ ProEtale.StrictTower.towerJ A i :=
  Functor.whiskeringRightObjCompIso _ _ ≪≫
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (cbcRealizationScalarOpen d i) ≪≫
    (Functor.whiskeringRightObjCompIso _ _).symm

/-- The scalar transpose equation on simultaneous strict diagram representatives.
Here x is one chain map of strict towers, so equality includes its differentials
and every quotient transition. Exact derived descent of this equation is the
first identity of completedOpenFiniteTransposeCoherence after conjugating by a,d.
Source: Stacks 03DI, 03CY and 03DJ, node proof Steps 1, 2, 6 and 7
(blueprint: lem-cbc-completed-open-finite-transpose-coherence).
Proof: the extension presheaf counit evaluates a summand in the ambient module.
Scalar restriction changes neither this evaluation nor the summand inclusion unit.
Thus the ordinary counit equation holds on each summand; sheafification extends
it uniquely. Apply naturality of the presheaf-identity comparison at x. Whiskering
with the entire strict index category and then with the cochain shape gives the
displayed equation at once, including all transition and differential equations.
ExactDerivedTransformationPasting localizes this equation with the original
units and counits; conjugation by the fixed a,d gives the derived identity. -/
theorem completedOpenFiniteTransposeCoherence_strict
    (C : CochainComplex (d.towers U') ℤ) (Q : CochainComplex (d.towers T') ℤ)
    (x : C ⟶ ((d.towerModulePull j').mapHomologicalComplex (.up ℤ)).obj Q) :
    (NatIso.mapHomologicalComplex (strictScalarOpen d j') (.up ℤ)).inv.app C ≫
        ((exchangeTowerModuleRes d T').mapHomologicalComplex (.up ℤ)).map
          (((((cbcRealizationOpenAdj d j').whiskerRight ℕᵒᵖ).mapHomologicalComplex
            (.up ℤ)).homEquiv C Q).symm x) =
      ((ProEtale.StrictTower.towerJ A j').mapHomologicalComplex (.up ℤ)).map
          (((exchangeTowerModuleRes d U').mapHomologicalComplex (.up ℤ)).map x ≫
            (NatIso.mapHomologicalComplex (exchangeModuleResPull d j') (.up ℤ)).hom.app Q) ≫
        (((ProEtale.StrictTower.moduleJAdj A j').whiskerRight ℕᵒᵖ).mapHomologicalComplex
          (.up ℤ)).counit.app
            (((exchangeTowerModuleRes d T').mapHomologicalComplex (.up ℤ)).obj Q) := by
  rw [Adjunction.homEquiv_counit]
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext n
  change (cbcRealizationScalarOpen d j').inv.app ((C.X q).obj n) ≫
      (cbcRealizationRes d T').map
        ((cbcOpenShriek d j' inferInstance).map ((x.f q).app n) ≫
          (cbcRealizationOpenAdj d j').counit.app ((Q.X q).obj n)) = _
  change _ = (ProEtale.StrictTower.moduleJ A j').map
      ((cbcRealizationRes d U').map ((x.f q).app n) ≫
        (exchangeOrdinaryResPull d j').hom.app ((Q.X q).obj n)) ≫
      (ProEtale.StrictTower.moduleJAdj A j').counit.app
        ((cbcRealizationRes d T').obj ((Q.X q).obj n))
  simpa only [Adjunction.homEquiv_counit] using
    scalarTranspose (cbcRealizationOpenAdj d j') (ProEtale.StrictTower.moduleJAdj A j')
    (cbcRealizationScalarOpen d j') (exchangeOrdinaryResPull d j') rfl ((x.f q).app n)

end AlgebraicGeometry.Scheme.CompletedOpenFiniteTranspose
