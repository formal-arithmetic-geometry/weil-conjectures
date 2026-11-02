/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGamma
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.CategoryTheory.Adjunction.ProperOpenTransport

/-!
# Strict reduction comparisons for completed operations

Strict reduction followed by constant-coefficient restriction compares completed-ring
objects with derived strict towers of constant-coefficient modules. This file records its
comparisons with inverse images.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8
(blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived flatConstantModulesAbelian
  SheafOfModules.RingedCoefficientProjection.cachedSheafifyModules
  SheafOfModules.RingedCoefficientProjection.cachedLocalEquivalences

attribute [local instance 100000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- Strict reduction followed by constant-coefficient restriction: the comparison of
completed-ring objects with derived strict towers of constant-coefficient modules.
Source: blueprint step 8 (blueprint: thm-cbc-complete-proetale). -/
def cbcStrictReduction (T : Scheme.{t}) :
    DerivedCategory (proEtaleRingModules T (d.completedRing T)) ⥤
      ProEtale.StrictTower.Derived A T :=
  completedReductionTower T d ⋙ exchangeTowerRes d T

theorem cbcStrictReduction_map {T : Scheme.{t}} {K L : d.derived T} (f : K ⟶ L) :
    (cbcStrictReduction d T).map f =
      (exchangeTowerRes d T).map ((completedReductionTower T d).map f) := rfl

theorem cbcStrictReduction_obj {T : Scheme.{t}} (K : d.derived T) :
    (cbcStrictReduction d T).obj K =
      (exchangeTowerRes d T).obj ((completedReductionTower T d).obj K) := rfl

/-- Strict reduction commutes with inverse image: the normalized reduction/pullback
comparison followed by the restriction/pullback comparison.
Source: blueprint step 8 (blueprint: thm-cbc-complete-proetale). -/
def cbcStrictPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.pull f ⋙ cbcStrictReduction d U ≅
      cbcStrictReduction d V ⋙ ProEtale.StrictTower.G A f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (d.reductionTowerPullbackIso f).symm (exchangeTowerRes d U) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (completedReductionTower V d) (exchangeResPull d f) ≪≫
    (Functor.associator _ _ _).symm

/-- Strict reduction commutes with inverse image compatibly with composition: the
comparison for a composite is the composite of the comparisons, up to the completed and
strict inverse-image compositors.
Source: blueprint step 8; Stacks 0D6D (blueprint: thm-cbc-complete-proetale). -/
theorem cbcStrictPull_comp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : d.derived Z) :
    (cbcStrictReduction d X).map ((d.pullComp f g).hom.app M) ≫
        (cbcStrictPull d f).hom.app ((d.pull g).obj M) ≫
          (ProEtale.StrictTower.G A f).map ((cbcStrictPull d g).hom.app M) =
      (cbcStrictPull d (f ≫ g)).hom.app M ≫
        (ProEtale.StrictTower.gComp A f g).hom.app ((cbcStrictReduction d Z).obj M) := by
  sorry

/-- The comparisons for equal morphisms agree up to the equality transports. -/
theorem cbcStrictPull_eqToHom {X Z : Scheme.{t}} {f₁ f₂ : X ⟶ Z} (e : f₁ = f₂)
    (M : d.derived Z) :
    (cbcStrictReduction d X).map ((eqToHom (congrArg (fun f ↦ d.pull f) e)).app M) ≫
        (cbcStrictPull d f₂).hom.app M =
      (cbcStrictPull d f₁).hom.app M ≫
        (eqToHom (congrArg (ProEtale.StrictTower.G A) e)).app ((cbcStrictReduction d Z).obj M) := by
  subst e
  simp

/-- The comparison for a composite, through an equality of the composite. -/
theorem cbcStrictPull_comp_eq {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) {q : X ⟶ Z}
    (e : f ≫ g = q) (M : d.derived Z) :
    (cbcStrictReduction d X).map ((d.pullComp f g).inv.app M ≫
        (eqToIso (congrArg (fun f ↦ d.pull f) e.symm)).inv.app M) ≫
          (cbcStrictPull d q).hom.app M =
      (cbcStrictPull d f).hom.app ((d.pull g).obj M) ≫
        (ProEtale.StrictTower.G A f).map ((cbcStrictPull d g).hom.app M) ≫
          ((ProEtale.StrictTower.gComp A f g).inv ≫
            (eqToIso (congrArg (ProEtale.StrictTower.G A) e.symm)).inv).app
              ((cbcStrictReduction d Z).obj M) := by
  subst e
  have hc := cbcStrictPull_comp d f g M
  simp only [eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Category.comp_id]
  rw [← cancel_epi ((cbcStrictReduction d X).map ((d.pullComp f g).hom.app M)),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, ← Category.assoc ((cbcStrictPull d f).hom.app _),
    ← Category.assoc ((cbcStrictReduction d X).map _), hc]
  simp

/-- The comparisons are compatible with the inverse-image square of a commutative square.
-/

theorem cbcStrictPull_square {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) (x : d.derived T) :
    (cbcStrictReduction d V).map ((cbcSquarePull d k r p i h).inv.app x) ≫
        (cbcStrictPull d r).hom.app ((d.pull i).obj x) ≫
          (ProEtale.StrictTower.G A r).map ((cbcStrictPull d i).hom.app x) =
      (cbcStrictPull d k).hom.app ((d.pull p).obj x) ≫
        (ProEtale.StrictTower.G A k).map ((cbcStrictPull d p).hom.app x) ≫
          (ProEtale.StrictTower.squareG A k r p i h).inv.app
            ((cbcStrictReduction d T).obj x) := by
  sorry

/-- Strict reduction commutes with direct image: the mate of the inverse-image comparison
is invertible. Its components are the strict projection-formula map and the
restriction/direct-image comparison.
Source: blueprint step 8; Stacks 0D6E (blueprint: thm-cbc-complete-proetale). -/
theorem cbcStrictPush_isIso {X Y : Scheme.{t}} (f : X ⟶ Y) :
    IsIso (mateEquiv (cbcPullPushAdjunction d f) (ProEtale.StrictTower.adj A f)
      (cbcStrictPull d f).inv) := by
  sorry

/-- Strict reduction commutes with extension by zero: the open-extension mate of the
inverse-image comparison is invertible.
Source: blueprint step 8; Stacks 03DI (blueprint: thm-cbc-complete-proetale). -/
theorem cbcStrictOpen_isIso {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (CategoryTheory.ProperOpenTransport.openComparison (cbcDerivedOpenAdjunction d j)
      (ProEtale.StrictTower.jAdj A j) (cbcStrictPull d j)) := by
  sorry

end AlgebraicGeometry.Scheme
