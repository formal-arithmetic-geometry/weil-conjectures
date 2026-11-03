/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGamma
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.CategoryTheory.Adjunction.ProperOpenTransport
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm

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

namespace CategoryTheory


/-- The mate of a horizontally pasted square of isomorphisms is invertible when the mates of
the two pieces are. -/
theorem mateEquiv_isIso_of_paste {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (ρ : G₁ ⋙ L₂ ≅ L₁ ⋙ H₁) (ε : L₂ ⋙ H₂ ≅ G₂ ⋙ L₃)
    [IsIso (mateEquiv adj₁ adj₂ ρ.hom)] [IsIso (mateEquiv adj₂ adj₃ ε.inv)] :
    IsIso (mateEquiv adj₁ adj₃
      ((Functor.associator L₁ H₁ H₂).symm ≪≫ Functor.isoWhiskerRight ρ.symm H₂ ≪≫
        Functor.associator G₁ L₂ H₂ ≪≫
        Functor.isoWhiskerLeft G₁ ε ≪≫ (Functor.associator G₁ G₂ L₃).symm).inv) := by
  have h : ((Functor.associator L₁ H₁ H₂).symm ≪≫ Functor.isoWhiskerRight ρ.symm H₂ ≪≫
        Functor.associator G₁ L₂ H₂ ≪≫
        Functor.isoWhiskerLeft G₁ ε ≪≫ (Functor.associator G₁ G₂ L₃).symm).inv =
      TwoSquare.hComp (TwoSquare.mk _ _ _ _ ρ.hom) (TwoSquare.mk _ _ _ _ ε.inv) := by
    ext X
    simp [TwoSquare.hComp]
  rw [h, mateEquiv_vcomp adj₁ adj₂ adj₃]
  have h1 : IsIso (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ ρ.hom)).natTrans :=
    inferInstanceAs (IsIso (mateEquiv adj₁ adj₂ ρ.hom))
  have h2 : IsIso (mateEquiv adj₂ adj₃ (TwoSquare.mk _ _ _ _ ε.inv)).natTrans :=
    inferInstanceAs (IsIso (mateEquiv adj₂ adj₃ ε.inv))
  have : ∀ X, IsIso ((TwoSquare.vComp (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ ρ.hom))
      (mateEquiv adj₂ adj₃ (TwoSquare.mk _ _ _ _ ε.inv))).natTrans.app X) := by
    intro X
    simp only [TwoSquare.vComp, TwoSquare.natTrans, TwoSquare.mk, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app,
      Category.id_comp, Category.comp_id]
    infer_instance
  exact NatIso.isIso_of_isIso_app _


/-- Morphism algebra deriving the comparison of a square from the comparisons of its two
composites. -/
theorem Functor.map_comp_eq_of_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {c₀ c₁ c₂ : C} {y z e₁ e₂ e₃ : D} {u : c₀ ⟶ c₂} {mh : c₁ ⟶ c₀} {mi : c₀ ⟶ c₁}
    {ah : c₂ ⟶ c₁} {ai : c₁ ⟶ c₂} {s : F.obj c₁ ⟶ e₁} {t₁ : F.obj c₂ ⟶ y} {t₂ : y ⟶ e₂}
    {bh : e₂ ⟶ e₁} {bi : e₁ ⟶ e₂} {w₁ : F.obj c₀ ⟶ z} {w₂ : z ⟶ e₃} {nh : e₁ ⟶ e₃}
    {ni : e₃ ⟶ e₁} {v : e₃ ⟶ e₂}
    (e₁' : u = mi ≫ ai) (e₂' : v = ni ≫ bi) (hm : mi ≫ mh = 𝟙 c₀) (ha : ai ≫ ah = 𝟙 c₁)
    (hb : bh ≫ bi = 𝟙 e₂) (hn : nh ≫ ni = 𝟙 e₁)
    (h₁ : F.map ah ≫ s = t₁ ≫ t₂ ≫ bh) (h₂ : F.map mh ≫ w₁ ≫ w₂ = s ≫ nh) :
    F.map u ≫ t₁ ≫ t₂ = w₁ ≫ w₂ ≫ v := by
  subst e₁' e₂'
  have ht : t₁ ≫ t₂ = F.map ah ≫ s ≫ bi := by
    rw [← Category.assoc, h₁]
    simp [hb]
  have hs : F.map mi ≫ s = w₁ ≫ w₂ ≫ ni := by
    calc F.map mi ≫ s = F.map mi ≫ s ≫ nh ≫ ni := by rw [hn, Category.comp_id]
      _ = F.map mi ≫ F.map mh ≫ w₁ ≫ w₂ ≫ ni := by rw [reassoc_of% h₂]
      _ = w₁ ≫ w₂ ≫ ni := by rw [← F.map_comp_assoc, hm, F.map_id, Category.id_comp]
  rw [ht, F.map_comp, Category.assoc, ← F.map_comp_assoc ai, ha, F.map_id, Category.id_comp,
    ← Category.assoc, hs]
  simp
end CategoryTheory

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

/-- The comparison for a composite, with the compositors packaged as isomorphisms. -/
theorem cbcStrictPull_comp_hom {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) {q : X ⟶ Z}
    (e : f ≫ g = q) (M : d.derived Z) :
    (cbcStrictReduction d X).map (((d.pullComp f g).symm ≪≫
        eqToIso (congrArg (fun f ↦ d.pull f) e)).hom.app M) ≫
          (cbcStrictPull d q).hom.app M =
      (cbcStrictPull d f).hom.app ((d.pull g).obj M) ≫
        (ProEtale.StrictTower.G A f).map ((cbcStrictPull d g).hom.app M) ≫
          ((ProEtale.StrictTower.gComp A f g).symm ≪≫
            eqToIso (congrArg (ProEtale.StrictTower.G A) e)).hom.app
              ((cbcStrictReduction d Z).obj M) := by
  subst e
  have hc := cbcStrictPull_comp_eq d f g rfl M
  simpa using hc

/-- The comparisons are compatible with the inverse-image square of a commutative square. -/
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

/-- The mate of the reduction/pullback comparison is the strict projection-formula map, so it
is invertible. Source: blueprint step 8 (blueprint: thm-cbc-complete-proetale). -/
theorem reductionTowerPullbackIso_mate_isIso {U V : Scheme.{t}} (f : U ⟶ V) :
    IsIso (mateEquiv (cbcPullPushAdjunction d f) (d.towerAdjunction f)
      (d.reductionTowerPullbackIso f).hom) := by
  have h (K : d.derived U) : (mateEquiv (cbcPullPushAdjunction d f) (d.towerAdjunction f)
      (d.reductionTowerPullbackIso f).hom).app K = d.towerProjection f K := by
    rw [AdicCoefficientDatum.towerProjection, Adjunction.homEquiv_unit]
    simp [mateEquiv_apply]
  have (K : d.derived U) : IsIso ((mateEquiv (cbcPullPushAdjunction d f) (d.towerAdjunction f)
      (d.reductionTowerPullbackIso f).hom).app K) := by
    rw [h K]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The mate of the restriction/pullback comparison is the restriction/direct-image
comparison, so it is invertible. Source: blueprint step 8; Stacks 0D6E
(blueprint: thm-cbc-complete-proetale). -/
theorem exchangeResPull_mate_isIso {U V : Scheme.{t}} (f : U ⟶ V) :
    IsIso (mateEquiv (d.towerAdjunction f) (ProEtale.StrictTower.adj A f)
      (exchangeResPull d f).inv) := by
  have hs := (exchangeResPush_existsUnique d f).choose_spec.1
  unfold ExchangeResPushNormalized at hs
  have he := exactDerivedMate_eq (d.towerModuleAdjunction f)
    (exchangeTowerModuleAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A)) (exchangeModuleResPull d f).symm (exchangeModuleResPush d f)
    (exchangeModuleResPull_mate d f) (exchangeResPush d f) hs
  have h : IsIso (exactDerivedMate (d.towerModuleAdjunction f)
    (exchangeTowerModuleAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A)) (exchangeModuleResPull d f).symm) := by
    rw [← he]
    infer_instance
  rw [exactDerivedMate, Functor.mapDerivedCategorySquareIso_symm] at h
  exact h

/-- Strict reduction commutes with direct image: the mate of the inverse-image comparison
is invertible. Its components are the strict projection-formula map and the
restriction/direct-image comparison.
Source: blueprint step 8; Stacks 0D6E (blueprint: thm-cbc-complete-proetale). -/
theorem cbcStrictPush_isIso {X Y : Scheme.{t}} (f : X ⟶ Y) :
    IsIso (mateEquiv (cbcPullPushAdjunction d f) (ProEtale.StrictTower.adj A f)
      (cbcStrictPull d f).inv) := by
  have := reductionTowerPullbackIso_mate_isIso d f
  have := exchangeResPull_mate_isIso d f
  exact mateEquiv_isIso_of_paste (cbcPullPushAdjunction d f) (d.towerAdjunction f)
    (ProEtale.StrictTower.adj A f) (d.reductionTowerPullbackIso f) (exchangeResPull d f)

/-- Strict reduction commutes with extension by zero: the open-extension mate of the
inverse-image comparison is invertible.
Source: blueprint step 8; Stacks 03DI (blueprint: thm-cbc-complete-proetale). -/
theorem cbcStrictOpen_isIso {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (CategoryTheory.ProperOpenTransport.openComparison (cbcDerivedOpenAdjunction d j)
      (ProEtale.StrictTower.jAdj A j) (cbcStrictPull d j)) := by
  sorry

end AlgebraicGeometry.Scheme
