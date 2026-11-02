/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarAdjunctions
import WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenClopenProjector

/-! # Scalar restriction and proper/open coherence

Source: Stacks Project, Modules on Sites, Tags 03CZ, 03D7 and 03DI
(blueprint: lem-sf-semilinear-scalar-proper-open). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections

attribute [-instance] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
  (B : Type (u + 1)) [CommRing B] (ψ : ∀ n : ℕ, CommRingCat.of B ⟶ R n)

/-- The intrinsic ordinary projector is an actual composite of natural transformations.
Source: Stacks 03DI and 0F7B
(blueprint: lem-sf-semilinear-scalar-proper-open). -/
def scalarOrdinaryPi
    (κ : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s],
      StrictTower.towerJ B s ≅ StrictTower.towerDirectImage B s)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (StrictTower.Towers B X) ⟶
      StrictTower.towerPullback B s ⋙ StrictTower.towerJ B s :=
  (scalarTowerAdj B s).unit ≫
    Functor.whiskerLeft (StrictTower.towerPullback B s) (κ s).inv

/-- The intrinsic proper/open arrows and their compatibility with scalar restriction.
Source: Stacks 03D8, 03DI and 0F7B
(blueprint: lem-sf-semilinear-scalar-proper-open). -/
structure OrdinaryScalarProperOpen (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) where
  /-- The constant-tower cartesian open comparison, fixed by its transpose below. -/
  beta : ∀ {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (_h : gU ≫ j = j' ≫ g) (_hsq : IsPullback gU j' j g),
    StrictTower.towerJ B j ⋙ StrictTower.towerPullback B g ≅
      StrictTower.towerPullback B gU ⋙ StrictTower.towerJ B j'
  /-- The inverse beta is exactly the open-unit transpose. -/
  beta_unit : ∀ {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) (M : StrictTower.Towers B U),
    ((scalarTowerOpenAdj B j').homEquiv _ _)
        ((beta gU j' j g h hsq).inv.app M) =
      (StrictTower.towerPullback B gU).map ((scalarTowerOpenAdj B j).unit.app M) ≫
        (scalarTowerSquare B gU j' j g h).inv.app ((StrictTower.towerJ B j).obj M)
  /-- Restriction preserves that canonical beta, before deriving or evaluation. -/
  beta_comparison : ∀ {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) (M : Modules R φ U),
    (C.rho X').map ((moduleBeta R φ gU j' j g h hsq).hom.app M) ≫
        (G.a j').hom.app ((pull R φ gU).obj M) ≫
        (StrictTower.towerJ B j').map ((G.b gU).hom.app M) =
      (G.b g).hom.app ((extension R φ j).obj M) ≫
        (StrictTower.towerPullback B g).map ((G.a j).hom.app M) ≫
        (beta gU j' j g h hsq).hom.app ((C.rho U).obj M)
  /-- The clopen extension/direct comparison, normalized by the inverse open unit. -/
  clopen : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s],
    StrictTower.towerJ B s ≅ StrictTower.towerDirectImage B s
  /-- This equation specifies the canonical open-to-direct map, rather than an arbitrary iso. -/
  clopen_unit : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
      [IsClosedImmersion s] (N : StrictTower.Towers B U),
    (scalarTowerOpenAdj B s).unit.app N ≫
        ((scalarTowerAdj B s).homEquiv _ _).symm ((clopen s).hom.app N) = 𝟙 N
  /-- Preservation of the actual ordinary clopen projector. -/
  pi_comparison : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
      [IsClosedImmersion s] (M : Modules R φ X),
    (C.rho X).map ((modulePi R φ s).app M) ≫
        (G.a s).hom.app ((pull R φ s).obj M) ≫
        (StrictTower.towerJ B s).map ((G.b s).hom.app M) =
      (scalarOrdinaryPi B clopen s).app ((C.rho X).obj M)
  /-- The constant ordinary alpha, specified by its full clopen word below. -/
  alpha : ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T)
    (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k]
    [QuasiCompact i] [IsProper r] [IsProper p] (_h : k ≫ p = r ≫ i),
    StrictTower.towerJ B i ⋙ StrictTower.towerPullback B p ⟶
      StrictTower.towerPullback B r ⋙ StrictTower.towerJ B k
  /-- Alpha is beta, then the clopen projector, then the canonical compositors. -/
  alpha_eq : ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T)
    (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k]
    [QuasiCompact i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : StrictTower.Towers B S),
    (alpha k r p i h).app M =
      (beta (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm
        (IsPullback.of_hasPullback p i).flip).hom.app M ≫
      (StrictTower.towerJ B (pullback.fst p i)).map
        ((scalarOrdinaryPi B clopen (StrictTower.squareLift k r p i h)).app
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (scalarTowerOpenComp B (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom.app
        ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).obj
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom.app
        ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).obj
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (StrictTower.towerJ B k).map
        ((StrictTower.towerGComp B (StrictTower.squareLift k r p i h)
          (pullback.snd p i)).inv.app M ≫
          (eqToIso (congrArg (StrictTower.towerPullback B) (pullback.lift_snd k r h))).hom.app M)
  /-- Preservation of the intrinsic ordinary alpha for every proper/open square. -/
  alpha_comparison : ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Modules R φ S),
    (C.rho W).map ((moduleAlpha R φ k r p i h).app M) ≫
        (G.a k).hom.app ((pull R φ r).obj M) ≫
        (StrictTower.towerJ B k).map ((G.b r).hom.app M) =
      (G.b p).hom.app ((extension R φ i).obj M) ≫
        (StrictTower.towerPullback B p).map ((G.a i).hom.app M) ≫
        (alpha k r p i h).app ((C.rho S).obj M)

section Comparison

variable {A₀ A₁ A₂ D₀ D₁ D₂ : Type*} [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* D₀] [Category* D₁] [Category* D₂]
  {L₀₁ : A₀ ⥤ A₁} {L₁₂ : A₁ ⥤ A₂} {L₀₂ : A₀ ⥤ A₂}
  {R₁₀ : A₁ ⥤ A₀} {R₂₁ : A₂ ⥤ A₁} {R₂₀ : A₂ ⥤ A₀}
  {L₀₁' : D₀ ⥤ D₁} {L₁₂' : D₁ ⥤ D₂} {L₀₂' : D₀ ⥤ D₂}
  {R₁₀' : D₁ ⥤ D₀} {R₂₁' : D₂ ⥤ D₁} {R₂₀' : D₂ ⥤ D₀}

/-- The left composite comparison is unit-normalized against the right comparison.
Source: Stacks 0D6D (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem leftAdjointCompIso_unit
    (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₀₂ : L₀₂ ⊣ R₂₀)
    (e : R₂₁ ⋙ R₁₀ ≅ R₂₀) (X : A₀) :
    adj₀₂.unit.app X ≫ e.inv.app (L₀₂.obj X) =
      adj₀₁.unit.app X ≫ R₁₀.map (adj₁₂.unit.app (L₀₁.obj X)) ≫
        R₁₀.map (R₂₁.map ((Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).hom.app X)) := by
  have h := unit_conjugateEquiv_symm adj₀₂ (adj₀₁.comp adj₁₂) e.inv X
  rw [h, Adjunction.leftAdjointCompIso_hom]
  simp [Adjunction.leftAdjointCompNatTrans]

/-- Compatible comparisons of three adjunctions carry a unit-normalized left composite
to a unit-normalized left composite.
Source: Stacks 0D6D (blueprint: lem-sf-semilinear-scalar-proper-open).
Proof: transpose under the composite adjunction and use the three unit equations. -/
private theorem leftComposite_comparison
    (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₀₂ : L₀₂ ⊣ R₂₀)
    (adj₀₁' : L₀₁' ⊣ R₁₀') (adj₁₂' : L₁₂' ⊣ R₂₁') (adj₀₂' : L₀₂' ⊣ R₂₀')
    (ρ₀ : A₀ ⥤ D₀) (ρ₁ : A₁ ⥤ D₁) (ρ₂ : A₂ ⥤ D₂)
    (l₀₁ : L₀₁ ⋙ ρ₁ ≅ ρ₀ ⋙ L₀₁') (l₁₂ : L₁₂ ⋙ ρ₂ ≅ ρ₁ ⋙ L₁₂')
    (l₀₂ : L₀₂ ⋙ ρ₂ ⟶ ρ₀ ⋙ L₀₂')
    (r₁₀ : R₁₀ ⋙ ρ₀ ⟶ ρ₁ ⋙ R₁₀') (r₂₁ : R₂₁ ⋙ ρ₁ ⟶ ρ₂ ⋙ R₂₁')
    (r₂₀ : R₂₀ ⋙ ρ₀ ⟶ ρ₂ ⋙ R₂₀')
    (h₀₁ : ∀ X, ρ₀.map (adj₀₁.unit.app X) ≫ r₁₀.app (L₀₁.obj X) ≫
      R₁₀'.map (l₀₁.hom.app X) = adj₀₁'.unit.app (ρ₀.obj X))
    (h₁₂ : ∀ Y, ρ₁.map (adj₁₂.unit.app Y) ≫ r₂₁.app (L₁₂.obj Y) ≫
      R₂₁'.map (l₁₂.hom.app Y) = adj₁₂'.unit.app (ρ₁.obj Y))
    (h₀₂ : ∀ X, ρ₀.map (adj₀₂.unit.app X) ≫ r₂₀.app (L₀₂.obj X) ≫
      R₂₀'.map (l₀₂.app X) = adj₀₂'.unit.app (ρ₀.obj X))
    (e : R₂₁ ⋙ R₁₀ ≅ R₂₀) (e' : R₂₁' ⋙ R₁₀' ≅ R₂₀')
    (he : ∀ Z, ρ₀.map (e.hom.app Z) ≫ r₂₀.app Z =
      r₁₀.app (R₂₁.obj Z) ≫ R₁₀'.map (r₂₁.app Z) ≫ e'.hom.app (ρ₂.obj Z))
    (c : L₀₁ ⋙ L₁₂ ⟶ L₀₂)
    (hc : ∀ X, adj₀₂.unit.app X ≫ e.inv.app (L₀₂.obj X) =
      adj₀₁.unit.app X ≫ R₁₀.map (adj₁₂.unit.app (L₀₁.obj X)) ≫
        R₁₀.map (R₂₁.map (c.app X)))
    (c' : L₀₁' ⋙ L₁₂' ⟶ L₀₂')
    (hc' : ∀ X, adj₀₂'.unit.app X ≫ e'.inv.app (L₀₂'.obj X) =
      adj₀₁'.unit.app X ≫ R₁₀'.map (adj₁₂'.unit.app (L₀₁'.obj X)) ≫
        R₁₀'.map (R₂₁'.map (c'.app X)))
    (X : A₀) :
    ρ₂.map (c.app X) ≫ l₀₂.app X =
      l₁₂.hom.app (L₀₁.obj X) ≫ L₁₂'.map (l₀₁.hom.app X) ≫ c'.app (ρ₀.obj X) := by
  have key : L₁₂'.map (l₀₁.inv.app X) ≫ l₁₂.inv.app (L₀₁.obj X) ≫ ρ₂.map (c.app X) ≫
      l₀₂.app X = c'.app (ρ₀.obj X) := by
    apply ((adj₀₁'.comp adj₁₂').homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map,
      Functor.map_comp, Category.assoc]
    rw [← hc', ← h₀₂, ← h₀₁]
    have s1 : R₁₀'.map (l₀₁.hom.app X) ≫
        R₁₀'.map (adj₁₂'.unit.app (L₀₁'.obj (ρ₀.obj X))) ≫
        R₁₀'.map (R₂₁'.map (L₁₂'.map (l₀₁.inv.app X))) =
        R₁₀'.map (adj₁₂'.unit.app (ρ₁.obj (L₀₁.obj X))) := by
      have n1 := adj₁₂'.unit.naturality (l₀₁.inv.app X)
      simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at n1
      simp only [← Functor.map_comp, ← n1, Iso.hom_inv_id_app_assoc]
    have s2 : R₁₀'.map (adj₁₂'.unit.app (ρ₁.obj (L₀₁.obj X))) ≫
        R₁₀'.map (R₂₁'.map (l₁₂.inv.app (L₀₁.obj X))) =
        R₁₀'.map (ρ₁.map (adj₁₂.unit.app (L₀₁.obj X))) ≫
          R₁₀'.map (r₂₁.app (L₁₂.obj (L₀₁.obj X))) := by
      rw [← h₁₂]
      simp only [Functor.map_comp, Category.assoc]
      rw [← R₁₀'.map_comp (R₂₁'.map _), ← R₂₁'.map_comp]
      simp
    have s3 := r₁₀.naturality (adj₁₂.unit.app (L₀₁.obj X))
    have s4 := r₂₁.naturality (c.app X)
    have s5 := r₁₀.naturality (R₂₁.map (c.app X))
    have s6 := e'.inv.naturality (l₀₂.app X)
    have s7 : ρ₀.map (e.inv.app (L₀₂.obj X)) ≫ r₁₀.app (R₂₁.obj (L₀₂.obj X)) ≫
        R₁₀'.map (r₂₁.app (L₀₂.obj X)) =
        r₂₀.app (L₀₂.obj X) ≫ e'.inv.app (ρ₂.obj (L₀₂.obj X)) := by
      rw [← cancel_epi (ρ₀.map (e.hom.app (L₀₂.obj X))), ← Functor.map_comp_assoc,
        Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% (he _)]
      simp
    have h5 : ρ₀.map (adj₀₂.unit.app X) ≫ ρ₀.map (e.inv.app (L₀₂.obj X)) =
        ρ₀.map (adj₀₁.unit.app X) ≫ ρ₀.map (R₁₀.map (adj₁₂.unit.app (L₀₁.obj X))) ≫
          ρ₀.map (R₁₀.map (R₂₁.map (c.app X))) := by
      simpa only [Functor.map_comp, Category.assoc] using congrArg ρ₀.map (hc X)
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at s3 s4 s5 s6 s7
    simp only [Category.assoc]
    rw [reassoc_of% s1, reassoc_of% s2, ← reassoc_of% s3]
    have s4' := congrArg R₁₀'.map s4
    simp only [Functor.map_comp] at s4'
    rw [← reassoc_of% s4', ← reassoc_of% s5]
    rw [← reassoc_of% h5, reassoc_of% s7, s6]
  rw [← key]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp

end Comparison

/-- The termwise section-normalized direct-image compositor on strict towers.
Source: Stacks 0D6D (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private def towerRComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    StrictTower.towerDirectImage B f ⋙ StrictTower.towerDirectImage B g ≅
      StrictTower.towerDirectImage B (f ≫ g) :=
  Functor.whiskeringRightObjCompIso _ _ ≪≫
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (StrictTower.moduleRComp B f g)

/-- The tower pullback compositor is unit-normalized against `towerRComp`.
Source: Stacks 0D6D (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem towerGComp_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (T : StrictTower.Towers B Z) :
    (scalarTowerAdj B (f ≫ g)).unit.app T ≫
        (towerRComp B f g).inv.app ((StrictTower.towerPullback B (f ≫ g)).obj T) =
      (scalarTowerAdj B g).unit.app T ≫
        (StrictTower.towerDirectImage B g).map
          ((scalarTowerAdj B f).unit.app ((StrictTower.towerPullback B g).obj T)) ≫
        (StrictTower.towerDirectImage B g).map ((StrictTower.towerDirectImage B f).map
          ((StrictTower.towerGComp B f g).inv.app T)) := by
  apply NatTrans.ext
  funext n
  have h := leftAdjointCompIso_unit
    (Scheme.proEtaleRingModuleAdjunction g (StrictTower.coefficients B Z)
      (StrictTower.coefficients B Y) (StrictTower.constantRingIso B g))
    (Scheme.proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
      (StrictTower.coefficients B X) (StrictTower.constantRingIso B f))
    (Scheme.proEtaleRingModuleAdjunction (f ≫ g) (StrictTower.coefficients B Z)
      (StrictTower.coefficients B X) (StrictTower.constantRingIso B (f ≫ g)))
    (StrictTower.moduleRComp B f g) (T.obj n)
  simp [scalarTowerAdj, towerRComp, StrictTower.towerGComp, StrictTower.moduleGComp]
  exact h

/-- Scalar restriction is the original section map at every level.
Source: Stacks 03CZ (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem rho_map_heq (C : OrdinaryScalarRestriction R φ B ψ) {X : Scheme.{u}}
    {M M' : Modules R φ X} (q : M ⟶ M') (n : ℕ) (H : X.ProEtᵒᵖ)
    (x : (((C.rho X).obj M).obj (op n)).val.obj H) (y : M.val.obj (op (n, H.unop)))
    (hxy : HEq x y) :
    HEq ((((C.rho X).map q).app (op n)).val.app H x) (q.val.app (op (n, H.unop)) y) := by
  have h := congrArg (fun t ↦ t.val.app H x) ((C.level X n).hom.naturality q)
  simp only [Functor.comp_map, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at h
  have h1 := C.level_sections X n M' H ((((C.rho X).map q).app (op n)).val.app H x)
  have h3 : ((C.level X n).hom.app M).val.app H x = y :=
    eq_of_heq ((C.level_sections X n M H x).trans hxy)
  subst h3
  exact h1.symm.trans (heq_of_eq h)

/-- Restriction maps of scalar restriction are the original restriction maps.
Source: Stacks 03CZ (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem rho_restrict_heq (C : OrdinaryScalarRestriction R φ B ψ) {X : Scheme.{u}}
    (M : Modules R φ X) (n : ℕ) {V V' : X.ProEt} (ρ : V ⟶ V')
    (z : (((C.rho X).obj M).obj (op n)).val.obj (op V')) (w : M.val.obj (op (n, V')))
    (hzw : HEq z w) :
    HEq ((((C.rho X).obj M).obj (op n)).val.map ρ.op z)
      (M.val.map (Prod.mkHom (𝟙 n) ρ).op w) := by
  have h := PresheafOfModules.naturality_apply ((C.level X n).hom.app M).val ρ.op z
  have h1 := C.level_sections X n M (op V) ((((C.rho X).obj M).obj (op n)).val.map ρ.op z)
  have h3 : ((C.level X n).hom.app M).val.app (op V') z = w :=
    eq_of_heq ((C.level_sections X n M (op V') z).trans hzw)
  subst h3
  exact h1.symm.trans (heq_of_eq h)

/-- Restriction carries the section-normalized system direct-image compositor to the
section-normalized tower compositor.
Source: Stacks 0D6D (blueprint: lem-sf-semilinear-scalar-proper-open).
Proof: all comparison maps are the identity on sections, and both compositors restrict
along the same fibre-product pasting isomorphism. -/
private theorem d_pComp (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Modules R φ X) :
    (C.rho Z).map ((modulePComp R φ f g).hom.app K) ≫ (G.d (f ≫ g)).hom.app K =
      (G.d g).hom.app ((push R φ f).obj K) ≫
        (StrictTower.towerDirectImage B g).map ((G.d f).hom.app K) ≫
        (towerRComp B f g).hom.app ((C.rho X).obj K) := by
  apply NatTrans.ext
  funext n
  induction n with | op n => ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro H
  induction H with | op H => ?_
  ext x
  simp only [NatTrans.comp_app, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  apply eq_of_heq
  have hx := C.level_sections Z n ((push R φ g).obj ((push R φ f).obj K)) (op H) x
  have hl := (G.d_sections (f ≫ g) K n (op H) _).trans
    (rho_map_heq R φ B ψ C ((modulePComp R φ f g).hom.app K) n (op H) x _ hx.symm)
  have hp : ((modulePComp R φ f g).hom.app K).val.app (op (n, H))
      (((C.level Z n).hom.app ((push R φ g).obj ((push R φ f).obj K))).val.app (op H) x) =
      K.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackComp f g).hom.app H)).op
        (((C.level Z n).hom.app ((push R φ g).obj ((push R φ f).obj K))).val.app (op H) x) := by
    unfold modulePComp
    exact (modulePComp_existsUnique R φ f g).choose_spec.1 K n H _
  rw [hp] at hl
  refine hl.trans ?_
  have ht : ((towerRComp B f g).hom.app ((C.rho X).obj K)).app (op n) =
      (StrictTower.moduleRComp B f g).hom.app (((C.rho X).obj K).obj (op n)) := by
    simp [towerRComp]
  rw [ht]
  have hr := (Classical.choose_spec (StrictTower.moduleRComp_existsUnique B f g)).1
    (((C.rho X).obj K).obj (op n)) H
  refine HEq.trans ?_ (heq_of_eq (hr _).symm)
  have hm := (G.d_sections f K n (op ((Scheme.proEtaleBaseChange g).obj H)) _).trans
    ((G.d_sections g ((push R φ f).obj K) n (op H) x).trans hx.symm)
  exact (rho_restrict_heq R φ B ψ C K n _ _ _ hm).symm

/-- Restriction preserves the unit-normalized inverse-image compositor.
Source: Stacks 0D6D (blueprint: lem-sf-semilinear-scalar-proper-open).
Proof: the inverse-image compositors are the left-adjoint comparisons of the
section-normalized direct-image compositors, which restriction preserves. -/
private theorem b_gComp (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules R φ Z) :
    (C.rho X).map ((moduleGComp R φ f g).inv.app M) ≫ (G.b (f ≫ g)).hom.app M =
      (G.b f).hom.app ((pull R φ g).obj M) ≫
        (StrictTower.towerPullback B f).map ((G.b g).hom.app M) ≫
        (StrictTower.towerGComp B f g).inv.app ((C.rho Z).obj M) :=
  leftComposite_comparison (moduleAdj R φ g) (moduleAdj R φ f) (moduleAdj R φ (f ≫ g))
    (scalarTowerAdj B g) (scalarTowerAdj B f) (scalarTowerAdj B (f ≫ g))
    (C.rho Z) (C.rho Y) (C.rho X) (G.b g) (G.b f) (G.b (f ≫ g)).hom
    (G.d g).hom (G.d f).hom (G.d (f ≫ g)).hom
    (OrdinaryScalarAdjunctions.unit R φ B ψ C G g)
    (OrdinaryScalarAdjunctions.unit R φ B ψ C G f)
    (OrdinaryScalarAdjunctions.unit R φ B ψ C G (f ≫ g))
    (modulePComp R φ f g) (towerRComp B f g) (d_pComp R φ B ψ C G f g)
    (moduleGComp R φ f g).inv (fun X ↦ leftAdjointCompIso_unit _ _ _ _ X)
    (StrictTower.towerGComp B f g).inv (towerGComp_unit B f g) M

/-- Restriction preserves the unit-normalized open-extension compositor.
Source: Stacks 03DI and 0F7D (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem a_jComp (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (N : Modules R φ U) :
    (C.rho X).map ((moduleJComp R φ i j).hom.app N) ≫ (G.a (i ≫ j)).hom.app N =
      (G.a j).hom.app ((extension R φ i).obj N) ≫
        (StrictTower.towerJ B j).map ((G.a i).hom.app N) ≫
        (scalarTowerOpenComp B i j).hom.app ((C.rho U).obj N) :=
  leftComposite_comparison (moduleJAdj R φ i) (moduleJAdj R φ j) (moduleJAdj R φ (i ≫ j))
    (scalarTowerOpenAdj B i) (scalarTowerOpenAdj B j) (scalarTowerOpenAdj B (i ≫ j))
    (C.rho U) (C.rho V) (C.rho X) (G.a i) (G.a j) (G.a (i ≫ j)).hom
    (G.b i).hom (G.b j).hom (G.b (i ≫ j)).hom
    (G.open_unit i) (G.open_unit j) (G.open_unit (i ≫ j))
    (moduleGComp R φ i j).symm (StrictTower.towerGComp B i j).symm
    (fun Z ↦ b_gComp R φ B ψ C G i j Z)
    (moduleJComp R φ i j).hom (fun X ↦ leftAdjointCompIso_unit _ _ _ _ X)
    (scalarTowerOpenComp B i j).hom (fun X ↦ leftAdjointCompIso_unit _ _ _ _ X) N

/-- The inverse-image comparison respects equality transport of scheme maps.
Source: Stacks 03D7 (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem b_congr (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    (h : f = f') (M : Modules R φ Y) :
    (C.rho X).map ((eqToIso (congrArg (pull R φ) h)).hom.app M) ≫ (G.b f').hom.app M =
      (G.b f).hom.app M ≫
        (eqToIso (congrArg (StrictTower.towerPullback B) h)).hom.app ((C.rho Y).obj M) := by
  subst h
  simp

/-- The open-extension comparison respects equality transport of open immersions.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem a_congr (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {U X : Scheme.{u}} {f f' : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion f'] (h : f = f') (N : Modules R φ U) :
    (C.rho X).map ((moduleJCongr R φ h).hom.app N) ≫ (G.a f').hom.app N =
      (G.a f).hom.app N ≫ (eqToIso (scalarTowerOpen_congr B h)).hom.app ((C.rho U).obj N) := by
  subst h
  simp [moduleJCongr]

/-- The forward form of `b_gComp`.
Source: Stacks 0D6D (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem b_gComp_hom (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules R φ Z) :
    (C.rho X).map ((moduleGComp R φ f g).hom.app M) ≫
        (G.b f).hom.app ((pull R φ g).obj M) ≫
        (StrictTower.towerPullback B f).map ((G.b g).hom.app M) =
      (G.b (f ≫ g)).hom.app M ≫
        (StrictTower.towerGComp B f g).hom.app ((C.rho Z).obj M) := by
  have h := b_gComp R φ B ψ C G f g M
  calc _ = (C.rho X).map ((moduleGComp R φ f g).hom.app M) ≫
        ((G.b f).hom.app ((pull R φ g).obj M) ≫
          (StrictTower.towerPullback B f).map ((G.b g).hom.app M) ≫
          (StrictTower.towerGComp B f g).inv.app ((C.rho Z).obj M)) ≫
        (StrictTower.towerGComp B f g).hom.app ((C.rho Z).obj M) := by
        simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    _ = _ := by
        rw [← h, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
          CategoryTheory.Functor.map_id, Category.id_comp]

/-- The square comparison of systems as a composite.
Source: Stacks 07A7 (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem moduleSquareG_hom_app {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i)
    (M : Modules R φ T) :
    (moduleSquareG R φ k r p i h).hom.app M =
      (moduleGComp R φ r i).inv.app M ≫
        (eqToIso (congrArg (pull R φ) h.symm)).hom.app M ≫
        (moduleGComp R φ k p).hom.app M := by
  rw [moduleSquareG_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]

/-- The square comparison of towers as a composite.
Source: Stacks 07A7 (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem scalarTowerSquare_hom_app {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i)
    (M : StrictTower.Towers B T) :
    (scalarTowerSquare B k r p i h).hom.app M =
      (StrictTower.towerGComp B r i).inv.app M ≫
        (eqToIso (congrArg (StrictTower.towerPullback B) h.symm)).hom.app M ≫
        (StrictTower.towerGComp B k p).hom.app M := by
  have e : (scalarTowerSquare B k r p i h).hom = (StrictTower.towerGComp B r i).inv ≫
      (eqToIso (congrArg (StrictTower.towerPullback B) h.symm)).hom ≫
        (StrictTower.towerGComp B k p).hom := rfl
  refine (congrArg (fun τ ↦ τ.app M) e).trans ?_
  simp only [NatTrans.comp_app]

/-- Restriction preserves the canonical pullback-square comparison.
Source: Stacks 07A7 (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem b_square (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i)
    (M : Modules R φ T) :
    (C.rho V).map ((moduleSquareG R φ k r p i h).hom.app M) ≫
        (G.b k).hom.app ((pull R φ p).obj M) ≫
        (StrictTower.towerPullback B k).map ((G.b p).hom.app M) =
      (G.b r).hom.app ((pull R φ i).obj M) ≫
        (StrictTower.towerPullback B r).map ((G.b i).hom.app M) ≫
        (scalarTowerSquare B k r p i h).hom.app ((C.rho T).obj M) := by
  rw [moduleSquareG_hom_app, scalarTowerSquare_hom_app, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, b_gComp_hom R φ B ψ C G k p M,
    reassoc_of% (b_congr R φ B ψ C G h.symm M), reassoc_of% (b_gComp R φ B ψ C G r i M)]

private theorem whiskeringRight_mapIso_eqToIso {X Y : Scheme.{u}} {f f' : X ⟶ Y} (e : f = f') :
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
        (eqToIso (congrArg (StrictTower.modulePullback B) e)) =
      eqToIso (congrArg (StrictTower.towerPullback B) e) := by
  subst e
  simp

private theorem scalarTowerSquare_eq_mapIso {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    scalarTowerSquare B k r p i h =
      Functor.whiskeringRightObjCompIso (StrictTower.modulePullback B i)
          (StrictTower.modulePullback B r) ≪≫
        (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (StrictTower.moduleSquareG B k r p i h) ≪≫
        (Functor.whiskeringRightObjCompIso (StrictTower.modulePullback B p)
          (StrictTower.modulePullback B k)).symm := by
  rw [StrictTower.moduleSquareG_eq, Functor.mapIso_trans, Functor.mapIso_trans,
    Functor.mapIso_symm, whiskeringRight_mapIso_eqToIso B h.symm]
  simp only [scalarTowerSquare, StrictTower.towerGComp, Iso.trans_symm, Iso.trans_assoc]
  rfl

private theorem towerBeta_unit {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) (M : StrictTower.Towers B U) :
    ((scalarTowerOpenAdj B j').homEquiv ((StrictTower.towerPullback B gU).obj M)
        ((StrictTower.towerPullback B g).obj ((StrictTower.towerJ B j).obj M)))
        ((StrictTower.openBetaTower B gU j' j g h hsq).inv.app M) =
      (StrictTower.towerPullback B gU).map ((scalarTowerOpenAdj B j).unit.app M) ≫
        (scalarTowerSquare B gU j' j g h).inv.app ((StrictTower.towerJ B j).obj M) := by
  rw [scalarTowerSquare_eq_mapIso]
  apply NatTrans.ext
  funext n
  have h1 := (StrictTower.openBetaModule_normalized B gU j' j g h hsq).2 (M.obj n)
  rw [Adjunction.homEquiv_unit] at h1 ⊢
  exact h1

/-- The clopen open-to-direct comparison, termwise on strict towers.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private def towerClopen {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
    [IsClosedImmersion s] : StrictTower.towerJ B s ≅ StrictTower.towerDirectImage B s :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
    (@asIso _ _ _ _ (StrictTower.clopenModuleToDirect B s)
      (StrictTower.clopenModuleToDirect_isIso B s))

/-- Components of the tower clopen comparison.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem towerClopen_hom_app_app {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
    [IsClosedImmersion s] (N : StrictTower.Towers B U) (n : ℕᵒᵖ) :
    ((towerClopen B s).hom.app N).app n = (StrictTower.clopenModuleToDirect B s).app (N.obj n) :=
  rfl

/-- The tower clopen comparison is normalized by the inverse open unit.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem towerClopen_unit {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
    [IsClosedImmersion s] (N : StrictTower.Towers B U) :
    (scalarTowerOpenAdj B s).unit.app N ≫
      ((scalarTowerAdj B s).homEquiv _ _).symm ((towerClopen B s).hom.app N) = 𝟙 N := by
  have := StrictTower.clopenModule_openUnit_isIso B s
  apply NatTrans.ext
  funext n
  have hm : ((StrictTower.clopenModuleAdj B s).homEquiv _ _).symm
      ((StrictTower.clopenModuleToDirect B s).app (N.obj n)) =
      inv ((StrictTower.moduleJAdj B s).unit.app (N.obj n)) := by
    rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit]
    simp [StrictTower.clopenModuleToDirect]
  rw [Adjunction.homEquiv_counit] at hm ⊢
  rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.id_app]
  simp only [scalarTowerOpenAdj, scalarTowerAdj, Adjunction.whiskerRight_unit_app_app,
    Adjunction.whiskerRight_counit_app_app, Functor.whiskeringRight_obj_map,
    Functor.whiskerRight_app]
  rw [towerClopen_hom_app_app, hm]
  exact IsIso.hom_inv_id _

/-- Restriction carries the system open-to-direct map to the tower clopen comparison.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-scalar-proper-open).
Proof: transpose under the direct-image adjunction; both transposes invert the
restricted open unit. -/
private theorem toP_comparison (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (N : Modules R φ U) :
    (G.a s).hom.app N ≫ (towerClopen B s).hom.app ((C.rho U).obj N) =
      (C.rho X).map ((moduleOpenToP R φ s).app N) ≫ (G.d s).hom.app N := by
  have := moduleJAdj_unit_isIso R φ s
  have hP : (moduleOpenToP R φ s).app N = (moduleAdj R φ s).unit.app ((extension R φ s).obj N) ≫
      (push R φ s).map (inv ((moduleJAdj R φ s).unit.app N)) := by
    simp [moduleOpenToP, NatIso.isIso_inv_app]
  have hd := (G.d s).hom.naturality (inv ((moduleJAdj R φ s).unit.app N))
  have hu := OrdinaryScalarAdjunctions.unit R φ B ψ C G s ((extension R φ s).obj N)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hd hu ⊢
  have hr0 : (C.rho X).map ((moduleOpenToP R φ s).app N) ≫ (G.d s).hom.app N =
      (scalarTowerAdj B s).homEquiv ((C.rho X).obj ((extension R φ s).obj N)) ((C.rho U).obj N)
        ((G.b s).inv.app ((extension R φ s).obj N) ≫
          (C.rho U).map (inv ((moduleJAdj R φ s).unit.app N))) := by
    rw [Adjunction.homEquiv_unit, hP, Functor.map_comp, Category.assoc, hd, ← hu,
      Category.assoc, Category.assoc, ← Functor.map_comp (StrictTower.towerDirectImage B s),
      Iso.hom_inv_id_app_assoc]
  apply ((scalarTowerAdj B s).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, hr0, Equiv.symm_apply_apply,
    ← cancel_epi ((C.rho U).map ((moduleJAdj R φ s).unit.app N) ≫
      (G.b s).hom.app ((extension R φ s).obj N))]
  have ho := G.open_unit s N
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at ho
  simp only [Category.assoc]
  rw [reassoc_of% ho, towerClopen_unit, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  rfl

/-- Restriction preserves the intrinsic clopen projector.
Source: Stacks 03DI and 0F7B (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem towerPi_comparison (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (M : Modules R φ X) :
    (C.rho X).map ((modulePi R φ s).app M) ≫
        (G.a s).hom.app ((pull R φ s).obj M) ≫
        (StrictTower.towerJ B s).map ((G.b s).hom.app M) =
      (scalarOrdinaryPi B (fun s ↦ towerClopen B s) s).app ((C.rho X).obj M) := by
  have := moduleOpenToP_isIso R φ s
  have ht := toP_comparison R φ B ψ C G s ((pull R φ s).obj M)
  have ht' : (C.rho X).map (inv ((moduleOpenToP R φ s).app ((pull R φ s).obj M))) ≫
      (G.a s).hom.app ((pull R φ s).obj M) =
      (G.d s).hom.app ((pull R φ s).obj M) ≫
        (towerClopen B s).inv.app ((C.rho U).obj ((pull R φ s).obj M)) := by
    rw [← cancel_epi ((C.rho X).map ((moduleOpenToP R φ s).app ((pull R φ s).obj M))),
      ← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, ← reassoc_of% ht, Iso.hom_inv_id_app, Category.comp_id]
  have hn := (towerClopen B s).inv.naturality ((G.b s).hom.app M)
  have hu := OrdinaryScalarAdjunctions.unit R φ B ψ C G s M
  have hpi : (modulePi R φ s).app M = (moduleAdj R φ s).unit.app M ≫
      inv ((moduleOpenToP R φ s).app ((pull R φ s).obj M)) := by
    simp [modulePi, NatIso.isIso_inv_app]
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hn hu ht' ⊢
  rw [hpi, Functor.map_comp, Category.assoc, reassoc_of% ht', ← hn, reassoc_of% hu]
  rfl

/-- The inverse system beta has the specified open-unit transpose.
Source: Stacks 09AE (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem moduleBeta_inv_unit {U' U X' X : Scheme.{u}} (gU : U' ⟶ U)
    (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) (M : Modules R φ U) :
    (moduleJAdj R φ j').unit.app ((pull R φ gU).obj M) ≫
      (pull R φ j').map ((moduleBeta R φ gU j' j g h hsq).inv.app M) =
      (pull R φ gU).map ((moduleJAdj R φ j).unit.app M) ≫
        (moduleSquareG R φ gU j' j g h).inv.app ((extension R φ j).obj M) := by
  have e := ((moduleJAdj R φ j').homEquiv _ _).apply_symm_apply
    ((pull R φ gU).map ((moduleJAdj R φ j).unit.app M) ≫
      (moduleSquareG R φ gU j' j g h).inv.app ((extension R φ j).obj M))
  rw [Adjunction.homEquiv_unit] at e
  exact e

/-- The inverse form of the square compatibility of the inverse-image comparison.
Source: Stacks 07A7 (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem b_square_inv (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {U' U X' X : Scheme.{u}} (gU : U' ⟶ U)
    (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X) (h : gU ≫ j = j' ≫ g) (E : Modules R φ X) :
    (G.b gU).inv.app ((pull R φ j).obj E) ≫
      (C.rho U').map ((moduleSquareG R φ gU j' j g h).inv.app E) ≫
      (G.b j').hom.app ((pull R φ g).obj E) =
      (StrictTower.towerPullback B gU).map ((G.b j).hom.app E) ≫
        (scalarTowerSquare B gU j' j g h).inv.app ((C.rho X).obj E) ≫
        (StrictTower.towerPullback B j').map ((G.b g).inv.app E) := by
  have hs := b_square R φ B ψ C G gU j' j g h E
  dsimp only [Functor.comp_obj] at hs
  have hbj : (G.b j').hom.app ((pull R φ g).obj E) =
      (C.rho U').map ((moduleSquareG R φ gU j' j g h).hom.app E) ≫
        (G.b gU).hom.app ((pull R φ j).obj E) ≫
        (StrictTower.towerPullback B gU).map ((G.b j).hom.app E) ≫
        (scalarTowerSquare B gU j' j g h).inv.app ((C.rho X).obj E) ≫
        (StrictTower.towerPullback B j').map ((G.b g).inv.app E) := by
    rw [reassoc_of% hs, Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hbj, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc]

/-- The inverse form of the beta compatibility, proved on open-unit transposes.
Source: Stacks 09AE (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem towerBeta_key (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {U' U X' X : Scheme.{u}} (gU : U' ⟶ U)
    (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) (M : Modules R φ U) :
    (StrictTower.towerJ B j').map ((G.b gU).inv.app M) ≫
      (G.a j').inv.app ((pull R φ gU).obj M) ≫
      (C.rho X').map ((moduleBeta R φ gU j' j g h hsq).inv.app M) =
      (StrictTower.openBetaTower B gU j' j g h hsq).inv.app ((C.rho U).obj M) ≫
        (StrictTower.towerPullback B g).map ((G.a j).inv.app M) ≫
        (G.b g).inv.app ((extension R φ j).obj M) := by
  have hs' := b_square_inv R φ B ψ C G gU j' j g h ((extension R φ j).obj M)
  have hβ := moduleBeta_inv_unit R φ gU j' j g h hsq M
  apply ((scalarTowerOpenAdj B j').homEquiv _ _).injective
  have ho' := G.open_unit j' ((pull R φ gU).obj M)
  have ho := G.open_unit j M
  have hb := (G.b j').hom.naturality ((moduleBeta R φ gU j' j g h hsq).inv.app M)
  have hbu := (G.b gU).inv.naturality ((moduleJAdj R φ j).unit.app M)
  rw [scalarTowerSquare_eq_mapIso] at hs'
  have hsT := (Functor.whiskeringRightObjCompIso (StrictTower.modulePullback B g)
      (StrictTower.modulePullback B j') ≪≫
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (StrictTower.moduleSquareG B gU j' j g h) ≪≫
    (Functor.whiskeringRightObjCompIso (StrictTower.modulePullback B j)
      (StrictTower.modulePullback B gU)).symm).inv.naturality ((G.a j).hom.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at ho' ho hb hbu hsT ⊢
  have ho'' : (scalarTowerOpenAdj B j').unit.app ((C.rho U').obj ((pull R φ gU).obj M)) ≫
      (StrictTower.towerPullback B j').map ((G.a j').inv.app ((pull R φ gU).obj M)) =
      (C.rho U').map ((moduleJAdj R φ j').unit.app ((pull R φ gU).obj M)) ≫
        (G.b j').hom.app ((extension R φ j').obj ((pull R φ gU).obj M)) := by
    rw [← ho', Category.assoc, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right, towerBeta_unit, scalarTowerSquare_eq_mapIso,
    Adjunction.homEquiv_unit, ← ho]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% ho'', ← hb, ← Functor.map_comp_assoc, hβ, Functor.map_comp_assoc,
    ← reassoc_of% hbu, hs', reassoc_of% hsT,
    ← Functor.map_comp_assoc (StrictTower.towerPullback B j'),
    ← Functor.map_comp (StrictTower.towerPullback B g), Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Restriction preserves the canonical cartesian open comparison beta.
Source: Stacks 09AE (blueprint: lem-sf-semilinear-scalar-proper-open).
Proof: invert both sides and compare their open-unit transposes, using the open-unit
normalizations and the square compatibility of the inverse-image comparison. -/
private theorem towerBeta_comparison (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {U' U X' X : Scheme.{u}} (gU : U' ⟶ U)
    (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) (M : Modules R φ U) :
    (C.rho X').map ((moduleBeta R φ gU j' j g h hsq).hom.app M) ≫
        (G.a j').hom.app ((pull R φ gU).obj M) ≫
        (StrictTower.towerJ B j').map ((G.b gU).hom.app M) =
      (G.b g).hom.app ((extension R φ j).obj M) ≫
        (StrictTower.towerPullback B g).map ((G.a j).hom.app M) ≫
        (StrictTower.openBetaTower B gU j' j g h hsq).hom.app ((C.rho U).obj M) := by
  have key := towerBeta_key R φ B ψ C G gU j' j g h hsq M
  let I := (C.rho X').mapIso ((moduleBeta R φ gU j' j g h hsq).app M) ≪≫
    (G.a j').app ((pull R φ gU).obj M) ≪≫ (StrictTower.towerJ B j').mapIso ((G.b gU).app M)
  have hR : ((G.b g).hom.app ((extension R φ j).obj M) ≫
      (StrictTower.towerPullback B g).map ((G.a j).hom.app M) ≫
      (StrictTower.openBetaTower B gU j' j g h hsq).hom.app ((C.rho U).obj M)) ≫ I.inv = 𝟙 _ := by
    simp only [I, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
    rw [key, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_app]
  exact ((Iso.comp_inv_eq_id I).1 hR).symm

/-- The constant-tower alpha: beta, the clopen projector and the canonical compositors.
Source: Stacks 0F7B (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private def towerAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T)
    (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k]
    [QuasiCompact i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    StrictTower.towerJ B i ⋙ StrictTower.towerPullback B p ⟶
      StrictTower.towerPullback B r ⋙ StrictTower.towerJ B k :=
  (StrictTower.openBetaTower B (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom ≫
    Functor.whiskerRight (Functor.whiskerLeft (StrictTower.towerPullback B (pullback.snd p i))
      (scalarOrdinaryPi B (fun s ↦ towerClopen B s) (StrictTower.squareLift k r p i h)))
      (StrictTower.towerJ B (pullback.fst p i)) ≫
    Functor.whiskerLeft (StrictTower.towerPullback B (pullback.snd p i) ⋙
        StrictTower.towerPullback B (StrictTower.squareLift k r p i h))
      ((scalarTowerOpenComp B (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
        (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom) ≫
    Functor.whiskerRight
      ((StrictTower.towerGComp B (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
        (eqToIso (congrArg (StrictTower.towerPullback B) (pullback.lift_snd k r h))).hom)
      (StrictTower.towerJ B k)

/-- The components of the tower alpha are its defining word.
Source: Stacks 0F7B (blueprint: lem-sf-semilinear-scalar-proper-open). -/
private theorem towerAlpha_app {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T)
    (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k]
    [QuasiCompact i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : StrictTower.Towers B S) :
    (towerAlpha B k r p i h).app M =
      (StrictTower.openBetaTower B (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom.app M ≫
      (StrictTower.towerJ B (pullback.fst p i)).map
        ((scalarOrdinaryPi B (fun s ↦ towerClopen B s) (StrictTower.squareLift k r p i h)).app
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (scalarTowerOpenComp B (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom.app
        ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).obj
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom.app
        ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).obj
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (StrictTower.towerJ B k).map
        ((StrictTower.towerGComp B (StrictTower.squareLift k r p i h)
          (pullback.snd p i)).inv.app M ≫
          (eqToIso (congrArg (StrictTower.towerPullback B) (pullback.lift_snd k r h))).hom.app M) := by
  simp only [towerAlpha, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  rfl

/-- Restriction preserves the intrinsic proper/open alpha.
Source: Stacks 0F7B (blueprint: lem-sf-semilinear-scalar-proper-open).
Proof: move the coefficient comparisons through beta, the clopen projector and the
two compositors, using their preservation statements and naturality. -/
private theorem towerAlpha_comparison (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) {V W S T : Scheme.{u}} (k : V ⟶ W)
    (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Modules R φ S) :
    (C.rho W).map ((moduleAlpha R φ k r p i h).app M) ≫
        (G.a k).hom.app ((pull R φ r).obj M) ≫
        (StrictTower.towerJ B k).map ((G.b r).hom.app M) =
      (G.b p).hom.app ((extension R φ i).obj M) ≫
        (StrictTower.towerPullback B p).map ((G.a i).hom.app M) ≫
        (towerAlpha B k r p i h).app ((C.rho S).obj M) := by
  have hb := towerBeta_comparison R φ B ψ C G (pullback.snd p i) (pullback.fst p i) i p
    pullback.condition.symm (IsPullback.of_hasPullback p i).flip M
  have hπ := towerPi_comparison R φ B ψ C G (StrictTower.squareLift k r p i h)
    ((pull R φ (pullback.snd p i)).obj M)
  have hJ := a_jComp R φ B ψ C G (StrictTower.squareLift k r p i h) (pullback.fst p i)
    ((pull R φ (StrictTower.squareLift k r p i h)).obj ((pull R φ (pullback.snd p i)).obj M))
  have hJc := a_congr R φ B ψ C G (pullback.lift_fst k r h)
    ((pull R φ (StrictTower.squareLift k r p i h)).obj ((pull R φ (pullback.snd p i)).obj M))
  have hG := b_gComp R φ B ψ C G (StrictTower.squareLift k r p i h) (pullback.snd p i) M
  have hGc := b_congr R φ B ψ C G (pullback.lift_snd k r h) M
  have n1 := (G.a k).hom.naturality
    ((eqToIso (congrArg (pull R φ) (pullback.lift_snd k r h))).hom.app M)
  have n2 := (G.a k).hom.naturality
    ((moduleGComp R φ (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv.app M)
  have n3 := (G.a (pullback.fst p i)).hom.naturality
    ((modulePi R φ (StrictTower.squareLift k r p i h)).app ((pull R φ (pullback.snd p i)).obj M))
  have hk0 : (C.rho V).map
      ((moduleGComp R φ (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv.app M) ≫
      (C.rho V).map ((eqToIso (congrArg (pull R φ) (pullback.lift_snd k r h))).hom.app M) ≫
      (G.b r).hom.app M =
      (G.b (StrictTower.squareLift k r p i h)).hom.app ((pull R φ (pullback.snd p i)).obj M) ≫
        (StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).map
          ((G.b (pullback.snd p i)).hom.app M) ≫
        (StrictTower.towerGComp B (StrictTower.squareLift k r p i h)
          (pullback.snd p i)).inv.app ((C.rho S).obj M) ≫
        (eqToIso (congrArg (StrictTower.towerPullback B) (pullback.lift_snd k r h))).hom.app
          ((C.rho S).obj M) := by
    rw [hGc, reassoc_of% hG]
  have hk := congrArg (StrictTower.towerJ B k).map hk0
  have n4 := (scalarTowerOpenComp B (StrictTower.squareLift k r p i h)
    (pullback.fst p i)).hom.naturality
      ((G.b (StrictTower.squareLift k r p i h)).hom.app ((pull R φ (pullback.snd p i)).obj M))
  have n5 := (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom.naturality
      ((G.b (StrictTower.squareLift k r p i h)).hom.app ((pull R φ (pullback.snd p i)).obj M))
  have n6 := (scalarTowerOpenComp B (StrictTower.squareLift k r p i h)
    (pullback.fst p i)).hom.naturality
      ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).map
        ((G.b (pullback.snd p i)).hom.app M))
  have n7 := (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom.naturality
      ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).map
        ((G.b (pullback.snd p i)).hom.app M))
  have hπ' := congrArg (StrictTower.towerJ B (pullback.fst p i)).map hπ
  have n8 := (scalarOrdinaryPi B (fun s ↦ towerClopen B s)
    (StrictTower.squareLift k r p i h)).naturality ((G.b (pullback.snd p i)).hom.app M)
  have n8' := congrArg (StrictTower.towerJ B (pullback.fst p i)).map n8
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at n1 n2 n3 hk n4 n5 n6 n7 hπ' n8 n8'
  rw [towerAlpha_app]
  simp only [moduleAlpha, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp, Category.assoc]
  rw [reassoc_of% n1, reassoc_of% n2, reassoc_of% hJc, reassoc_of% hJ, reassoc_of% n3,
    reassoc_of% hk, ← reassoc_of% n5, ← reassoc_of% n4, ← reassoc_of% n7,
    ← reassoc_of% n6, reassoc_of% hπ', ← reassoc_of% n8', reassoc_of% hb]

/-- The normalized adjunction comparisons preserve beta, the clopen projector and alpha.
Source: Stacks 03D8, 03DI and 0F7B; blueprint fix-prop-coherence
(blueprint: lem-sf-semilinear-scalar-proper-open).
Proof: choose the constant-tower cartesian beta as the inverse open-unit transpose.
The inverse-image compositor comparison follows by taking the mates of the
sectionwise direct-image compositor. The open compositor comparison follows from
uniqueness of the unit-preserving left-adjoint comparison. Transposing the two sides
of beta compatibility, substituting these compositor and open-unit equations,
gives identical morphisms; the adjunction bijection proves their equality.
For a clopen map, the open unit is invertible and its inverse transpose is the
extension/direct-image comparison. Take its inverse and compose with the
direct-image unit to define pi. The already established unit and mate comparisons
prove pi compatibility. Define alpha by the specified beta, pi and compositor
word. Substitute beta and pi compatibility and the two compositor equations into
this word. Naturality moves each coefficient comparison through the factors, and
the neighboring inverse comparisons cancel. The resulting equation is alpha
compatibility. None of these arguments assumes that the proper/open square is
cartesian or that a coefficient map is flat. -/
theorem ordinaryScalarProperOpen (hψ : ∀ n : ℕ, ψ (n + 1) ≫ φ n = ψ n)
    (C : OrdinaryScalarRestriction R φ B ψ) (G : OrdinaryScalarAdjunctions R φ B ψ C) :
    Nonempty (OrdinaryScalarProperOpen R φ B ψ C G) :=
  ⟨{ beta := fun gU j' j g _ _ h hsq ↦ StrictTower.openBetaTower B gU j' j g h hsq
     beta_unit := fun gU j' j g _ _ h hsq M ↦ towerBeta_unit B gU j' j g h hsq M
     beta_comparison := fun gU j' j g _ _ h hsq M ↦
       towerBeta_comparison R φ B ψ C G gU j' j g h hsq M
     clopen := fun s _ _ ↦ towerClopen B s
     clopen_unit := fun s _ _ N ↦ towerClopen_unit B s N
     pi_comparison := fun s _ _ M ↦ towerPi_comparison R φ B ψ C G s M
     alpha := fun k r p i _ _ _ _ _ _ h ↦ towerAlpha B k r p i h
     alpha_eq := fun k r p i _ _ _ _ _ _ h M ↦ towerAlpha_app B k r p i h M
     alpha_comparison := fun k r p i _ _ _ _ _ _ h M ↦
       towerAlpha_comparison R φ B ψ C G k r p i h M }⟩

end AlgebraicGeometry.ProEtale.VaryingRing
