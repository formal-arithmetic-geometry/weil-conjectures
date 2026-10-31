/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralCompactificationSystemRealization
public import WeilConjectures.SixFunctors.ConstantSemilinearGeneratorComparison
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.SfCbcCompactSupportCompositionLimit
public import WeilConjectures.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import WeilConjectures.Compactification.Triangle
import WeilConjectures.SixFunctors.IntegralCompactificationOrdinaryScalarAction

/-! # Integral compactification comparison bridge

Source: blueprint main-20261015, fix-lem-exchanges, proof Step 5; the additional
constant/semilinear comparison obligation
(blueprint: def-sf-integral-compactification-ordinary-site-transport).

The helpers fix the small-site coordinate transports by sections and adjunction mates.
The two composition maps are constructed independently, before any finite evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralCompactificationBridge
open IntegralSystemRealization GeneratorReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical exact small-site transport on strict constant towers.
Source: Stacks 00VC, 0941
(blueprint: def-sf-integral-compactification-ordinary-site-transport). -/
abbrev towerModel (T : Scheme.{u}) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sfCbcModelModules T (constantRing l E))

/-- Named exactness data keep derived site transport from re-expanding equivalence proofs.
Source: Stacks 00VC, 0941
(blueprint: def-sf-integral-compactification-ordinary-site-transport). -/
instance towerModel_additive (T : Scheme.{u}) :
    Functor.Additive (towerModel l E T) := inferInstance

/-- Named exactness data keep derived site transport from re-expanding equivalence proofs.
Source: Stacks 00VC, 0941
(blueprint: def-sf-integral-compactification-ordinary-site-transport). -/
instance towerModel_preservesFiniteLimits (T : Scheme.{u}) :
    PreservesFiniteLimits (towerModel l E T) := inferInstance

/-- Named exactness data keep derived site transport from re-expanding equivalence proofs.
Source: Stacks 00VC, 0941
(blueprint: def-sf-integral-compactification-ordinary-site-transport). -/
instance towerModel_preservesFiniteColimits (T : Scheme.{u}) :
    PreservesFiniteColimits (towerModel l E T) := inferInstance

/-- The same transport after localizing the strict diagram category.
Source: Stacks 00VC, 05RU
(blueprint: def-sf-integral-compactification-ordinary-site-transport). -/
abbrev derivedTowerModel (T : Scheme.{u}) := (towerModel l E T).mapDerivedCategory

private theorem underlying_add
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {A : Type*} [Ring A] (F G : C ⥤ ModuleCat A) [F.Additive] [G.Additive]
    (a : F ⋙ forget (ModuleCat A) ⟶ G ⋙ forget (ModuleCat A))
    (M : C) (x y : F.obj M) : a.app M (x + y) = a.app M x + a.app M y := by
  have hn {M N : C} (f : M ⟶ N) (x : F.obj M) :
      a.app N ((F.map f) x) = (G.map f) (a.app M x) :=
    congrArg (fun h ↦ h x) (a.naturality f)
  let z : F.obj (M ⊞ M) := F.map biprod.inl x + F.map biprod.inr y
  have hz₁ : F.map (biprod.fst : M ⊞ M ⟶ M) z = x := by
    simp [z, ← ModuleCat.comp_apply, ← F.map_comp]
  have hz₂ : F.map (biprod.snd : M ⊞ M ⟶ M) z = y := by
    simp [z, ← ModuleCat.comp_apply, ← F.map_comp]
  calc
    a.app M (x + y) =
        a.app M (F.map (biprod.fst + biprod.snd : M ⊞ M ⟶ M) z) := by
      rw [F.map_add]
      change a.app M (x + y) = a.app M
        (F.map biprod.fst z + F.map biprod.snd z)
      rw [hz₁, hz₂]
    _ = G.map (biprod.fst + biprod.snd : M ⊞ M ⟶ M) (a.app _ z) := hn _ z
    _ = G.map biprod.fst (a.app _ z) + G.map biprod.snd (a.app _ z) := by
      rw [G.map_add]
      rfl
    _ = a.app M x + a.app M y := by rw [← hn, ← hn, hz₁, hz₂]

/-- Direct-image transport is uniquely fixed on every underlying section.
Source: Stacks 03D7, 00VC
(blueprint: def-sf-integral-compactification-ordinary-site-transport).
Proof: both functors are geometric precomposition with the same coefficient action.
The displayed underlying direct-image comparison is the Hom-normalized comparison of
constantSemilinearGeneratorComparison. Identity on its sections is linear, natural,
and invertible. Sections determine the comparison uniquely. -/
theorem ordinaryDirectModel_existsUnique {V T : Scheme.{u}} (f : V ⟶ T) :
    ∃! b : ProEtale.StrictTower.moduleDirectImage
        (ULift.{u + 1} (constantRing l E)) f ⋙ sfCbcModelModules T (constantRing l E) ≅
      sfCbcModelModules V (constantRing l E) ⋙
        (sfCbcMorphism f).modulePush (ULift.{u + 1} (constantRing l E)),
      ∀ (M : ProEtale.StrictTower.Modules (ULift.{u + 1} (constantRing l E)) V)
        (W : (proEtaleSiteModel T)ᵒᵖ)
        (x : ((sfCbcModelModules T (constantRing l E)).obj
          ((ProEtale.StrictTower.moduleDirectImage
            (ULift.{u + 1} (constantRing l E)) f).obj M)).val.obj W),
        HEq (((constantDirectUnderlying l E f).hom.app
          ((sfCbcModelModules V (constantRing l E)).obj M)).hom.app W
            ((b.hom.app M).val.app W x)) x := by
  classical
  let L := ProEtale.StrictTower.moduleDirectImage
    (ULift.{u + 1} (constantRing l E)) f ⋙ sfCbcModelModules T (constantRing l E)
  let R : ProEtale.StrictTower.Modules (ULift.{u + 1} (constantRing l E)) V ⥤
      ConstantCompletion.Mod (sfCbcModelRing T (constantRing l E)) :=
    sfCbcModelModules V (constantRing l E) ⋙
    (sfCbcMorphism f).modulePush (ULift.{u + 1} (constantRing l E))
  let U := ConstantCompletion.underlying (sfCbcModelRing T (constantRing l E))
  let e : R ⋙ U ≅ L ⋙ U :=
    Functor.isoWhiskerLeft (sfCbcModelModules V (constantRing l E))
      (constantDirectUnderlying l E f)
  have ha (M) (W) (x y : (L.obj M).val.obj W) :
      (e.inv.app M).hom.app W (x + y) =
        (show (R.obj M).val.obj W from (e.inv.app M).hom.app W x) +
          (show (R.obj M).val.obj W from (e.inv.app M).hom.app W y) := by
    have : (SheafOfModules.evaluation (siteModuleRings
        (sfCbcModelRing T (constantRing l E))) W).Additive := by
      dsimp only [SheafOfModules.evaluation]
      infer_instance
    have : ((sfCbcMorphism f).modulePush
        (ULift.{u + 1} (constantRing l E))).Additive :=
      ((sfCbcMorphism f).moduleAdjunction
        (ULift.{u + 1} (constantRing l E))).right_adjoint_additive
    have : R.Additive := by
      dsimp only [R]
      infer_instance
    exact underlying_add
      (L ⋙ SheafOfModules.evaluation _ W) (R ⋙ SheafOfModules.evaluation _ W)
      { app := fun M ↦ (e.inv.app M).hom.app W
        naturality := by
          intro M N a
          exact congrArg (fun h ↦ h.hom.app W) (e.inv.naturality a) }
      M x y
  have hs (M) (W) (r : (sfCbcModelRing T (constantRing l E)).obj.obj W)
      (x : (L.obj M).val.obj W) :
      (e.inv.app M).hom.app W (r • x) =
        r • (show (R.obj M).val.obj W from (e.inv.app M).hom.app W x) := by
    exact ordinaryDirectUnderlying_smul l E f M W r x
  let b : L ⟶ R :=
    { app := fun M ↦
        ⟨{ app := fun W ↦ ModuleCat.ofHom
              (X := (L.obj M).val.obj W) (Y := (R.obj M).val.obj W)
              { toFun := (e.inv.app M).hom.app W
                map_add' := ha M W
                map_smul' := hs M W }
           naturality := by
             intro W W' a
             ext x
             exact congrArg (fun h ↦ h x) ((e.inv.app M).hom.naturality a) }⟩
      naturality := by
        intro M N a
        ext W x
        exact congrArg (fun h ↦ h.hom.app W x) (e.inv.naturality a) }
  have hinv (M) (W) (x : (L.obj M).val.obj W) :
      (e.hom.app M).hom.app W ((b.app M).val.app W x) = x :=
    congrArg (fun h ↦ h.hom.app W x) (e.inv_hom_id_app M)
  have hbij (M) (W) : Function.Bijective ((b.app M).val.app W) := by
    constructor
    · intro x y h
      exact (hinv M W x).symm.trans ((congrArg ((e.hom.app M).hom.app W) h).trans
        (hinv M W y))
    · intro y
      refine ⟨(e.hom.app M).hom.app W y, ?_⟩
      exact congrArg (fun h ↦ h.hom.app W y) (e.hom_inv_id_app M)
  have hcomp (M) (W) : IsIso ((b.app M).val.app W) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij M W)
  have hpres (M) : IsIso (b.app M).val := by
    let q := PresheafOfModules.isoMk (fun W ↦ asIso ((b.app M).val.app W))
      (by intro W W' a; exact (b.app M).val.naturality a)
    have hq : q.hom = (b.app M).val := by ext W x; rfl
    rw [← hq]
    infer_instance
  have hmod (M) : IsIso (b.app M) := by
    have : IsIso ((SheafOfModules.forget _).map (b.app M)) := hpres M
    exact isIso_of_reflects_iso (b.app M) (SheafOfModules.forget _)
  have : IsIso b := NatIso.isIso_of_isIso_app b
  refine ⟨asIso b, ?_, ?_⟩
  · intro M W x
    exact heq_of_eq (hinv M W x)
  · intro c hc
    apply Iso.ext
    ext M W x
    have h := eq_of_heq (hc M W x)
    change (e.hom.app M).hom.app W ((c.hom.app M).val.app W x) = x at h
    have hi := congrArg (fun h ↦ h.hom.app W ((c.hom.app M).val.app W x))
      (e.hom_inv_id_app M)
    change (e.inv.app M).hom.app W
      ((e.hom.app M).hom.app W ((c.hom.app M).val.app W x)) = _ at hi
    rw [h] at hi
    exact hi.symm

/-- The section-normalized ordinary direct-image transport.
Source: Stacks 03D7 (blueprint: def-sf-integral-compactification-ordinary-site-transport). -/
def ordinaryDirectModel {V T : Scheme.{u}} (f : V ⟶ T) :=
  (ordinaryDirectModel_existsUnique l E f).exists.choose

end WeilConjectures.IntegralCompactificationBridge
