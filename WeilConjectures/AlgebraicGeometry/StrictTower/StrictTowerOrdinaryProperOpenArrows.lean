/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.CategoryTheory.SmoothPurity.TermwiseCompositeTransformation
public import WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenClopenProjector
public import WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows

/-! # Ordinary clopen arrows for constant-coefficient strict towers

Source: Stacks Project, Tags 09BN, 0F7B, and the underived refinement of the blueprint.
(blueprint: def-cbc-strict-tower-ordinary-proper-open-arrows)

These are the ordinary constructions underlying the recorded derived arrows. All
functors and adjunctions are the already specified constant-ring module operations.
The open unit, its direct-image transpose, and the clopen projector are imported
from ProperOpenClopenProjector. Cartesian beta and the open-extension compositor
are imported from TowerOpenBetaNormalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] Functor.leftAdjoint modulePullback

/-- Unit-preserving open-adjoint transport along equality of scheme morphisms.
Source: Stacks, Tag 09BN
(blueprint: def-cbc-strict-tower-ordinary-proper-open-arrows). -/
def singleJCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : moduleJ B f ≅ moduleJ B g :=
  ((moduleJAdj B f).ofNatIsoRight
    (eqToIso (congrArg (modulePullback B) h))).leftAdjointUniq (moduleJAdj B g)

/-- The intrinsic ordinary alpha: cartesian beta, clopen projection, and compositors.
Source: Stacks, Tag 0F7B and the blueprint's underived refinement
(blueprint: def-cbc-strict-tower-ordinary-proper-open-arrows). -/
def singleAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : moduleJ B i ⋙ modulePullback B p ⟶
      modulePullback B r ⋙ moduleJ B k :=
  (openBetaModule B (pullback.snd p i) (pullback.fst p i) i p
    (pullback.condition.symm) (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (modulePullback B (pullback.snd p i))
    (clopenModulePi B (squareLift k r p i h))) (moduleJ B (pullback.fst p i)) ≫
  Functor.whiskerRight
    (Functor.associator (modulePullback B (pullback.snd p i))
      (modulePullback B (squareLift k r p i h)) (moduleJ B (squareLift k r p i h))).inv
      (moduleJ B (pullback.fst p i)) ≫
  (Functor.associator
    (modulePullback B (pullback.snd p i) ⋙ modulePullback B (squareLift k r p i h))
    (moduleJ B (squareLift k r p i h)) (moduleJ B (pullback.fst p i))).hom ≫
  Functor.whiskerLeft
    (modulePullback B (pullback.snd p i) ⋙ modulePullback B (squareLift k r p i h))
    ((openBetaModuleJComp B (squareLift k r p i h) (pullback.fst p i)).hom ≫
      (singleJCongr B (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((moduleGComp B (squareLift k r p i h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (modulePullback B) (pullback.lift_snd k r h))).hom) (moduleJ B k)

/-- Termwise alpha on strict towers, before taking complexes.
Source: Stacks, Tag 0F7B
(blueprint: def-cbc-strict-tower-ordinary-proper-open-arrows). -/
def towerAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : towerJ B i ⋙ towerPullback B p ⟶
      towerPullback B r ⋙ towerJ B k :=
  Functor.termwiseCompositeTransformation ℕᵒᵖ (Modules B S) (Modules B T)
    (Modules B V) (Modules B W) (moduleJ B i) (modulePullback B p)
    (modulePullback B r) (moduleJ B k) (singleAlpha B k r p i h)

section DescentCalculus

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v₁ v₂ v₃ u₁ u₂ u₃ w₁ w₂ w₃
variable {A : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} A] [Category.{v₂} D] [Category.{v₃} E]
  [aA : Abelian A] [aD : Abelian D] [aE : Abelian E]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} D]
  [HasDerivedCategory.{w₃} E]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance] clopenTowerAbelian

private abbrev ordinaryAbelian (X : Scheme.{u}) : Abelian (Modules B X) :=
  @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ _ _
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X))
    (SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1})
    (SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1})

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem adjCongr_refl {L : A ⥤ D} {R : D ⥤ A} (a : L ⊣ R) :
    ((a.ofNatIsoRight (Iso.refl R)).leftAdjointUniq a).hom = 𝟙 L := by
  have he : a.ofNatIsoRight (Iso.refl R) = a := by
    apply Adjunction.ext
    apply NatTrans.ext
    funext X
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Iso.refl_hom, NatTrans.id_app]
    exact Category.comp_id _
  rw [he, Adjunction.leftAdjointUniq_refl]

private theorem singleJCongr_refl {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] : (singleJCongr B (rfl : f = f)).hom = 𝟙 _ := by
  exact adjCongr_refl (moduleJAdj B f)

private def compCompatible
    (F : A ⥤ D) (H : D ⥤ E) (L : A ⥤ E) [F.Additive] [H.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (t : F ⋙ H ⟶ L)
    (d : F.mapDerivedCategory ⋙ H.mapDerivedCategory ⟶ L.mapDerivedCategory) : Prop :=
  ∀ K : CochainComplex A ℤ,
    d.app (DerivedCategory.Q.obj K) ≫ L.mapDerivedCategoryFactors.hom.app K =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K)

private def squareCompatible
    {C : Type*} [Category C] [aC : Abelian C] [HasDerivedCategory C]
    (F : A ⥤ D) (H : D ⥤ E) (G : A ⥤ C) (L : C ⥤ E)
    [F.Additive] [H.Additive] [G.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (t : F ⋙ H ⟶ G ⋙ L)
    (d : F.mapDerivedCategory ⋙ H.mapDerivedCategory ⟶
      G.mapDerivedCategory ⋙ L.mapDerivedCategory) : Prop :=
  ∀ K : CochainComplex A ℤ,
    d.app (DerivedCategory.Q.obj K) ≫
        L.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        L.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K)

private def unitCompatible (F : A ⥤ D) (H : D ⥤ A) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (p : 𝟭 A ⟶ F ⋙ H)
    (d : 𝟭 (DerivedCategory A) ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory) : Prop :=
  ∀ K : CochainComplex A ℤ,
    d.app (DerivedCategory.Q.obj K) ≫
        H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex p (.up ℤ)).app K)

private theorem factorsh_eq (F : A ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, Iso.refl_hom, Iso.refl_inv, Functor.comp_obj]
  erw [F.mapDerivedCategory.map_id, Category.id_comp, DerivedCategory.Qh.map_id,
    Category.comp_id, Category.comp_id]

private theorem hom_fac
    {L : A ⥤ D} {R : D ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) (d : L.mapDerivedCategory ⊣ R.mapDerivedCategory)
    (hu : ∀ K : CochainComplex A ℤ,
      d.unit.app (DerivedCategory.Q.obj K) ≫
          R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
          R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K))
    (K : CochainComplex A ℤ) (N : CochainComplex D ℤ)
    (f : (L.mapHomologicalComplex (.up ℤ)).obj K ⟶ N) :
    d.homEquiv _ _ (L.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        R.mapDerivedCategoryFactors.inv.app N := by
  apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app N)).1
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryFactors_hom_naturality,
    ← Category.assoc (R.mapDerivedCategory.map _)]
  rw [← Category.assoc, hu]
  simp only [Iso.inv_hom_id_app, ← Functor.map_comp]
  erw [Category.comp_id]
  rw [Adjunction.homEquiv_unit]

omit [Abelian A] [Abelian D] [HasDerivedCategory A] [HasDerivedCategory D] in
private theorem conjugate_hom_fac
    {L L' : A ⥤ D} {R R' : D ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (e : L ≅ L')
    (K : A) (N : D) (f : L'.obj K ⟶ N) :
    a.homEquiv K N (e.hom.app K ≫ f) =
      b.homEquiv K N f ≫ (conjugateIsoEquiv b a e).hom.app N := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  have h := unit_conjugateEquiv b a e.hom K
  dsimp only [conjugateIsoEquiv_apply_hom] at *
  rw [← Category.assoc, ← h, Category.assoc]
  simpa only [Category.assoc] using
    congrArg (b.unit.app K ≫ ·) ((conjugateEquiv b a e.hom).naturality f).symm

private theorem square_fac
    {F : A ⥤ D} {H : D ⥤ E} {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {G : A ⥤ C} {L : C ⥤ E}
    [F.Additive] [H.Additive] [G.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : F ⋙ H ≅ G ⋙ L) (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
        L.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        L.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Category.assoc]
  have ht := Functor.mapDerivedCategoryCompIso_hom_app_factors F H K
  rw [← ht]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem square_fac_of_eq
    {F : A ⥤ D} {H : D ⥤ E} {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {G : A ⥤ C} {L : C ⥤ E}
    [F.Additive] [H.Additive] [G.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : F ⋙ H ≅ G ⋙ L)
    (d : F.mapDerivedCategory ⋙ H.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ L.mapDerivedCategory)
    (hd : d = Functor.mapDerivedCategorySquareIso e) (K : CochainComplex A ℤ) :
    d.hom.app (DerivedCategory.Q.obj K) ≫
        L.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        L.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  subst d
  exact square_fac e K

private theorem squareCompatible_of_eq
    {C : Type*} [Category C] [aC : Abelian C] [HasDerivedCategory C]
    (F : A ⥤ D) (H : D ⥤ E) (G : A ⥤ C) (L : C ⥤ E)
    [F.Additive] [H.Additive] [G.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (t : F ⋙ H ≅ G ⋙ L)
    (d : F.mapDerivedCategory ⋙ H.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ L.mapDerivedCategory)
    (hd : d = Functor.mapDerivedCategorySquareIso t) :
    squareCompatible F H G L t.hom d.hom := by
  intro K
  exact square_fac_of_eq t d hd K

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem whisker_comp_hom
    {L₁ : A ⥤ D} {R₁ : D ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {L₃ : A ⥤ E} {R₃ : E ⥤ A}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃) (e : R₃ ≅ R₂ ⋙ R₁) :
    (Adjunction.leftAdjointCompIso (a.whiskerRight ℕᵒᵖ) (b.whiskerRight ℕᵒᵖ)
      (c.whiskerRight ℕᵒᵖ)
      (((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e) ≪≫
        Functor.whiskeringRightObjCompIso R₂ R₁).symm).hom =
      ((Functor.whiskeringRightObjCompIso L₁ L₂).symm ≪≫
        (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
          (Adjunction.leftAdjointCompIso a b c e.symm)).hom := by
  ext M n
  simp only [Adjunction.leftAdjointCompIso_hom_app]
  dsimp only [Functor.whiskeringRight, Functor.comp_obj, Functor.comp_map,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.whiskeringRightObjCompIso,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  simp only [Adjunction.whiskerRight_unit_app_app,
    Adjunction.whiskerRight_counit_app_app, Category.comp_id, Category.id_comp,
    Adjunction.leftAdjointCompIso_hom_app]
  rfl

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
@[irreducible] private def termwiseCompHom (f : A ⥤ D) (g : D ⥤ E) (h : A ⥤ E)
    (t : f ⋙ g ⟶ h) :
    (Functor.whiskeringRight ℕᵒᵖ A D).obj f ⋙
      (Functor.whiskeringRight ℕᵒᵖ D E).obj g ⟶
      (Functor.whiskeringRight ℕᵒᵖ A E).obj h :=
  (Functor.whiskeringRightObjCompIso f g).inv ≫
    (Functor.whiskeringRight ℕᵒᵖ A E).map t

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private abbrev tw {C D : Type*} [Category C] [Category D] (f : C ⥤ D) :=
  (Functor.whiskeringRight ℕᵒᵖ C D).obj f

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem projector_paste (G : A ⥤ D) (J : D ⥤ A) (H : A ⥤ E) (L : D ⥤ E)
    (p : 𝟭 A ⟶ G ⋙ J) (a : J ⋙ H ⟶ L)
    {x x' z : A} {y : D} {w v : E}
    (f : x ⟶ x') (g : G.obj x' ⟶ y) (l : J.obj y ⟶ z)
    (m : H.obj z ⟶ w) (n : w ⟶ v) (t : L.obj y ⟶ v)
    (ha : a.app y ≫ t = H.map l ≫ m ≫ n)
    (p' : x' ⟶ z) (hp : p.app x' ≫ J.map g ≫ l = p') :
    H.map (p.app x) ≫ a.app (G.obj x) ≫ L.map (G.map f) ≫ L.map g ≫ t =
      H.map f ≫ H.map p' ≫ m ≫ n := by
  have hc : p.app x ≫ J.map (G.map f ≫ g) ≫ l = f ≫ p' := by
    rw [J.map_comp]
    rw [← Category.assoc, ← Category.assoc]
    change ((p.app x ≫ (G ⋙ J).map f) ≫ J.map g) ≫ l = _
    rw [← p.naturality f]
    simpa only [Category.assoc, Functor.id_map, Functor.id_obj] using congrArg (f ≫ ·) hp
  calc
    _ = H.map (p.app x ≫ J.map (G.map f ≫ g) ≫ l) ≫ m ≫ n := by
      rw [← L.map_comp_assoc, ← a.naturality_assoc]
      change H.map (p.app x) ≫ H.map (J.map (G.map f ≫ g)) ≫ a.app y ≫ t = _
      rw [ha]
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by rw [hc, H.map_comp]; simp only [Category.assoc]

private def towerJTail {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    (l : U ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
    (h : j ≫ k = l) : towerJ B j ⋙ towerJ B k ⟶ towerJ B l :=
  termwiseCompHom (moduleJ B j) (moduleJ B k) (moduleJ B l)
    ((openBetaModuleJComp B j k).hom ≫ (singleJCongr B h).hom)

private def towerGTail {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : X ⟶ Z) (h : f ≫ g = r) :
    towerPullback B g ⋙ towerPullback B f ⟶ towerPullback B r :=
  termwiseCompHom (modulePullback B g) (modulePullback B f) (modulePullback B r)
    ((moduleGComp B f g).inv ≫ (eqToIso (congrArg (modulePullback B) h)).hom)

omit [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem complex_four
    {F₀ F₁ F₂ F₃ F₄ : A ⥤ E}
    [F₀.Additive] [F₁.Additive] [F₂.Additive] [F₃.Additive] [F₄.Additive]
    (a : F₀ ⟶ F₁) (b : F₁ ⟶ F₂) (c : F₂ ⟶ F₃) (d : F₃ ⟶ F₄)
    (K : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex (a ≫ b ≫ c ≫ d) (.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex a (.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex b (.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex c (.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex d (.up ℤ)).app K := by
  simp only [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

omit [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem complex_whiskerLeft
    (F : A ⥤ D) {H L : D ⥤ E} [F.Additive] [H.Additive] [L.Additive]
    (a : H ⟶ L) (K : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex (Functor.whiskerLeft F a) (.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex a (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  ext n
  rfl

omit [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem complex_whiskerRight
    {F G : A ⥤ D} (H : D ⥤ E) [F.Additive] [G.Additive] [H.Additive]
    (a : F ⟶ G) (K : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex (Functor.whiskerRight a H) (.up ℤ)).app K =
      (H.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K) := by
  ext n
  rfl

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem whisker_paste
    {C T : Type*} [Category C] [Category T]
    (i : A ⥤ T) (p : T ⥤ E) (q : A ⥤ D) (s : D ⥤ C) (j : C ⥤ D)
    (b : D ⥤ E) (k : C ⥤ E) (r : A ⥤ C)
    (βt : i ⋙ p ⟶ q ⋙ b) (pt : 𝟭 D ⟶ s ⋙ j) (τj : j ⋙ b ⟶ k)
    (et : q ⋙ s ⟶ r) :
    (Functor.whiskeringRightObjCompIso i p).hom ≫
      (Functor.whiskeringRight ℕᵒᵖ A E).map
        (βt ≫ Functor.whiskerRight (Functor.whiskerLeft q pt) b ≫
          Functor.whiskerLeft (q ⋙ s) τj ≫ Functor.whiskerRight et k) ≫
      (Functor.whiskeringRightObjCompIso r k).inv =
    ((Functor.whiskeringRightObjCompIso i p).hom ≫
      (Functor.whiskeringRight ℕᵒᵖ A E).map βt ≫
      (Functor.whiskeringRightObjCompIso q b).inv) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft ((Functor.whiskeringRight ℕᵒᵖ A D).obj q)
        ((Functor.whiskeringRight ℕᵒᵖ D D).map pt))
      ((Functor.whiskeringRight ℕᵒᵖ D E).obj b) ≫
    Functor.whiskerLeft
      ((Functor.whiskeringRight ℕᵒᵖ A D).obj q ⋙
        (Functor.whiskeringRight ℕᵒᵖ D C).obj s)
      ((Functor.whiskeringRightObjCompIso j b).inv ≫
        (Functor.whiskeringRight ℕᵒᵖ C E).map τj) ≫
    Functor.whiskerRight
      ((Functor.whiskeringRightObjCompIso q s).inv ≫
        (Functor.whiskeringRight ℕᵒᵖ A C).map et)
      ((Functor.whiskeringRight ℕᵒᵖ C E).obj k) := by
  ext M n
  dsimp only [Functor.whiskeringRightObjCompIso, Functor.whiskeringRight,
    towerJ, towerPullback,
    Functor.comp_obj, Functor.comp_map, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.comp_app, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app]
  simp only [Category.id_comp, Category.comp_id]

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem assoc_paste
    {C T : Type*} [Category C] [Category T]
    (i : A ⥤ T) (p : T ⥤ E) (q : A ⥤ D) (s : D ⥤ C) (j : C ⥤ D)
    (b : D ⥤ E) (k : C ⥤ E) (r : A ⥤ C)
    (βt : i ⋙ p ⟶ q ⋙ b) (pt : 𝟭 D ⟶ s ⋙ j) (τj : j ⋙ b ⟶ k)
    (et : q ⋙ s ⟶ r) :
    βt ≫ Functor.whiskerRight (Functor.whiskerLeft q pt) b ≫
      Functor.whiskerRight (Functor.associator q s j).inv b ≫
      (Functor.associator (q ⋙ s) j b).hom ≫
      Functor.whiskerLeft (q ⋙ s) τj ≫ Functor.whiskerRight et k =
    βt ≫ Functor.whiskerRight (Functor.whiskerLeft q pt) b ≫
      Functor.whiskerLeft (q ⋙ s) τj ≫ Functor.whiskerRight et k := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.comp_obj,
    Category.id_comp]
  rw [b.map_id, Category.id_comp]

end DescentCalculus

end AlgebraicGeometry.ProEtale.StrictTower
