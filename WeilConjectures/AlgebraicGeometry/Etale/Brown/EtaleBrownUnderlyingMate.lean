/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization

/-! # The ordinary restriction and Brown image cube

Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 03CV and 03CZ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive
section OrdinaryRightCube

universe a₀v a₁v b₀v b₁v xv yv a₀u a₁u b₀u b₁u xu yu
variable {A₀ : Type a₀u} [Category.{a₀v} A₀] {A₁ : Type a₁u} [Category.{a₁v} A₁]
  {B₀ : Type b₀u} [Category.{b₀v} B₀] {B₁ : Type b₁u} [Category.{b₁v} B₁]
  {X : Type xu} [Category.{xv} X] {Y : Type yu} [Category.{yv} Y]
  (F₀ : A₀ ⥤ B₀) (G₀ : B₀ ⥤ A₀) (a₀ : F₀ ⊣ G₀)
  (F₁ : A₁ ⥤ B₁) (G₁ : B₁ ⥤ A₁) (a₁ : F₁ ⊣ G₁)
  (RA : A₀ ⥤ A₁) (RB : B₀ ⥤ B₁)
  (Ua : A₁ ⥤ X) (Un : A₀ ⥤ X) (Ub : B₁ ⥤ Y) (Uq : B₀ ⥤ Y)
  (L : X ⥤ Y) (V : Y ⥤ X) (adj : L ⊣ V)
  (ra : RA ⋙ Ua ≅ Un) (rb : RB ⋙ Ub ≅ Uq)
  (mu₀ : F₀ ⋙ Uq ≅ Un ⋙ L) (mu₁ : F₁ ⋙ Ub ≅ Ua ⋙ L)
  (γ₀ : G₀ ⋙ Un ≅ Uq ⋙ V) (γ₁ : G₁ ⋙ Ua ≅ Ub ⋙ V)
  (β : RA ⋙ F₁ ≅ F₀ ⋙ RB)
  (h₀ : ∀ M N (f : F₀.obj M ⟶ N),
    Un.map (a₀.homEquiv M N f) ≫ γ₀.hom.app N =
      adj.homEquiv _ _ (mu₀.inv.app M ≫ Uq.map f))
  (h₁ : ∀ M N (f : F₁.obj M ⟶ N),
    Ua.map (a₁.homEquiv M N f) ≫ γ₁.hom.app N =
      adj.homEquiv _ _ (mu₁.inv.app M ≫ Ub.map f))
  (hβ : ∀ M, Ub.map (β.hom.app M) ≫ rb.hom.app (F₀.obj M) ≫ mu₀.hom.app M =
    mu₁.hom.app (RA.obj M) ≫ L.map (ra.hom.app M))

include h₀ h₁ hβ in
private theorem ordinary_restriction_mate (N : B₀) :
    Ua.map ((mateEquiv a₀ a₁ (.mk _ _ _ _ β.hom)).app N) ≫
        γ₁.hom.app (RB.obj N) ≫ V.map (rb.hom.app N) =
      ra.hom.app (G₀.obj N) ≫ γ₀.hom.app N := by
  let α := (mateEquiv a₀ a₁ (.mk _ _ _ _ β.hom))
  let M := G₀.obj N
  let ε := a₀.counit.app N
  have ha : α.app N = a₁.homEquiv _ _
      (β.hom.app M ≫ RB.map ε) := by
    dsimp only [α, mateEquiv, TwoSquare.mk,
      Equiv.coe_fn_mk, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
      Functor.leftUnitor_hom_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.comp_obj]
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.id_comp]
    dsimp only [Functor.comp_map]
    erw [Category.comp_id]
  rw [ha]
  erw [← Category.assoc, h₁]
  rw [← adj.homEquiv_naturality_right]
  apply (adj.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  have hb := rb.hom.naturality ε
  change Ub.map (RB.map ε) ≫ rb.hom.app N =
    rb.hom.app (F₀.obj M) ≫ Uq.map ε at hb
  simp only [Functor.map_comp, Category.assoc]
  rw [hb]
  have hi := hβ M
  have hi' : mu₁.inv.app (RA.obj M) ≫
      Ub.map (β.hom.app M) ≫
      rb.hom.app (F₀.obj M) =
    L.map (ra.hom.app M) ≫ mu₀.inv.app M := by
    apply (cancel_epi (mu₁.hom.app (RA.obj M))).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    apply (cancel_mono (mu₀.hom.app M)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact hi
  dsimp only [Functor.comp_obj]
  slice_lhs 1 3 => exact hi'
  rw [Category.assoc]
  rw [Adjunction.homEquiv_naturality_left_symm]
  have hε : a₀.homEquiv M N ε = 𝟙 M := by
    rw [Adjunction.homEquiv_unit, a₀.right_triangle_components]
  have hn := h₀ M N ε
  rw [hε] at hn
  erw [Un.map_id M, Category.id_comp] at hn
  erw [hn, Equiv.symm_apply_apply]

end OrdinaryRightCube
private local instance brown_mate_pullback_continuous
    {V W : Scheme.{u}} (g : V ⟶ W) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      W.smallEtaleTopology V.smallEtaleTopology := Etale.isContinuous_overPullback g

section UnderlyingOrdinaryCube

private abbrev brownMateLevel (W : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :=
  SheafOfModules.{u + 1}
    ((sheafCompose W.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of R)))

private abbrev brownMateUnderlying (W : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    brownMateLevel W R ⥤ Sheaf W.smallEtaleTopology (Type (u + 1)) :=
  toSheaf _ ⋙ sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})

private abbrev brownMateRestriction (W : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) :
    brownMateLevel W S ⥤ brownMateLevel W R :=
  SheafOfModules.restrictScalars
    ((sheafCompose W.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map (CommRingCat.ofHom φ)))

private abbrev brownMateRestrictionUnderlying (W : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) :
    brownMateRestriction W φ ⋙ brownMateUnderlying W R ≅ brownMateUnderlying W S :=
  isoWhiskerRight (siteScalarUnderlyingIso
    ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map (CommRingCat.ofHom φ)))
    (sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1}))

private theorem brown_underlying_ordinary_cube
    (R S : Type (u + 1)) [CommRing R] [CommRing S] (φ : R →+* S)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (Gm : brownMateLevel V S ⥤ brownMateLevel W S)
    (Gn : brownMateLevel V R ⥤ brownMateLevel W R)
    (α : Gm ⋙ brownMateRestriction W φ ⟶ brownMateRestriction V φ ⋙ Gn)
    (γm : Gm ⋙ brownMateUnderlying W S ≅ brownMateUnderlying V S ⋙
      (MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
        (Type (u + 1)) W.smallEtaleTopology V.smallEtaleTopology)
    (γn : Gn ⋙ brownMateUnderlying W R ≅ brownMateUnderlying V R ⋙
      (MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
        (Type (u + 1)) W.smallEtaleTopology V.smallEtaleTopology)
    (rW : brownMateRestriction W φ ⋙ Etale.SystemProjection.constantModule W (.of R) ≅
      Etale.SystemProjection.constantModule W (.of S) ⋙
        Sheaf.restrictScalars W.smallEtaleTopology φ)
    (rV : brownMateRestriction V φ ⋙ Etale.SystemProjection.constantModule V (.of R) ≅
      Etale.SystemProjection.constantModule V (.of S) ⋙
        Sheaf.restrictScalars V.smallEtaleTopology φ)
    (dm : Gm ⋙ Etale.SystemProjection.constantModule W (.of S) ≅
      Etale.SystemProjection.constantModule V (.of S) ⋙ Etale.lowerStar (ModuleCat S) g)
    (dn : Gn ⋙ Etale.SystemProjection.constantModule W (.of R) ≅
      Etale.SystemProjection.constantModule V (.of R) ⋙ Etale.lowerStar (ModuleCat R) g)
    (hraw : ∀ N,
      (brownMateUnderlying W R).map (α.app N) ≫
        γn.hom.app ((brownMateRestriction V φ).obj N) ≫
        ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
          (Type (u + 1)) W.smallEtaleTopology V.smallEtaleTopology).map
            ((brownMateRestrictionUnderlying V φ).hom.app N) =
      (brownMateRestrictionUnderlying W φ).hom.app (Gm.obj N) ≫ γm.hom.app N)
    (hrW : ∀ (M : brownMateLevel W S) (U : W.Etaleᵒᵖ) (x : M.val.obj U),
      HEq ((rW.hom.app M).hom.app U x) x)
    (hrV : ∀ (M : brownMateLevel V S) (U : V.Etaleᵒᵖ) (x : M.val.obj U),
      HEq ((rV.hom.app M).hom.app U x) x)
    (hdm : ∀ (N : brownMateLevel V S) (U : W.Etaleᵒᵖ) (x : (Gm.obj N).val.obj U),
      (dm.hom.app N).hom.app U x = (γm.hom.app N).hom.app U x)
    (hdn : ∀ (N : brownMateLevel V R) (U : W.Etaleᵒᵖ) (x : (Gn.obj N).val.obj U),
      (dn.hom.app N).hom.app U x = (γn.hom.app N).hom.app U x)
    (N : brownMateLevel V S) :
    (Etale.SystemProjection.constantModule W (.of R)).map (α.app N) ≫
        dn.hom.app ((brownMateRestriction V φ).obj N) ≫
        (Etale.lowerStar (ModuleCat R) g).map (rV.hom.app N) =
      rW.hom.app (Gm.obj N) ≫
        (Sheaf.restrictScalars W.smallEtaleTopology φ).map (dm.hom.app N) ≫
        (Etale.lowerStarRestrictScalarsIso φ g).hom.app
          ((Etale.SystemProjection.constantModule V (.of S)).obj N) := by
  ext U x
  have hu := congrArg (fun z ↦ z.hom.app U x) (hraw N)
  change (γn.hom.app _).hom.app U ((α.app N).val.app U x) =
    (γm.hom.app N).hom.app U x at hu
  have hw := hrW (Gm.obj N) U x
  have hv := hrV N ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj U)
    ((dn.hom.app _).hom.app U ((α.app N).val.app U x))
  change (rV.hom.app N).hom.app
      ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj U)
      ((dn.hom.app _).hom.app U ((α.app N).val.app U x)) =
    (dm.hom.app N).hom.app U ((rW.hom.app _).hom.app U x)
  calc
    _ = (dn.hom.app _).hom.app U ((α.app N).val.app U x) := eq_of_heq hv
    _ = (γn.hom.app _).hom.app U ((α.app N).val.app U x) := hdn _ U _
    _ = (γm.hom.app N).hom.app U x := hu
    _ = (dm.hom.app N).hom.app U x := (hdm N U x).symm
    _ = _ := congrArg ((dm.hom.app N).hom.app U) (eq_of_heq hw).symm

end UnderlyingOrdinaryCube

-- Specializing the mate checks the concrete coefficient categories.
/-- The underlying ordinary Brown mate after restriction. -/
private theorem brown_underlying_cube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    {m n : ℕ} (h : m ≤ n) (M : strictEtaleLevel V O t m) :
    (coefficientUnderlying (J := W.smallEtaleTopology) O t n).map
        ((mateEquiv (A.levelAdj m) (A.levelAdj n)
          (.mk _ _ _ _ (A.restrictInverse h).hom)).app M) ≫
      (A.rightUnderlying n).hom.app
        ((coefficientRestriction (J := V.smallEtaleTopology) O t h).obj M) ≫
      ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
        (Type (u + 1)) _ _).map
        ((coefficientRestrictionUnderlying (J := V.smallEtaleTopology) O t h).hom.app M) =
    (coefficientRestrictionUnderlying (J := W.smallEtaleTopology) O t h).hom.app
        ((A.right m).obj M) ≫ (A.rightUnderlying m).hom.app M := by
  exact ordinary_restriction_mate
    (A.lift m).modules (A.right m) (A.levelAdj m)
    (A.lift n).modules (A.right n) (A.levelAdj n)
    (coefficientRestriction (J := W.smallEtaleTopology) O t h)
    (coefficientRestriction (J := V.smallEtaleTopology) O t h)
    (coefficientUnderlying (J := W.smallEtaleTopology) O t n)
    (coefficientUnderlying (J := W.smallEtaleTopology) O t m)
    (coefficientUnderlying (J := V.smallEtaleTopology) O t n)
    (coefficientUnderlying (J := V.smallEtaleTopology) O t m)
    _ _ (strictEtaleSetAdjunction g)
    (coefficientRestrictionUnderlying (J := W.smallEtaleTopology) O t h)
    (coefficientRestrictionUnderlying (J := V.smallEtaleTopology) O t h)
    (A.lift m).moduleUnderlying (A.lift n).moduleUnderlying
    (A.rightUnderlying m) (A.rightUnderlying n) (A.restrictInverse h)
    (A.levelTranspose m) (A.levelTranspose n) (A.restrictInverseUnderlying h) M

-- Name the coherence components so their large types are checked once and shared
-- by the section-law projection and its uses in the ordinary cube.
private def brown_underlying_restriction_coherence
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t)
    (R : StrictEtaleBrownRealizationData O t W P) : Prop :=
  ∀ {m n : ℕ} (h : m ≤ n) (M : strictEtaleLevel W O t m)
    (U : W.Etaleᵒᵖ) (x : M.val.obj U),
    HEq (((R.ordinaryRestriction h).hom.app M).hom.app U x) x

private def brown_underlying_localization_coherence
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t)
    (R : StrictEtaleBrownRealizationData O t W P) : Prop :=
  letI := R.ordinaryAdditive
  ∀ {m n : ℕ} (h : m ≤ n) (K : CochainComplex (strictEtaleLevel W O t m) ℤ),
    (R.restriction h).hom.app (DerivedCategory.Q.obj K) ≫
      (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h)).map ((R.factors m).hom.app K) ≫
      (Sheaf.restrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h)).mapDerivedCategoryFactors.hom.app
          (((strictEtaleBrownConstant O t W m).mapHomologicalComplex (.up ℤ)).obj K) =
    (R.derived n).map ((P.scalar h).restrictionFactors.hom.app K) ≫
      (R.factors n).hom.app
        (((coefficientRestriction (J := W.smallEtaleTopology) O t h).mapHomologicalComplex
          (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (R.ordinaryRestriction h) (.up ℤ)).hom.app K)

private def brown_underlying_scalar_coherence
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t)
    (R : StrictEtaleBrownRealizationData O t W P) : Prop :=
  ∀ {m n : ℕ} (h : m ≤ n),
    (mateEquiv (P.scalar h).derivedAdj
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h)))
      (.mk _ _ _ _ (R.scalar h).inv)) = (R.restriction h).hom

set_option profiler true in
private theorem brown_underlying_coherence_iff
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t)
    (R : StrictEtaleBrownRealizationData O t W P) :
    StrictEtaleBrownRealizationCoherence O t W P R ↔
      brown_underlying_restriction_coherence O t W P R ∧
      brown_underlying_localization_coherence O t W P R ∧
      brown_underlying_scalar_coherence O t W P R := Iff.rfl

set_option profiler true in
private theorem brown_underlying_restriction_section
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t)
    (R : StrictEtaleBrownRealization O t W P) :
    brown_underlying_restriction_coherence O t W P R.val :=
  ((brown_underlying_coherence_iff O t W P R.val).mp R.property).1

private theorem brown_underlying_right_section
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (r : StrictEtaleBrownImageRealization O t g n A (B.level n) RV RW) :
    ∀ (M : strictEtaleLevel V O t n) (U : W.Etaleᵒᵖ)
      (x : ((A.right n).obj M).val.obj U),
      ((r.val.ordinaryRight.hom.app M).hom.app U x) =
        ((A.rightUnderlying n).hom.app M).hom.app U x :=
  r.property.1

-- Check the section calculation independently of the derived assembly.
set_option profiler true in
/-- The ordinary Brown restriction/image cube, before deriving.
Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 03CV and 03CZ.
(blueprint: lem-pur-brown-ordinary-restriction-cube).
Proof: transpose the inverse-image restriction square using the two ordinary
adjunctions. The underlying-set Hom formulas identify its transpose with the
set-sheaf direct-image restriction identity. Evaluate at an etale object and a
section; the Brown image section equations and the scalar restriction section
equations identify the two routes. No properness or finite-coefficient hypothesis
is used, including for identity coefficient transitions and the zero ring. -/
theorem etaleBrownOrdinaryRestrictionCube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ n, StrictEtaleBrownImageRealization O t g n A (B.level n) RV RW)
    {m n : ℕ} (h : m ≤ n) (M : strictEtaleLevel V O t m) :
      (RW.val.ordinaryRestriction h).hom.app ((A.right m).obj M) ≫
          (Functor.whiskerRight (rg m).val.ordinaryRight.hom (Sheaf.restrictScalars
      W.smallEtaleTopology (strictEtaleBrownRingMap O t h)) ≫
            Functor.whiskerLeft (strictEtaleBrownConstant O t V m)
      (Etale.lowerStarRestrictScalarsIso (strictEtaleBrownRingMap O t h) g).hom).app M =
        (Functor.whiskerRight ((mateEquiv (A.levelAdj m) (A.levelAdj n) (.mk _ _ _ _
      (A.restrictInverse h).hom))) (strictEtaleBrownConstant O t W n) ≫
          Functor.whiskerLeft (coefficientRestriction.{u + 1, u, u + 1} (J := V.smallEtaleTopology)
      O t h) (rg n).val.ordinaryRight.hom).app M ≫
            (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).map
      ((RV.val.ordinaryRestriction h).hom.app M) := by
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Category.assoc, brownMateRestriction, coefficientRestriction,
    coefficientQuotientMap, strictEtaleBrownRingMap] using
    (brown_underlying_ordinary_cube (strictEtaleBrownRing O t n)
      (strictEtaleBrownRing O t m) (strictEtaleBrownRingMap O t h) g
      (A.right m) (A.right n)
      (mateEquiv (A.levelAdj m) (A.levelAdj n)
        (.mk _ _ _ _ (A.restrictInverse h).hom))
      (A.rightUnderlying m) (A.rightUnderlying n)
      (RW.val.ordinaryRestriction h) (RV.val.ordinaryRestriction h)
      (rg m).val.ordinaryRight (rg n).val.ordinaryRight
      (fun N ↦ brown_underlying_cube O t g A h N)
      (fun N U x ↦ brown_underlying_restriction_section O t W PW RW h N U x)
      (fun N U x ↦ brown_underlying_restriction_section O t V PV RV h N U x)
      (fun N U x ↦ brown_underlying_right_section O t g m A PW PV B RV RW (rg m) N U x)
      (fun N U x ↦ brown_underlying_right_section O t g n A PW PV B RV RW (rg n) N U x)
      M).symm

end AlgebraicGeometry
