/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedTransitionData
public import WeilConjectures.AlgebraicGeometry.Open.OpenScalarRestrictionUnit
public import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeOpenTransition
public import WeilConjectures.SmoothPurity.Compact.CompactSupportOpenScalarRestriction
public import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryOpenTransition

/-! # The normalized transition of one geometric operation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpShriekTransition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local irreducible] scalarCoordinates quotientMap
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

attribute [-instance] CategoryTheory.catToReflQuiver in
end AlgebraicGeometry.ProEtale.SpShriekTransition

private def transportTransition
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : C ⥤ E} {R R' : E ⥤ D}
    (t : F ⟶ G ⋙ R) (q : R ≅ R') : F ⟶ G ⋙ R' :=
  t ≫ Functor.whiskerLeft G q.hom

private theorem transportTransition_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : C ⥤ E} {R R' : E ⥤ D}
    (t : F ⟶ G ⋙ R) (q : R ≅ R') (X : C) :
    (transportTransition t q).app X = t.app X ≫ q.hom.app (G.obj X) := by
  rfl

private theorem coordinateTranspose
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (q : R ≅ R')
    {X : C} {Y : D} (t : X ⟶ R.obj Y) :
    b.homEquiv _ _
        ((a.leftAdjointUniq (b.ofNatIsoRight q.symm)).inv.app X ≫
          (a.homEquiv _ _).symm t) = t ≫ q.hom.app Y := by
  have h := leftAdjointUniq_homEquiv_comp (b.ofNatIsoRight q.symm) a X Y
    ((a.homEquiv _ _).symm t)
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_ofNatIsoRight_apply] at h
  apply (cancel_mono (q.inv.app Y)).mp
  simpa only [Adjunction.leftAdjointUniq_inv_app, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id] using h

private theorem pullMate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : B ⥤ A} {F' : C ⥤ D} {G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (p : C ⥤ A) (q : D ⥤ B)
    (d : G' ⋙ p ≅ q ⋙ G) {K : A} {N : C}
    (f : F.obj K ⟶ q.obj (F'.obj N)) (t : K ⟶ p.obj N)
    (hf : a.homEquiv _ _ f =
      t ≫ p.map (b.unit.app N) ≫ d.hom.app (F'.obj N)) :
    f = F.map t ≫ ((mateEquiv b a).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans.app N := by
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  simp only [Adjunction.homEquiv_unit]
  have hc := unit_mateEquiv_symm b a (TwoSquare.mk _ _ _ _ d.hom) N
  dsimp only [Functor.id_obj] at hc
  erw [← hc]
  simpa only [Adjunction.homEquiv_unit] using hf

private theorem scalarOpenMate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {LA : A ⥤ B} {RA : B ⥤ A} {LB : C ⥤ D} {RB : D ⥤ C}
    {SX : B ⥤ D} {RX : D ⥤ B} {SU : A ⥤ C} {RU : C ⥤ A}
    (a : LA ⊣ RA) (b : LB ⊣ RB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : RB ⋙ RU ≅ RX ⋙ RA) (c : RU ⋙ LA ⟶ LB ⋙ RX)
    (hc : ∀ N, a.unit.app (RU.obj N) ≫ RA.map (c.app N) ≫
      q.inv.app (LB.obj N) = RU.map (b.unit.app N))
    (K : A) (N : C) (f : SU.obj K ⟶ N) :
    x.homEquiv _ _
        (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).hom.app K ≫
          LB.map f) = LA.map (u.homEquiv _ _ f) ≫ c.app N := by
  dsimp only [Functor.comp_obj] at *
  apply (a.homEquiv _ _).injective
  have ht := leftAdjointUniq_homEquiv_comp (a.comp x)
    ((u.comp b).ofNatIsoRight q) K _ (LB.map f)
  rw [Adjunction.comp_homEquiv] at ht
  change a.homEquiv _ _ (x.homEquiv _ _ _) = _ at ht
  rw [ht, Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [Adjunction.comp_homEquiv]
  change u.homEquiv _ _ (b.homEquiv _ _ _) ≫ _ = _
  have hb : b.homEquiv _ _ (LB.map f) = f ≫ b.unit.app N := by
    rw [Adjunction.homEquiv_unit]
    simpa only [Functor.id_map, Functor.comp_map] using (b.unit.naturality f).symm
  rw [hb, u.homEquiv_naturality_right, a.homEquiv_naturality_left]
  have hc' : a.homEquiv (RU.obj N) (RX.obj (LB.obj N)) (c.app N) =
      RU.map (b.unit.app N) ≫ q.hom.app (LB.obj N) := by
    apply (cancel_mono (q.inv.app (LB.obj N))).mp
    simpa only [Adjunction.homEquiv_unit, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id, Functor.comp_obj] using hc N
  rw [hc', Category.assoc]

private theorem transportedLeftUniq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {LA LA' : A ⥤ B} {RA : B ⥤ A} {LB LB' : C ⥤ D} {RB : D ⥤ C}
    {SX : B ⥤ D} {RX : D ⥤ B} {SU : A ⥤ C} {RU : C ⥤ A}
    (a : LA ⊣ RA) (b : LB ⊣ RB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : RB ⋙ RU ≅ RX ⋙ RA) (rA : LA' ≅ LA) (rB : LB' ≅ LB) :
    Functor.isoWhiskerRight rA SX ≪≫
        (a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q) ≪≫
        Functor.isoWhiskerLeft SU rB.symm =
      ((a.ofNatIsoLeft rA.symm).comp x).leftAdjointUniq
        ((u.comp (b.ofNatIsoLeft rB.symm)).ofNatIsoRight q) := by
  apply Iso.ext
  ext K
  apply (((a.ofNatIsoLeft rA.symm).comp x).homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom]
  rw [Adjunction.comp_homEquiv]
  change (a.ofNatIsoLeft rA.symm).homEquiv _ _ (x.homEquiv _ _ _) = _
  rw [x.homEquiv_naturality_left,
    Adjunction.homEquiv_ofNatIsoLeft_apply]
  simp only [Iso.symm_hom, Functor.comp_obj, Iso.inv_hom_id_app_assoc]
  have ht := leftAdjointUniq_homEquiv_comp (a.comp x)
    ((u.comp b).ofNatIsoRight q) K _ (rB.inv.app (SU.obj K))
  rw [Adjunction.comp_homEquiv] at ht
  change a.homEquiv _ _ (x.homEquiv _ _ _) = _ at ht
  rw [ht, Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [Adjunction.comp_homEquiv]
  change u.homEquiv _ _ (b.homEquiv _ _ (rB.inv.app (SU.obj K))) ≫ _ = _
  simp only [Adjunction.homEquiv_unit, Adjunction.ofNatIsoRight_unit,
    Adjunction.comp_unit_app, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Functor.map_comp, Category.assoc, Functor.comp_obj]

/-- Open extension carries the actual reduction to its normalized open scalar word.
Source: blueprint integral-adjunction direct-image paragraph (1), step 2;
Stacks 03DI and 06YY; Zheng 4.1.
Proof: use the ordinary open adjunction and its evaluated units/counits to identify
extension of the strict transition with the coefficient-restriction square. Derive
the square termwise, since both open extension and restriction are exact. Transpose
under scalar adjunction. The normalized open units and uniqueness of composite left
adjoints identify this comparison with reductionOpenScalarIso. The scalar coordinate
maps preserve the units, and substitution gives the equality. Zero and empty opens,
equal indices, and noninvertible input transitions obey the same calculation.
(blueprint: lem-sp-normalized-open-transition). -/
theorem normalized_open_transition (b : SpTowerShriek.Base l E)
    {U T : Scheme.{u}} {j : U ⟶ T} [IsOpenImmersion j]
    {g : SpTowerShriek.Geometry l E b j} (a : SpTowerShriek.Open l E b j g)
    {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.D l E U) :
    rho l E b T h ((SpTowerShriek.openD l E b a).obj M) ≫
        (SpTowerShriek.openEvaluation l E b a m).hom.app M =
      (scalarExtensionFunctor (quotientMap l E h) T).map
          ((SpTowerShriek.openEvaluation l E b a n).hom.app M) ≫
        (reductionOpenScalarIso (quotientMap l E h) j).hom.app
          ((SpTowerShriek.Ev l E U n).obj M) ≫
        (sfIntrinsicDerivedOpen (SpTowerShriek.R l E m) j).map (rho l E b U h M) := by
  apply ((proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := T) (quotientMap l E h))).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, rho_transpose]
  erw [Adjunction.homEquiv_naturality_left]
  erw [reductionOpenScalar_transpose]
  rw [rho_transpose]
  have htransport := derivedOpenTransition l E b a h M
  run_tac transportInstances `htransport

private theorem reductionOpenScalar_transpose
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : proEtaleDerivedCategory U A) (N : proEtaleDerivedCategory U B)
    (f : (scalarExtensionFunctor φ U).obj K ⟶ N) :
    (proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := T) φ)).homEquiv _ _
        ((reductionOpenScalarIso φ j).hom.app K ≫
          (sfIntrinsicDerivedOpen B j).map f) =
      (sfIntrinsicDerivedOpen A j).map
          ((proEtaleRingDerivedExtensionAdjunction
            (proEtaleConstantRingMap (T := U) φ)).homEquiv _ _ f) ≫
        (sfOpenRestrictionDerived j φ).hom.app N := by
  let a := OpenScalarTensor.openAdj A j
  let b := OpenScalarTensor.openAdj B j
  let x := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)
  let u := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := U) φ)
  let q := OpenScalarTensor.rightSquare φ j
  have he := transportedLeftUniq a b x u q (reductionOpenModel A j) (reductionOpenModel B j)
  have hm := scalarOpenMate
    (a.ofNatIsoLeft (reductionOpenModel A j).symm)
    (b.ofNatIsoLeft (reductionOpenModel B j).symm) x u q
    (sfOpenRestrictionDerived j φ).hom (openScalarRestrictionUnit φ j) K N f
  rw [← he] at hm
  exact hm

private theorem rho_transpose (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.D l E T) :
    (proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := T) (quotientMap l E h))).homEquiv _ _
        (rho l E b T h M) = (strictTransition l E T h).app M := by
  rw [strictTransition_eq]
  have htransport :=
    (coordinateReduction_transpose ((b.calculus T).scalar h).adjunction
      (proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := T) (quotientMap l E h)))
      (eqToIso (congrArg (fun φ ↦ SemilinearSections.resD φ) (coefficientMap_eq l E T h)))
      ((SemilinearSections.derivedTransition (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app M))
  simp only [rho, scalarCoordinates_eq, reduction_eq]
  run_tac transportInstances `htransport

private theorem strictTransition_eq (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    (M : SpTowerShriek.D l E T) :
    (strictTransition l E T h).app M =
      (SemilinearSections.derivedTransition (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app M ≫
      (eqToIso (congrArg (fun φ ↦ SemilinearSections.resD φ)
        (coefficientMap_eq l E T h))).hom.app ((SpTowerShriek.Ev l E T m).obj M) := by
  have htransport := transportTransition_app
    (G := SpTowerShriek.Ev l E T m)
    (SemilinearSections.derivedTransition (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)
    (eqToIso (congrArg (fun φ ↦ SemilinearSections.resD φ)
      (coefficientMap_eq l E T h))) M
  dsimp only [strictTransition]
  run_tac transportInstances `htransport

private theorem coordinateReduction_transpose
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (q : R ≅ R')
    {X : C} {Y : D} (t : X ⟶ R.obj Y) :
    b.homEquiv _ _
        (coordinateReduction (a.leftAdjointUniq (b.ofNatIsoRight q.symm))
          ((a.homEquiv _ _).symm t)) = t ≫ q.hom.app Y :=
  coordinateTranspose a b q t

private theorem reduction_eq (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.D l E T) :
    SemilinearSections.reduction (ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T) h ((b.calculus T).scalar h) M =
      (((b.calculus T).scalar h).adjunction.homEquiv _ _).symm
        ((SemilinearSections.derivedTransition (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app M) := by
  rfl

private theorem scalarCoordinates_eq (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {m n : ℕ} (h : m ≤ n) :
    scalarCoordinates l E b T h =
      ((b.calculus T).scalar h).adjunction.leftAdjointUniq
        ((proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := T) (quotientMap l E h))).ofNatIsoRight
          (eqToIso (congrArg (fun φ ↦ SemilinearSections.resD φ)
            (coefficientMap_eq l E T h))).symm) := by
  unfold scalarCoordinates; rfl

private theorem derivedOpenTransition (b : SpTowerShriek.Base l E)
    {U T : Scheme.{u}} {j : U ⟶ T} [IsOpenImmersion j]
    {g : SpTowerShriek.Geometry l E b j} (a : SpTowerShriek.Open l E b j g)
    {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.D l E U) :
    (strictTransition l E T h).app ((SpTowerShriek.openD l E b a).obj M) ≫
        (scalarRestriction (quotientMap l E h) T).map
          ((SpTowerShriek.openEvaluation l E b a m).hom.app M) =
      (SpTowerShriek.openEvaluation l E b a n).hom.app M ≫
        (sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) j).map
          ((strictTransition l E U h).app M) ≫
        (sfOpenRestrictionDerived j (quotientMap l E h)).hom.app
          ((SpTowerShriek.Ev l E U m).obj M) := by
  have htransport := localizeOpenTransition a.extension
    (SpTowerShriek.ev l E U n) (SpTowerShriek.ev l E U m)
    (SpTowerShriek.ev l E T n) (SpTowerShriek.ev l E T m)
    (sfIntrinsicExtensionByZero j (SpTowerShriek.R l E n))
    (sfIntrinsicExtensionByZero j (SpTowerShriek.R l E m))
    (proEtaleCoefficientRestrictScalars U (quotientMap l E h))
    (proEtaleCoefficientRestrictScalars T (quotientMap l E h))
    (a.evaluation n) (a.evaluation m) (sfOpenRestriction j (quotientMap l E h))
    (ordinaryTransition l E U h) (ordinaryTransition l E T h)
    (strictTransition l E U h) (strictTransition l E T h)
    (fun K ↦ by
      have hfactor := strictTransition_fac l E U h K
      run_tac transportInstances `hfactor)
    (fun K ↦ by
      have hfactor := strictTransition_fac l E T h K
      run_tac transportInstances `hfactor)
    (ordinaryOpenTransition l E b a h) M
  run_tac transportInstances `htransport

private theorem strictTransition_fac (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    (K : CochainComplex (SpTowerShriek.S l E T) ℤ) :
    (strictTransition l E T h).app (DerivedCategory.Q.obj K) ≫
      (scalarRestriction (quotientMap l E h) T).map
        ((SpTowerShriek.ev l E T m).mapDerivedCategoryFactors.hom.app K) ≫
      (proEtaleCoefficientRestrictScalars T (quotientMap l E h)).mapDerivedCategoryFactors.hom.app
        (((SpTowerShriek.ev l E T m).mapHomologicalComplex (.up ℤ)).obj K) =
    (SpTowerShriek.ev l E T n).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (ordinaryTransition l E T h) (.up ℤ)).app K) := by
  have htransport := transportTransition_fac T (coefficientMap_eq l E T h)
    (SpTowerShriek.ev l E T n) (SpTowerShriek.ev l E T m)
    (SemilinearSections.transition (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)
    (SemilinearSections.derivedTransition (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)
    (fun L ↦ by
      have hfactor := genericTransition_fac l E T h L
      run_tac transportInstances `hfactor) K
  dsimp only [strictTransition]
  run_tac transportInstances `htransport

private theorem transportTransition_fac
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {φ ψ : R ⟶ S} (hφ : φ = ψ)
    (F₀ : C ⥤ SemilinearSections.Mod (ProEt.topology T) R)
    (F₁ : C ⥤ SemilinearSections.Mod (ProEt.topology T) S)
    [F₀.Additive] [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    (t : F₀ ⟶ F₁ ⋙ SemilinearSections.res φ)
    (d : F₀.mapDerivedCategory ⟶ F₁.mapDerivedCategory ⋙ SemilinearSections.resD φ)
    (hd : ∀ K : CochainComplex C ℤ,
      d.app (DerivedCategory.Q.obj K) ≫
        (SemilinearSections.resD φ).map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        (SemilinearSections.res φ).mapDerivedCategoryFactors.hom.app
          ((F₁.mapHomologicalComplex (.up ℤ)).obj K) =
      F₀.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K))
    (K : CochainComplex C ℤ) :
    (transportTransition d
        (eqToIso (congrArg (fun a ↦ SemilinearSections.resD a) hφ))).app
          (DerivedCategory.Q.obj K) ≫
        (SemilinearSections.resD ψ).map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        (SemilinearSections.res ψ).mapDerivedCategoryFactors.hom.app
          ((F₁.mapHomologicalComplex (.up ℤ)).obj K) =
      F₀.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (t ≫ Functor.whiskerLeft F₁
          (eqToHom (congrArg (fun a ↦ SemilinearSections.res a) hφ))) (.up ℤ)).app K) := by
  cases hφ
  simpa only [transportTransition, eqToIso_refl, Iso.refl_hom, eqToHom_refl,
    Functor.whiskerLeft_id', Category.comp_id] using hd K

private theorem genericTransition_fac (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    (K : CochainComplex (SpTowerShriek.S l E T) ℤ) :
    (SemilinearSections.derivedTransition (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app
        (DerivedCategory.Q.obj K) ≫
      (SemilinearSections.resD (SemilinearSections.coefficientMap (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)).map
        ((SpTowerShriek.ev l E T m).mapDerivedCategoryFactors.hom.app K) ≫
      (SemilinearSections.res (SemilinearSections.coefficientMap (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)).mapDerivedCategoryFactors.hom.app
        (((SpTowerShriek.ev l E T m).mapHomologicalComplex (.up ℤ)).obj K) =
    (SpTowerShriek.ev l E T n).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (SemilinearSections.transition (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h) (.up ℤ)).app K) := by
  dsimp only [SemilinearSections.derivedTransition, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Localization.liftNatTrans_app]
  simp only [Category.assoc]
  change _ ≫ _ ≫
    ((SpTowerShriek.ev l E T m ⋙ SemilinearSections.res
      (SemilinearSections.coefficientMap (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)).mapDerivedCategoryFactors).inv.app K ≫
      _ = _
  simp only [Iso.inv_hom_id_app, Category.comp_id]
  rfl

private meta def transportInstances (userName : Name) : TacticM Unit :=
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let ds := (← getLCtx).decls.toList.filterMap id
    let some d := ds.find? (fun d ↦ d.userName.eraseMacroScopes == userName)
      | throwError "no comparison named {userName}"
    let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
    let q ← instanceCongr cache true 500 target (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf

private meta def instanceCongr
    (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr))
    (norm : Bool) : Nat → Expr → Expr → MetaM Expr
  | 0, _, _ => throwError "instance congruence depth exhausted"
  | fuel + 1, a, b => do
    let a := (← instantiateMVars a).headBeta.consumeMData
    let b := (← instantiateMVars b).headBeta.consumeMData
    let entries ← cache.get
    if let some h := entries[(a, b)]? then return h
    let h ← do
      if a == b then return ← mkHEqRefl a
      if ← isProp (← inferType a) then
        return ← mkAppM ``instanceProofsHEq #[a, b]
      if let .letE _ _ val body _ := a then
        return ← instanceCongr cache norm fuel (body.instantiate1 val) b
      if let .letE _ _ val body _ := b then
        return ← instanceCongr cache norm fuel a (body.instantiate1 val)
      if a.isFVar then
        if let some val := ((← getLCtx).get! a.fvarId!).value? then
          return ← instanceCongr cache norm fuel val b
      if b.isFVar then
        if let some val := ((← getLCtx).get! b.fvarId!).value? then
          return ← instanceCongr cache norm fuel a val
      let af := a.getAppFn
      let bf := b.getAppFn
      if af.isMData then
        return ← instanceCongr cache norm fuel (mkAppN af.consumeMData a.getAppArgs) b
      if bf.isMData then
        return ← instanceCongr cache norm fuel a (mkAppN bf.consumeMData b.getAppArgs)
      if norm then
        let a' ← nameCoordinateProjection a
        let b' ← nameCoordinateProjection b
        if a' != a || b' != b then return ← instanceCongr cache norm fuel a' b'
        let a' ← reduceCoordinateObject 30 a
        let b' ← reduceCoordinateObject 30 b
        if a' != a || b' != b then return ← instanceCongr cache norm fuel a' b'
      let sharedType := af.isConstOf ``DerivedCategory ||
        af.isConstOf ``instCategoryDerivedCategory || af.isConstOf ``Sheaf ||
        af.isConstOf ``ObjectProperty.FullSubcategory.category ||
        af.isConstOf ``Functor.category || af.isConstOf ``CategoryTheory.Functor ||
        af.isConstOf ``HasDerivedCategory.ofIsGrothendieckAbelian
      if sharedType then
        if ← withReducible (isDefEq a b) then return ← mkHEqRefl a
      if af == bf && a.getAppArgs.size == b.getAppArgs.size then
        let aa := a.getAppArgs
        let bb := b.getAppArgs
        let ct ← mkHCongrWithArity af aa.size
        let cp ← mkAuxTheorem ct.type ct.proof (zetaDelta := true)
        let mut ps := #[]
        for i in [:aa.size] do
          let mut h ← instanceCongr cache norm fuel aa[i]! bb[i]!
          if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
          ps := ps ++ #[aa[i]!, bb[i]!, h]
        let pf := mkAppN cp ps
        if (← inferType pf).isHEq then return pf
        return ← mkAppM ``heq_of_eq #[pf]
      if af != bf then
        if af.isConstOf ``AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory ||
            af.isConstOf ``AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory ||
            af.isConstOf ``SemilinearSections.hasDerived ||
            af.isConstOf ``SemilinearSections.moduleAbelian ||
            af.isConstOf ``proEtaleCoefficientRestrictScalars ||
            af.isConstOf ``proEtaleRingRestrictScalars ||
            af.isConstOf ``SemilinearSections.res ||
            af.isConstOf ``SemilinearSections.resD ||
            af.isConstOf ``scalarRestriction ||
            af.isConstOf ``SpTowerShriek.Ev ||
            af.isConstOf ``SpTowerShriek.ev ||
            af.isConstOf ``SemilinearSections.e ||
            af.isConstOf ``SpTowerShriek.openD ||
            af.isConstOf ``SpTowerShriek.openEvaluation ||
            af.isConstOf ``sfIntrinsicDerivedOpen ||
            af.isConstOf ``sfOpenRestrictionDerived ||
            af.isConstOf ``Functor.mapDerivedCategorySquareIso ||
            af.isConstOf ``ordinaryTransition ||
            af.isConstOf ``strictTransition ||
            af.isConstOf ``transportTransition ||
            af.isConstOf ``proEtaleConstantRingMap ||
            af.isConstOf ``ProjectionRestriction.derived ||
            af.isConstOf ``AlgebraicGeometry.ProEtale.scalarExtensionFunctor ||
            af.isConstOf ``SemilinearSections.DS ||
            af.isConstOf ``SemilinearSections.D ||
            af.isConstOf ``SemilinearSections.Mod ||
            af.isConstOf ``SheafOfModules.instPreadditive then
          if let some a' ← withDefault <| unfoldDefinition? a then
            return ← instanceCongr cache norm fuel a' b
        if bf.isConstOf ``AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory ||
            bf.isConstOf ``AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory ||
            bf.isConstOf ``SemilinearSections.hasDerived ||
            bf.isConstOf ``SemilinearSections.moduleAbelian ||
            bf.isConstOf ``proEtaleCoefficientRestrictScalars ||
            bf.isConstOf ``proEtaleRingRestrictScalars ||
            bf.isConstOf ``SemilinearSections.res ||
            bf.isConstOf ``SemilinearSections.resD ||
            bf.isConstOf ``scalarRestriction ||
            bf.isConstOf ``SpTowerShriek.Ev ||
            bf.isConstOf ``SpTowerShriek.ev ||
            bf.isConstOf ``SemilinearSections.e ||
            bf.isConstOf ``SpTowerShriek.openD ||
            bf.isConstOf ``SpTowerShriek.openEvaluation ||
            bf.isConstOf ``sfIntrinsicDerivedOpen ||
            bf.isConstOf ``sfOpenRestrictionDerived ||
            bf.isConstOf ``Functor.mapDerivedCategorySquareIso ||
            bf.isConstOf ``ordinaryTransition ||
            bf.isConstOf ``strictTransition ||
            bf.isConstOf ``transportTransition ||
            bf.isConstOf ``proEtaleConstantRingMap ||
            bf.isConstOf ``ProjectionRestriction.derived ||
            bf.isConstOf ``AlgebraicGeometry.ProEtale.scalarExtensionFunctor ||
            bf.isConstOf ``SemilinearSections.DS ||
            bf.isConstOf ``SemilinearSections.D ||
            bf.isConstOf ``SemilinearSections.Mod ||
            bf.isConstOf ``SheafOfModules.instPreadditive then
          if let some b' ← withDefault <| unfoldDefinition? b then
            return ← instanceCongr cache norm fuel a b'
      if af.isConstOf ``CommRing.toRing || bf.isConstOf ``CommRing.toRing then
        unless ← isDefEq a b do throwError "coefficient rings differ"
        return ← mkHEqRefl a
      if ← withReducible (isDefEq a b) then return ← mkHEqRefl a
      throwError "unmatched instance data: {a} versus {b}"
    cache.modify (·.insert (a, b) h)
    return h

private meta def reduceCoordinateObject : Nat → Expr → MetaM Expr
  | 0, e => pure e
  | fuel + 1, e => do
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``Functor.obj && args.size == 6 then
      let f := args[4]!
      let h := f.getAppFn
      if h.isConstOf ``Functor.comp || h.isConstOf ``ObjectProperty.ι ||
          h.isConstOf ``ObjectProperty.lift || h.isConstOf ``Functor.id then
        if let some f' ← withDefault <| unfoldDefinition? f then
          let e' ← whnfCore (mkApp (.proj ``CategoryTheory.Functor 0 f') args[5]!)
          return ← reduceCoordinateObject fuel (← nameCoordinateProjection e')
    if fn.isConstOf ``ObjectProperty.FullSubcategory.obj then
      let arg := args.back!
      let arg' ← reduceCoordinateObject fuel (← nameCoordinateProjection arg)
      if arg' != arg then
        let e' := mkAppN fn (args.set! (args.size - 1) arg')
        if let some e'' ← withDefault <| unfoldDefinition? e' then
          return ← reduceCoordinateObject fuel (← whnfCore e'')
      if let some e' ← Lean.Expr.reduceProjStruct? e then return e'
    return e

private meta def nameCoordinateProjection (e : Expr) : MetaM Expr := do
  if e.getAppFn.isConstOf ``Abelian.toPreadditive then
    return ← withDefault <| whnf e
  let .proj n i f := e.getAppFn | return e
  if n == ``Abelian then return ← withDefault <| whnf e
  let name := if n == ``CategoryTheory.Functor then
      if i == 0 then ``Functor.obj else ``Functor.map
    else if n == ``Iso then if i == 0 then ``Iso.hom else ``Iso.inv
    else if n == ``NatTrans && i == 0 then ``NatTrans.app
    else if n == ``ObjectProperty.FullSubcategory && i == 0 then
      ``ObjectProperty.FullSubcategory.obj
    else if n == ``InducedCategory.Hom && i == 0 then ``InducedCategory.Hom.hom
    else Name.anonymous
  if name.isAnonymous then return e
  let ty ← inferType f
  let ty ← if ty.getAppFn.isConstOf n then pure ty else whnf ty
  let p := mkAppN (.const name ty.getAppFn.constLevels!) (ty.getAppArgs.push f)
  return mkAppN p e.getAppArgs

private theorem instanceProofsHEq {P Q : Prop} (p : P) (q : Q) : HEq p q := by
  have h : P = Q := propext ⟨fun _ ↦ q, fun _ ↦ p⟩
  cases h
  rfl

private def strictTransition (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    SpTowerShriek.Ev l E T n ⟶
      SpTowerShriek.Ev l E T m ⋙ scalarRestriction (quotientMap l E h) T :=
  transportTransition
    (G := SpTowerShriek.Ev l E T m)
    (SemilinearSections.derivedTransition (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)
    (eqToIso (congrArg (fun φ ↦ SemilinearSections.resD φ)
      (coefficientMap_eq l E T h)))

-- Explicit congruence transport follows TowerCompositorFiniteEvaluation; it keeps
-- proof-irrelevant instance changes outside the derived-functor implementations.

private theorem ordinaryOpenTransition (b : SpTowerShriek.Base l E)
    {U T : Scheme.{u}} {j : U ⟶ T} [IsOpenImmersion j]
    {g : SpTowerShriek.Geometry l E b j} (a : SpTowerShriek.Open l E b j g)
    {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.S l E U) :
    (ordinaryTransition l E T h).app (a.extension.obj M) ≫
        (proEtaleCoefficientRestrictScalars T (quotientMap l E h)).map
          ((a.evaluation m).hom.app M) =
      (a.evaluation n).hom.app M ≫
        (sfIntrinsicExtensionByZero j (SpTowerShriek.R l E n)).map
          ((ordinaryTransition l E U h).app M) ≫
        (sfOpenRestriction j (quotientMap l E h)).hom.app
          ((SpTowerShriek.ev l E U m).obj M) := by
  have he (k : ℕ) : a.ordinaryPullEvaluation k = g.ordinaryPullEvaluation k :=
    eq_of_heq ((a.ordinaryPullEvaluation_eq k).trans (g.ordinaryPullEvaluation_eq k).symm)
  have : IsIso (compactSupportScalarPullback j (quotientMap l E h)) :=
    compactSupportScalarPullback_isIso j (quotientMap l E h)
  apply horizontalOpenMate a.ordinaryAdjunction
    (SpTowerShriek.finiteOpenAdjunction l E b j n)
    (SpTowerShriek.finiteOpenAdjunction l E b j m)
    (SpTowerShriek.ev l E U n) (SpTowerShriek.ev l E U m)
    (SpTowerShriek.ev l E T n) (SpTowerShriek.ev l E T m)
    (proEtaleCoefficientRestrictScalars U (quotientMap l E h))
    (proEtaleCoefficientRestrictScalars T (quotientMap l E h))
    (g.ordinaryPullEvaluation n) (g.ordinaryPullEvaluation m)
    (a.evaluation n) (a.evaluation m)
    (ordinaryTransition l E U h) (ordinaryTransition l E T h)
    (compactSupportScalarPullback j (quotientMap l E h))
    (sfOpenRestriction j (quotientMap l E h)).hom ?_ ?_
    (ordinaryPullTransition l E b g h) ?_ M
  · intro N
    simpa only [he] using a.unit_evaluation n N
  · intro N
    simpa only [he] using a.unit_evaluation m N
  · exact ordinaryUnit (quotientMap l E h) j

private theorem ordinaryPullTransition (b : SpTowerShriek.Base l E)
    {U T : Scheme.{u}} {j : U ⟶ T} (g : SpTowerShriek.Geometry l E b j)
    {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.S l E T) :
    (ordinaryTransition l E U h).app (g.pull.obj M) ≫
        (proEtaleCoefficientRestrictScalars U (quotientMap l E h)).map
          ((g.ordinaryPullEvaluation m).hom.app M) =
      (g.ordinaryPullEvaluation n).hom.app M ≫
        (proEtaleConstantRingPullback (SpTowerShriek.R l E n) j).map
          ((ordinaryTransition l E T h).app M) ≫
        (compactSupportScalarPullback j (quotientMap l E h)).app
          ((SpTowerShriek.ev l E T m).obj M) := by
  apply pullSquareCore j (quotientMap l E h) g.pull
    (SpTowerShriek.ev l E T n) (SpTowerShriek.ev l E T m)
    (SpTowerShriek.ev l E U n) (SpTowerShriek.ev l E U m)
    (g.ordinaryPullEvaluation n) (g.ordinaryPullEvaluation m) _ _
    (coefficientMap_eq l E T h) (coefficientMap_eq l E U h) _ _ ?_ M
  intro N V x y hy
  have hu := g.ordinaryUnitTransition
  unfold SpTowerShriek.OrdinaryUnitTransition SpTowerShriek.OrdinaryUnitTransitionModel at hu
  exact hu N h V x y hy

private theorem pullSquareCore
    {C D : Type*} [Category C] [Category D]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {U T : Scheme.{u}} (j : U ⟶ T) (φ : A →+* B)
    (P : C ⥤ D)
    (F₀ : C ⥤ proEtaleRingModules T (proEtaleConstantRing T A))
    (F₁ : C ⥤ proEtaleRingModules T (proEtaleConstantRing T B))
    (E₀ : D ⥤ proEtaleRingModules U (proEtaleConstantRing U A))
    (E₁ : D ⥤ proEtaleRingModules U (proEtaleConstantRing U B))
    (en : P ⋙ E₀ ≅ F₀ ⋙ proEtaleConstantRingPullback A j)
    (em : P ⋙ E₁ ≅ F₁ ⋙ proEtaleConstantRingPullback B j)
    (φT : proEtaleConstantRing T A ⟶ proEtaleConstantRing T B)
    (φU : proEtaleConstantRing U A ⟶ proEtaleConstantRing U B)
    (hT : φT = proEtaleConstantRingMap (T := T) (φ))
    (hU : φU = proEtaleConstantRingMap (T := U) (φ))
    (tT : F₀ ⟶
      F₁ ⋙ SemilinearSections.res φT)
    (tU : E₀ ⟶
      E₁ ⋙ SemilinearSections.res φU)
    (hu : ∀ (M : C) (V : T.ProEtᵒᵖ)
      (x : ((F₀).obj M).val.obj V)
      (y : ((F₁).obj M).val.obj V),
      HEq ((tT.app M).val.app V x) y →
      HEq ((((proEtaleConstantRingAdjunction (A) j).homEquiv _ _)
        (en.inv.app M ≫ tU.app (P.obj M) ≫
          (SemilinearSections.res φU).map
            (em.hom.app M))).val.app V x)
        (((proEtaleConstantRingAdjunction (B) j).unit.app
          ((F₁).obj M)).val.app V y)) :
    let tT' := tT ≫ Functor.whiskerLeft _
      (eqToHom (congrArg (fun φ ↦ SemilinearSections.res φ) hT))
    let tU' := tU ≫ Functor.whiskerLeft _
      (eqToHom (congrArg (fun φ ↦ SemilinearSections.res φ) hU))
    ∀ M : C,
      tU'.app (P.obj M) ≫
          (proEtaleCoefficientRestrictScalars U (φ)).map
            (em.hom.app M) =
        en.hom.app M ≫
          (proEtaleConstantRingPullback (A) j).map (tT'.app M) ≫
          (compactSupportScalarPullback j (φ)).app
            ((F₁).obj M) := by
  subst φT
  subst φU
  dsimp only
  simp only [eqToHom_refl, Functor.whiskerLeft_app, NatTrans.comp_app,
    NatTrans.id_app]
  intro M
  rw [scalarPullback_eq]
  apply (cancel_epi (en.inv.app M)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [Category.comp_id, Category.id_comp]
  apply pullMate
    (proEtaleConstantRingAdjunction (A) j)
    (proEtaleConstantRingAdjunction (B) j)
    (SemilinearSections.res (proEtaleConstantRingMap (T := T) (φ)))
    (SemilinearSections.res (proEtaleConstantRingMap (T := U) (φ)))
    (compactSupportScalarDirectImage j (φ))
  ext V x
  have hh := hu M V x ((tT.app M).val.app V x) HEq.rfl
  change _ = ((compactSupportScalarDirectImage j (φ)).hom.app
    ((proEtaleConstantRingPullback (B) j).obj
      ((F₁).obj M))).val.app V
    (((proEtaleConstantRingAdjunction (B) j).unit.app
      ((F₁).obj M)).val.app V ((tT.app M).val.app V x))
  exact (eq_of_heq hh).trans (compactSupportScalarDirectImage_sections j (φ)
    ((proEtaleConstantRingPullback (B) j).obj
      ((F₁).obj M)) V
    (((proEtaleConstantRingAdjunction (B) j).unit.app
      ((F₁).obj M)).val.app V ((tT.app M).val.app V x))).symm

private theorem scalarPullback_eq
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {U T : Scheme.{u}} (j : U ⟶ T) (φ : A →+* B) :
    compactSupportScalarPullback j φ =
      ((mateEquiv (proEtaleConstantRingAdjunction B j)
        (proEtaleConstantRingAdjunction A j)).symm
        (compactSupportScalarDirectImage j φ).hom).natTrans := by
  rfl

private def ordinaryTransition (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    SpTowerShriek.ev l E T n ⟶ SpTowerShriek.ev l E T m ⋙
      proEtaleCoefficientRestrictScalars T (quotientMap l E h) :=
  SemilinearSections.transition (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h ≫
    Functor.whiskerLeft _ (eqToHom (congrArg
      (fun φ ↦ SemilinearSections.res φ) (coefficientMap_eq l E T h)))
