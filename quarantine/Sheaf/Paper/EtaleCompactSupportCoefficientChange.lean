/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.CompactSupportCoefficientChange
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleEssentiallySmall
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.Paper.EtaleDerivedScalarTensor
import Sheaf.Paper.EtaleProperCoefficientTensorUnit
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Ordinary-etale coefficient comparison for compact support

Source: Stacks Project, Tags 0GL5, 0GL6 and 07A6
(blueprint: lem-fix-compact-support-coefficient-change).
These are universal tensor presentations on the ordinary-etale site. The existing
pro-etale presentations and their normalized comparisons are imported unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The inverse mate of the canonical restriction/inverse-image identification on
sheaves. Source: Stacks Tags 03S2 and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change). -/
def coefficientRestrictionOpenMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars Z.smallEtaleTopology φ :=
  (mateEquiv (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).symm
      (asIso (upperStarRestrictScalars φ j).natTrans).inv

/-- The open coefficient mate is invertible. Source: Stacks Tags 03S2 and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: on the open both composites are the same module with restricted scalars;
off the open both are zero. The identity comparison has inverse the same identity.
Its transpose is the restriction/inverse-image identification, since both transposes
are the open unit. Thus it is the displayed mate, not an arbitrary isomorphism. -/
theorem coefficientRestrictionOpenMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso (coefficientRestrictionOpenMap φ j) := by
  have hopen (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      IsIso ((j)^*[ModuleCat.{u + 1} A].map
        ((coefficientRestrictionOpenMap φ j).app F)) := by
    have h := unit_mateEquiv_symm
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
      (asIso (upperStarRestrictScalars φ j).natTrans).inv F
    change _ = _ ≫ (j)^*[ModuleCat.{u + 1} A].map
      ((coefficientRestrictionOpenMap φ j).app F) at h
    dsimp only [Functor.id_obj] at h
    have hi : IsIso ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit.app
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj F) ≫
        (j)^*[ModuleCat.{u + 1} A].map
          ((coefficientRestrictionOpenMap φ j).app F)) := by
      rw [← h]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp hi
  have happ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      IsIso ((coefficientRestrictionOpenMap φ j).app F) := by
    refine Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦ ?_
    let t := Z.algClosurePoint x
    by_cases ht : t.base (IsLocalRing.closedPoint _) ∈ Set.range j.base
    · have h := isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map
        (ModuleCat.{u + 1} A) j _ (hopen F)
        (IsOpenImmersion.lift j t (Scheme.range_base_subset_of_closedPoint_mem t ht))
      rw [IsOpenImmersion.lift_fac] at h
      exact h
    · have hd : Disjoint (Set.range j.base) (Set.range t.base) := by
        rw [Set.disjoint_right]
        rintro _ ⟨p, rfl⟩
        simpa only [Subsingleton.elim p (IsLocalRing.closedPoint _)] using ht
      have h₁ := isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
        (ModuleCat.{u + 1} A) j t hd
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj F)
      have h₂ := ((Sheaf.restrictScalars _ φ).map_isZero
        (isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
          (ModuleCat.{u + 1} B) j t hd F)).of_iso
        ((asIso (upperStarRestrictScalars φ t).natTrans).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj F))
      have hi : IsIso ((t)^*[ModuleCat.{u + 1} A].map
          ((coefficientRestrictionOpenMap φ j).app F)) :=
        ⟨⟨h₂.to_ _, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
      have h := isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map
        (ModuleCat.{u + 1} A) t _ hi (𝟙 _)
      rw [Category.id_comp] at h
      exact h
  exact NatIso.isIso_of_isIso_app _

/-- The open restriction comparison descends termwise to bounded-below complexes.
Source: Stacks Tag 0GL6 (blueprint: lem-fix-compact-support-coefficient-change). -/
def coefficientRestrictionOpenPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  letI := coefficientRestrictionOpenMap_isIso φ j
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (asIso (coefficientRestrictionOpenMap φ j)) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The canonical proper/open scalar restriction comparison, with its direction
fixed by the open unit and the direct-image resolution map.
Source: Stacks Tag 0GL6 (blueprint: lem-fix-compact-support-coefficient-change). -/
def compactSupportCoefficientRestrictionPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c ≅
      rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B) c ⋙
        (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientRestrictionOpenPlus φ c.i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (rightDerivedLowerStarRestrictScalars φ c.g)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- A bounded-below presentation of the actual derived tensor, retaining its universal
arrow in the ambient derived category. Source: Stacks Tags 06YY and 07A6
(blueprint: lem-fix-compact-support-coefficient-change). -/
structure CoefficientTensorModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) where
  obj : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
  unit : K ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.obj obj
  universal : Sheaf.IsDerivedBaseChange unit.hom

set_option backward.isDefEq.respectTransparency false in
private theorem scalarExtension_plus_of_finiteTor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (K : DerivedCategoryModule A T) (a b : ℤ)
    (hK : DerivedCategory.hasTorAmplitudeIn A T a b K) :
    _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ T).obj K) := by
  refine ⟨a, (_root_.DerivedCategory.isGE_iff _ a).mpr fun q hq ↦ ?_⟩
  apply Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    (Sheaf.restrictScalars T.smallEtaleTopology φ)
  exact (hK (scalarCoefficientSheaf φ T) q (Or.inl hq)).of_iso
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso ((scalarTensorIso φ T).app K))

/-- Scalar extension of a morphism, uniquely specified by the universal arrows.
Source: Stacks Tag 07A6 (blueprint: lem-fix-compact-support-coefficient-change). -/
def CoefficientTensorModel.map
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B} {T : Scheme.{u}}
    {K L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ T K) (N : CoefficientTensorModel φ T L) (f : K ⟶ L) :
    M.obj ⟶ N.obj :=
  ObjectProperty.homMk ((Equiv.ofBijective _ (M.universal N.obj.obj)).symm
    (f.hom ≫ N.unit.hom))

/-- The canonical B-linear comparison is the unique arrow with the proper/open
restriction adjunct. Source: Stacks Tags 0GL5, 0GL6 and 07A6
(blueprint: lem-fix-compact-support-coefficient-change). -/
def compactSupportCoefficientComparisonPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj K)) :
    N.obj ⟶
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B) c).obj M.obj :=
  ObjectProperty.homMk ((Equiv.ofBijective _ (N.universal _)).symm
    (((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).map M.unit ≫
      (compactSupportCoefficientRestrictionPlus φ c).hom.app M.obj).hom))

set_option backward.isDefEq.respectTransparency false in
private theorem universal_open_transport
    {CA DA CB DB : Type*} [Category CA] [Category DA] [Category CB] [Category DB]
    {JA : CA ⥤ DA} {RA : DA ⥤ CA} {JB : CB ⥤ DB} {RB : DB ⥤ CB}
    (adjA : JA ⊣ RA) (adjB : JB ⊣ RB) (UX : CB ⥤ CA) (UZ : DB ⥤ DA)
    (c : UX ⋙ JA ≅ JB ⋙ UZ) (t : RB ⋙ UX ≅ UZ ⋙ RA)
    (hc : ∀ M, adjA.unit.app (UX.obj M) ≫ RA.map (c.hom.app M) =
      UX.map (adjB.unit.app M) ≫ t.hom.app (JB.obj M))
    {K : CA} {M : CB} (η : K ⟶ UX.obj M)
    (hη : ∀ N, Function.Bijective fun g : M ⟶ N ↦ η ≫ UX.map g) (N : DB) :
    Function.Bijective fun g : JB.obj M ⟶ N ↦
      JA.map η ≫ c.hom.app M ≫ UZ.map g := by
  have h := (adjA.homEquiv K (UZ.obj N)).symm.bijective.comp
    (((t.app N).homToEquiv (Z := K)).bijective.comp
      ((hη (RB.obj N)).comp (adjB.homEquiv M N).bijective))
  convert h using 1
  funext g
  change JA.map η ≫ c.hom.app M ≫ UZ.map g =
    (adjA.homEquiv K (UZ.obj N)).symm
      ((η ≫ UX.map ((adjB.homEquiv M N) g)) ≫ (t.app N).hom)
  apply (adjA.homEquiv K (UZ.obj N)).injective
  rw [Equiv.apply_symm_apply]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (adjA.unit.naturality η), reassoc_of% hc M]
  have hn := t.hom.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem openTensorUnit_universal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K) :
    Sheaf.IsDerivedBaseChange
      (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.map M.unit ≫
        (coefficientRestrictionOpenPlus φ j).hom.app M.obj).hom) := by
  have := coefficientRestrictionOpenMap_isIso φ j
  let β := asIso (coefficientRestrictionOpenMap φ j)
  let τ := (asIso (upperStarRestrictScalars φ j).natTrans).symm
  have hc (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj F) ≫
        (upperStar (ModuleCat.{u + 1} A) j).map (β.hom.app F) =
      (Sheaf.restrictScalars X.smallEtaleTopology φ).map
          ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).unit.app F) ≫
        τ.hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj F) := by
    exact (unit_mateEquiv_symm
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j) τ.hom F).symm
  have hd := Adjunction.mapDerivedCategoryAdjunction_mate
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j) τ β hc
  intro N
  have h := universal_open_transport
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
    (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
    (Functor.mapDerivedCategorySquareIso β) (Functor.mapDerivedCategorySquareIso τ)
    hd M.unit.hom M.universal N
  have he : _root_.DerivedCategory.Plus.ι.map
      ((coefficientRestrictionOpenPlus φ j).hom.app M.obj) =
      (Functor.mapDerivedCategorySquareIso β).hom.app M.obj.obj := by
    have hcomp : _root_.DerivedCategory.Plus.ι.mapIso
        (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusCompIso
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)).app M.obj) =
        (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryCompIso
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)).app M.obj.obj) := by
      apply Iso.ext
      exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app _ _ _
    simp only [coefficientRestrictionOpenPlus, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.map_comp]
    have hinv := congrArg Iso.inv hcomp
    change _root_.DerivedCategory.Plus.ι.map
        (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusCompIso
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)).inv.app M.obj) =
        (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryCompIso
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)).inv.app M.obj.obj) at hinv
    rw [hinv]
    simp only [Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app]
    rfl
  change Function.Bijective fun g ↦
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map M.unit.hom ≫
      _root_.DerivedCategory.Plus.ι.map
        ((coefficientRestrictionOpenPlus φ j).hom.app M.obj)) ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map g
  rw [he]
  convert h using 1
  funext g
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical ordinary-etale coefficient comparison is invertible for finite rings.
Source: Stacks Tags 0GL5 and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: write compact support as the proper direct image after open extension. The
open coefficient mate is an isomorphism by its unit normalization. For the proper
factor use the torsion-ring unbounded proper projection formula, applied to the
constant B-module; the canonical direct-image coefficient arrow is its counit mate.
The universal tensor bijections identify this B-linear composite with the displayed
comparison. Restricting back to the bounded-below full subcategory reflects its
invertibility. This is the ordinary-etale part of the coefficient-change argument. -/
theorem compactSupportCoefficientComparisonPlus_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {φ : A →+* B} {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    {f : X ⟶ Y} (c : Compactification f)
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj K)) :
    IsIso (compactSupportCoefficientComparisonPlus c M N) := by
  let η := (openImmersionLowerShriek (ModuleCat.{u + 1} A)
    c.i).mapDerivedCategoryPlus.map M.unit ≫
      (coefficientRestrictionOpenPlus φ c.i).hom.app M.obj
  have hη : Sheaf.IsDerivedBaseChange η.hom := openTensorUnit_universal c.i M
  have hp := properCoefficientTensorUnit_universal φ c.g η hη
  have htarget : Sheaf.IsDerivedBaseChange
      (((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).map M.unit ≫
        (compactSupportCoefficientRestrictionPlus φ c).hom.app M.obj).hom) := by
    simpa only [η, compactSupportCoefficientRestrictionPlus,
      rightDerivedLowerShriekOfCompactificationPlus,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Functor.map_comp,
      Functor.comp_map, Category.assoc] using hp
  have hfac := (Equiv.ofBijective _ (N.universal _)).apply_symm_apply
    (((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).map M.unit ≫
      (compactSupportCoefficientRestrictionPlus φ c).hom.app M.obj).hom)
  have : IsIso (_root_.DerivedCategory.Plus.ι.map
      (compactSupportCoefficientComparisonPlus c M N)) :=
    N.universal.isIso htarget (compactSupportCoefficientComparisonPlus c M N).hom hfac
  exact isIso_of_reflects_iso (compactSupportCoefficientComparisonPlus c M N)
    _root_.DerivedCategory.Plus.ι

set_option backward.isDefEq.respectTransparency false in
/-- Finite Tor amplitude ensures that reduction has a bounded tensor presentation;
no flatness of the coefficient map is assumed. Source: Stacks Tags 06YY and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: apply the finite-Tor interval to the constant sheaf B in degree zero.
The scalar/tensor isomorphism identifies its tensor with restriction of the chosen
scalar extension. Exact scalar restriction detects vanishing of homology, so the
scalar extension is bounded below. Package it in D+ with the scalar adjunction
unit. Its universal bijection is precisely the adjunction Hom equivalence. This
argument permits nonflat quotients and needs no choice of a flat representative. -/
theorem nonempty_coefficientTensorModel_of_finiteTor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m n : ℕ) (hn : 1 ≤ n) (hmn : n ≤ m)
    (T : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)))))
    (_hK : WeilConjectures.finiteTorConstructibleEtale l E m (hn.trans hmn) T K.obj) :
    Nonempty (CoefficientTensorModel
      (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal l E m)
        (T := Padic.coefficientExtensionIdeal l E n) (Ideal.pow_le_pow_right hmn))) T K) := by
  let φ := RingHom.ulift.{u + 1, u + 1, u, u} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E m)
    (T := Padic.coefficientExtensionIdeal l E n) (Ideal.pow_le_pow_right hmn))
  obtain ⟨a, b, _, ht⟩ := _hK.2
  let ad := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
  let L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))) :=
    ⟨(scalarExtension φ T).obj K.obj,
      scalarExtension_plus_of_finiteTor φ T K.obj a b ht⟩
  refine ⟨⟨L, ObjectProperty.homMk (ad.unit.app K.obj), ?_⟩⟩
  intro N
  convert (ad.homEquiv K.obj N).bijective using 1
  funext g
  exact (ad.homEquiv_unit K.obj N g).symm

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

private local instance fixedSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

set_option backward.isDefEq.respectTransparency false in
private theorem tensorModel_origin_of_scalar_plus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T : Scheme.{u}}
    (K₀ : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (h : _root_.DerivedCategory.TStructure.t.plus ((Etale.scalarExtension φ T).obj K₀.obj))
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))}
    (e : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K₀.obj ≅ K)
    (M : CoefficientTensorModel φ T K) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) T M.obj := by
  let := pbcRestriction_isRightAdjoint.{u} (Scheme.ProEt.topology T) φ
  let U := Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) φ
  let S := pbcFixedScalarExtension.{u} (Scheme.ProEt.topology T) φ
  let ad : S ⊣ U := Adjunction.ofIsRightAdjoint U
  have hu : Sheaf.IsDerivedBaseChange.{u} (J := Scheme.ProEt.topology T)
      (f := φ) (ad.unit.app K) := by
    intro N
    convert (ad.homEquiv K N).bijective using 1
    funext g
    exact (ad.homEquiv_unit K N g).symm
  let g := (ad.homEquiv K M.obj).symm M.unit
  have hg : ad.unit.app K ≫ U.map g = M.unit := by
    change ad.homEquiv K M.obj g = M.unit
    exact Equiv.apply_symm_apply _ _
  have : IsIso g := Sheaf.IsDerivedBaseChange.isIso.{u} hu M.universal g hg
  let i : (comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory.obj
      ((Etale.scalarExtension φ T).obj K₀.obj) ≅ M.obj :=
    (pbcComparisonReduction.{u} T φ).symm.app K₀.obj ≪≫ S.mapIso e ≪≫ asIso g
  exact (DerivedCategory.plusEtaleOrigin _ T).prop_of_iso i
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj h)

set_option backward.isDefEq.respectTransparency false in
/-- A universal tensor of a finite-Tor ordinary-etale realization remains bounded
below of etale origin, including for nonflat finite reduction.
Source: Stacks Tags 06YY and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: the finite-Tor interval and the scalar/tensor isomorphism make the chosen
ordinary-etale scalar extension bounded below. The canonical B-linear comparison
of scalar extension with site inverse image carries its realization to the chosen
pro-etale scalar extension of K, using the given origin isomorphism. The scalar
adjunction unit is universal. The unique map from that presentation to M preserves
the unit and is invertible by the two universal properties. Transporting the
bounded-below origin along the resulting isomorphism proves the claim. -/
theorem CoefficientTensorModel.origin_of_etale_finiteTor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m n : ℕ) (hn : 1 ≤ n) (hmn : n ≤ m)
    {T : Scheme.{u}}
    (K₀ : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)))))
    (_hK₀ : WeilConjectures.finiteTorConstructibleEtale l E m (hn.trans hmn) T K₀.obj)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))))}
    (_e : (comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))) T).mapDerivedCategory.obj K₀.obj ≅ K)
    (M : CoefficientTensorModel
      (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal l E m)
        (T := Padic.coefficientExtensionIdeal l E n) (Ideal.pow_le_pow_right hmn))) T K) :
    DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) T M.obj := by
  obtain ⟨a, b, _, ht⟩ := _hK₀.2
  exact tensorModel_origin_of_scalar_plus _ K₀
    (Etale.scalarExtension_plus_of_finiteTor _ T K₀.obj a b ht) _e M

end AlgebraicGeometry.ProEtale
