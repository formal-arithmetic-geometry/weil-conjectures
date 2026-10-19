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
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.Paper.ProperCoefficientUniversal
import Sheaf.Paper.WitnessCompatibility
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

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

private theorem universal_left_adjoint
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G : C ⥤ E} {H : D ⥤ F} (β : G ⋙ L₂ ≅ L₁ ⋙ H)
    (τ : R₁ ⋙ G ≅ H ⋙ R₂)
    (hβ : ∀ K, adj₂.unit.app (G.obj K) ≫ R₂.map (β.hom.app K) =
      G.map (adj₁.unit.app K) ≫ τ.hom.app (L₁.obj K))
    {K : E} {M : C} (η : K ⟶ G.obj M)
    (hη : ∀ N, Function.Bijective fun g : M ⟶ N ↦ η ≫ G.map g) :
    ∀ N, Function.Bijective fun g : L₁.obj M ⟶ N ↦
      (L₂.map η ≫ β.hom.app M) ≫ H.map g := by
  intro N
  let e := (adj₁.homEquiv M N).trans
    ((Equiv.ofBijective _ (hη (R₁.obj N))).trans
      (((τ.app N).homToEquiv).trans (adj₂.homEquiv K (H.obj N)).symm))
  convert e.bijective using 1
  ext g
  apply (adj₂.homEquiv K (H.obj N)).injective
  dsimp [e]
  simp only [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% (adj₂.unit_naturality η), reassoc_of% (hβ M)]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ η ≫ G.map (adj₁.unit.app M) ≫ k) (τ.hom.naturality g).symm


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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientRestrictionOpen_universal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    {M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    (η : K ⟶ (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj M)
    (hη : Sheaf.IsDerivedBaseChange η.hom) :
    Sheaf.IsDerivedBaseChange
      (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.map η ≫
        (coefficientRestrictionOpenPlus φ j).hom.app M).hom) := by
  have := coefficientRestrictionOpenMap_isIso φ j
  let β := asIso (coefficientRestrictionOpenMap φ j)
  let τ := (asIso (upperStarRestrictScalars φ j).natTrans).symm
  have hb (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
    (unit_mateEquiv_symm
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
      τ.hom F).symm
  have hd :=
    Adjunction.mapDerivedCategoryAdjunction_mate
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j) τ β hb
  have hu := universal_left_adjoint
    ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) j).mapDerivedCategoryAdjunction)
    ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction)
    (Functor.mapDerivedCategorySquareIso β) (Functor.mapDerivedCategorySquareIso τ)
    hd η.hom hη
  have hi : ((coefficientRestrictionOpenPlus φ j).hom.app M).hom =
      (Functor.mapDerivedCategorySquareIso β).hom.app M.obj := by
    change _root_.DerivedCategory.Plus.ι.map
      ((coefficientRestrictionOpenPlus φ j).hom.app M) = _
    simp only [coefficientRestrictionOpenPlus, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.map_comp,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app]
    congr 1
    have hh := Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app
      (Sheaf.restrictScalars X.smallEtaleTopology φ)
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j) M
    rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso
      (Sheaf.restrictScalars X.smallEtaleTopology φ)
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)).hom.app M.obj)]
    erw [← hh]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, hh, Iso.hom_inv_id_app]
    rfl
  change Sheaf.IsDerivedBaseChange
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map η.hom ≫ _)
  rw [hi]
  exact hu

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
  have ho := coefficientRestrictionOpen_universal φ c.i M.unit M.universal
  have hp := properCoefficientUniversal φ c.g
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.map
      M.unit ≫ (coefficientRestrictionOpenPlus φ c.i).hom.app M.obj) ho
  have hu : Sheaf.IsDerivedBaseChange
      (((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).map
        M.unit ≫ (compactSupportCoefficientRestrictionPlus φ c).hom.app M.obj).hom) := by
    simpa only [compactSupportCoefficientRestrictionPlus, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.comp_id, Category.id_comp,
      Functor.map_comp, Functor.comp_map, Category.assoc] using hp
  have hi := N.universal.isIso hu
    (compactSupportCoefficientComparisonPlus c M N).hom (by
      exact (Equiv.ofBijective _ (N.universal _)).apply_symm_apply _)
  let : IsIso (_root_.DerivedCategory.Plus.ι.map
      (compactSupportCoefficientComparisonPlus c M N)) := hi
  exact isIso_of_reflects_iso (compactSupportCoefficientComparisonPlus c M N)
    _root_.DerivedCategory.Plus.ι

/-- Finite Tor amplitude ensures that reduction has a bounded tensor presentation;
no flatness of the coefficient map is assumed. Source: Stacks Tags 06YY and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: the finite-Tor interval supplies a bounded flat cochain representative by
DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn. The quotient coefficient
map is surjective and its kernel is generated by the image of the appropriate
uniformizer power. The existing Sheaf.reductionDatum constructs its termwise
reduction and its canonical unit. This complex inherits the lower degree bound.
The bounded flat representative is K-flat, so reductionDatum.bijective_comp_map
gives the universal property against every ambient B-complex. Transport this
unit along the chosen representative isomorphism. -/
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
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E m)
  let B := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)
  let q : Padic.coefficientExtensionRing l E m →+*
      Padic.coefficientExtensionRing l E n :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
  let φ : A →+* B := RingHom.ulift q
  have hq : Function.Surjective q := Ideal.Quotient.factor_surjective _
  have hφ : Function.Surjective φ := by
    rintro ⟨y⟩
    obtain ⟨x, hx⟩ := hq y
    exact ⟨ULift.up x, congrArg ULift.up hx⟩
  let π := Padic.coefficientExtensionUniformizer l E
  let r := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E m) (π ^ n)
  have hkerq : RingHom.ker q = Ideal.span {r} := by
    rw [Ideal.Quotient.factor_ker]
    simp only [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
      Ideal.map_span, Set.image_singleton]
    rfl
  have hker : RingHom.ker φ = Ideal.span {ULift.up r} := by
    ext x
    rw [RingHom.mem_ker]
    change ULift.up (q x.down) = ULift.up 0 ↔ _
    rw [ULift.up_inj, ← RingHom.mem_ker, hkerq,
      Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨ULift.up y, congrArg ULift.up hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.down, congrArg ULift.down hy⟩
  obtain ⟨a, b, _hab, hTor⟩ := _hK.2
  have hTor' := (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn).1 hTor
  obtain ⟨P, hGE, hLE, hflat, ⟨e⟩⟩ :=
    _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn hTor'
  let D := Sheaf.reductionDatum T.smallEtaleTopology φ hφ (ULift.up r) hker
  let P' := (D.Φ.mapHomologicalComplex (.up ℤ)).obj P
  have : CochainComplex.IsStrictlyGE P' a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact D.Φ.map_isZero (P.isZero_of_isStrictlyGE a i hi)
  have hplus : _root_.DerivedCategory.TStructure.t.plus
      ((_root_.DerivedCategory.Q).obj P') := ⟨a, inferInstance⟩
  let η := _root_.DerivedCategory.Q.map (D.complexMap P) ≫
    (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app P'
  have hη : Sheaf.IsDerivedBaseChange η := by
    intro L
    have := Sheaf.restrictScalars_full T.smallEtaleTopology φ hφ
    exact D.bijective_comp_map P (CochainComplex.kFlat_of_bounded_of_flat P a b hflat) L
  exact ⟨⟨⟨(_root_.DerivedCategory.Q).obj P', hplus⟩,
    ObjectProperty.homMk (e.inv ≫ η), hη.of_iso e.symm⟩⟩

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

private theorem scalarExtensionIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {K : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))}
    {L : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars J φ).obj L}
    (hη : Sheaf.IsDerivedBaseChange η) :
    Nonempty ((pbcFixedScalarExtension J φ).obj K ≅ L) := by
  let adj := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ)
  have hu : Sheaf.IsDerivedBaseChange (adj.unit.app K) := by
    intro N
    convert (adj.homEquiv K N).bijective using 1
    ext g
    exact (adj.homEquiv_unit _ _ g).symm
  let c := (adj.homEquiv K L).symm η
  have hc : IsIso c := hu.isIso hη c (by
    change (adj.homEquiv K L) ((adj.homEquiv K L).symm η) = η
    exact Equiv.apply_symm_apply _ _)
  exact ⟨asIso c⟩

/-- A universal tensor of a finite-Tor ordinary-etale realization remains bounded
below of etale origin, including for nonflat finite reduction.
Source: Stacks Tags 06YY and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: the preceding existence theorem gives a bounded-below ordinary-etale
presentation N. The scalar adjunction and the universal-arrow bijections identify
N and M with the respective actual scalar extensions. The canonical
pbcComparisonReduction isomorphism commutes comparison inverse image with scalar
extension. Compose it with scalar extension of the supplied etale-origin
isomorphism and with the two universal-presentation isomorphisms. This realizes
M as comparison inverse image of N. Etale origin is invariant under isomorphisms.
This is the domain calculation of
lem-sf-compact-coefficient-composition, proof step 2, without exceptional adjunctions. -/
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
  let φ := RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E m)
    (T := Padic.coefficientExtensionIdeal l E n) (Ideal.pow_le_pow_right hmn))
  obtain ⟨N⟩ := Etale.nonempty_coefficientTensorModel_of_finiteTor
    l E m n hn hmn T K₀ _hK₀
  obtain ⟨eN⟩ := scalarExtensionIso N.universal
  obtain ⟨eM⟩ := scalarExtensionIso M.universal
  let ν := (comparisonUpperStar (ModuleCat.{u + 1}
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) T).mapDerivedCategory
  let e' : ν.obj N.obj.obj ≅ M.obj :=
    ν.mapIso eN.symm ≪≫ (pbcComparisonReduction T φ).symm.app K₀.obj ≪≫
      (pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).mapIso _e ≪≫ eM
  exact (DerivedCategory.plusEtaleOrigin _ T).prop_of_iso e'
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj N.obj.property)

end AlgebraicGeometry.ProEtale
