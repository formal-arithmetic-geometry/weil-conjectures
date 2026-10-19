/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q35 and U7
-/
module

public import Sheaf.Paper.WitnessCompatibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction

/-!
# Direct image and finite coefficient restriction in the fixed scalar presentation

Source: Stacks, Tags 0D6E and 07A6; blueprint
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars).
The comparison is the actual adjunction mate of the canonical inverse-image comparison.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private theorem mate_left_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L E : A ⥤ B} {R : B ⥤ A} {L' E' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (e : L ≅ E) (e' : L' ≅ E')
    (s : G ⋙ E' ⟶ E ⋙ H) :
    (mateEquiv (adj.ofNatIsoLeft e) (adj'.ofNatIsoLeft e')
      (TwoSquare.mk _ _ _ _ s)).natTrans =
      (mateEquiv adj adj'
        (TwoSquare.mk _ _ _ _
          (Functor.whiskerLeft G e'.hom ≫ s ≫ Functor.whiskerRight e.inv H))).natTrans := by
  ext X
  simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit,
    Functor.map_comp, Functor.comp_map, Category.assoc]
  repeat first | erw [Category.id_comp] | erw [Category.comp_id]
  rfl

namespace AlgebraicGeometry.ProEtale

private theorem restriction_underived_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom)).natTrans =
        𝟙 (lowerStar (ModuleCat.{u + 1} B) f ⋙
          Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ) := by
  apply (mateEquiv (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) φ)).injective
  change (mateEquiv (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) φ)
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom))).natTrans = _
  rw [iterated_mateEquiv_conjugateEquiv]
  rw [conjugateEquiv_upperStarRestrictScalarsIso_hom]
  ext M ⟨U⟩ x
  exact congrArg (fun t ↦ t.hom x)
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).right_triangle_components
      (M.obj.obj (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj U)))).symm

attribute [local irreducible] upperStar

/-- The canonical inverse-image/restriction square, with its published normalization.
Source: Stacks Tag 07A6
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars). -/
noncomputable abbrev fixedScalarRestrictionPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  leftDerivedUpperStarRestrictScalarsIso φ f

/-- The inverse-direction direct-image comparison is the mate of the canonical square.
Source: Stacks Tags 0D6E and 07A6
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars). -/
noncomputable def fixedScalarRestrictionDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R((f)_*[ModuleCat.{u + 1} B]) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ ⟶
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        R((f)_*[ModuleCat.{u + 1} A]) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (fixedScalarRestrictionPullback φ f).hom

private noncomputable abbrev restrictionDerivedUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) :
    _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      F.rightDerivedFunctor.obj (_root_.DerivedCategory.Q.obj K) :=
  F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K)

private theorem restrictionDerivedUnit_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] {K I : CochainComplex C ℤ} (j : K ⟶ I) :
    _root_.DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map j) ≫
        restrictionDerivedUnit F I =
      restrictionDerivedUnit F K ≫ F.rightDerivedFunctor.map (_root_.DerivedCategory.Q.map j) :=
  F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient _ _).map j)

private theorem restrictionDerivedUnit_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (I : CochainComplex C ℤ) [I.IsKInjective] :
    (F.rightDerivedFunctorObjQIso I).hom = inv (restrictionDerivedUnit F I) := by
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, asIso_inv]
  change F.rightDerivedFunctor.map (𝟙 _) ≫ inv (restrictionDerivedUnit F I) ≫ 𝟙 _ = _
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_derived_adj_eq
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f =
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm := by
  exact Adjunction.derived_eq_ofNatIsoLeft
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).mapHomotopyCategory (.up ℤ))
    (HomotopyCategory.quasiIso _ _) (HomotopyCategory.quasiIso _ _)
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactorsh.hom
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorUnit
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
      (upperStar (ModuleCat.{u + 1} A) f)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_mate_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    fixedScalarRestrictionDirectImageMap φ f =
      (mateEquiv
        (Adjunction.mapDerivedCategoryRightDerivedAdjunction
          (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))
        (Adjunction.mapDerivedCategoryRightDerivedAdjunction
          (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso
            (upperStarRestrictScalarsIso φ f)).hom)).natTrans := by
  change (mateEquiv
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (TwoSquare.mk _ _ _ _ (fixedScalarRestrictionPullback φ f).hom)).natTrans = _
  rw [restriction_derived_adj_eq, restriction_derived_adj_eq]
  refine (mate_left_iso _ _ _ _ (fixedScalarRestrictionPullback φ f).hom).trans ?_
  congr 2
  ext K
  simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Iso.symm_hom, Iso.symm_inv, fixedScalarRestrictionPullback,
    leftDerivedUpperStarRestrictScalarsIso_hom_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_mate_factors
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ℤ) :
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
        (restrictionDerivedUnit (lowerStar (ModuleCat.{u + 1} B) f) K) ≫
      (fixedScalarRestrictionDirectImageMap φ f).app (_root_.DerivedCategory.Q.obj K) ≫
      (R(lowerStar (ModuleCat.{u + 1} A) f)).map
        ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactors.hom.app
          K) =
    (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryFactors.hom.app
        (((lowerStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj K) ≫
      restrictionDerivedUnit (lowerStar (ModuleCat.{u + 1} A) f)
        (((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapHomologicalComplex
          (.up ℤ)).obj K) := by
  have h := derived_mate_factors
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarRestrictScalarsIso φ f) K
  rw [restriction_underived_mate] at h
  simp only [NatTrans.mapHomologicalComplex_id, NatTrans.id_app] at h
  erw [DerivedCategory.Q.map_id, Category.id_comp] at h
  rw [restriction_mate_eq]
  dsimp only [chainDerivedUnit] at h
  simp only [quotient_hom_id, quotient_inv_id] at h
  repeat first
    | erw [CategoryTheory.Functor.map_id] at h
    | erw [Category.id_comp] at h
    | erw [Category.comp_id] at h
  exact h

/-- Restriction of finite coefficients commutes with the unbounded derived direct image.
The map is fixed by its adjunction-mate definition, rather than an arbitrary isomorphism.
Source: Stacks Tags 0D6E and 07A6
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars).
Proof: restriction is exact. The two composites are the direct image of the same
morphism of ringed topoi. Resolve a K-injective B-complex after restriction by a
K-injective A-complex. The right-derived comparison is inverse to the image of this
resolution. The canonical derived adjunction formula identifies that comparison with
the mate above. In particular this argument does not suppose that restriction itself
preserves K-injectives. This gives invertibility for every unbounded object. -/
theorem fixedScalarRestrictionDirectImageMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (fixedScalarRestrictionDirectImageMap φ f) := by
  sorry

/-- The forward-direction canonical comparison, with the K-injective normalization
inherited from the named mate theorem. Source: Stacks Tag 0D6E
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars). -/
noncomputable def fixedScalarRestrictionDirectImage
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        R((f)_*[ModuleCat.{u + 1} A]) ≅
      R((f)_*[ModuleCat.{u + 1} B]) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ :=
  letI := fixedScalarRestrictionDirectImageMap_isIso φ f
  (asIso (fixedScalarRestrictionDirectImageMap φ f)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical comparison is the inverse image of the restricted K-injective
resolution, with all exact-functor quotient identifications written explicitly.
Source: Stacks Tags 0D6E and 0D6J
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars).
Proof: the underived pullback square has identity direct-image mate, by the
restriction/coextension adjunction triangle identity. Transport the derived mate
through the canonical left-derived pullback identification and apply the generic
derived-mate factorization. Naturality of the right-derived unit at j, followed by
cancellation of the K-injective unit isomorphisms, gives the displayed equation.
The global invertibility theorem above and the K-injective computation isomorphisms
then show that the image of f_*(j) in the derived category is invertible, hence that
f_*(j) is a quasi-isomorphism. -/
theorem fixedScalarRestrictionDirectImage_kInjective
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ℤ)
    [J.IsKInjective]
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective]
    (j : ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapHomologicalComplex
      (.up ℤ)).obj J ⟶ I) [QuasiIso j] :
    QuasiIso (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j) ∧
      (fixedScalarRestrictionDirectImage φ f).hom.app (_root_.DerivedCategory.Q.obj J) ≫
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
            ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorObjQIso J).hom ≫
          (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryFactors.hom.app
            (((lowerStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj J) ≫
          _root_.DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j) =
        (R((f)_*[ModuleCat.{u + 1} A])).map
            ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactors.hom.app
              J) ≫
          (R((f)_*[ModuleCat.{u + 1} A])).map (_root_.DerivedCategory.Q.map j) ≫
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorObjQIso I).hom := by
  let uB := restrictionDerivedUnit (lowerStar (ModuleCat.{u + 1} B) f) J
  let uI := restrictionDerivedUnit (lowerStar (ModuleCat.{u + 1} A) f) I
  have : IsIso uB := inferInstance
  have : IsIso uI := inferInstance
  have : IsIso (fixedScalarRestrictionDirectImageMap φ f) :=
    fixedScalarRestrictionDirectImageMap_isIso φ f
  have hf := restriction_mate_factors φ f J
  have hn := restrictionDerivedUnit_naturality (lowerStar (ModuleCat.{u + 1} A) f) j
  have he :
      (fixedScalarRestrictionDirectImage φ f).hom.app (_root_.DerivedCategory.Q.obj J) ≫
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
            ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorObjQIso J).hom ≫
          (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryFactors.hom.app
            (((lowerStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj J) ≫
          _root_.DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j) =
        (R((f)_*[ModuleCat.{u + 1} A])).map
            ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactors.hom.app
              J) ≫
          (R((f)_*[ModuleCat.{u + 1} A])).map (_root_.DerivedCategory.Q.map j) ≫
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorObjQIso I).hom := by
    rw [restrictionDerivedUnit_inv, restrictionDerivedUnit_inv]
    apply (cancel_mono uI).1
    dsimp only [uI]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [hn, ← reassoc_of% hf]
    simp only [fixedScalarRestrictionDirectImage, Iso.symm_hom, asIso_inv,
      ← Functor.map_comp_assoc, IsIso.inv_hom_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← Category.assoc, ← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app]
    simp only [Category.id_comp]
  refine ⟨?_, he⟩
  apply (_root_.DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp
  have hiso : IsIso
      ((fixedScalarRestrictionDirectImage φ f).hom.app (_root_.DerivedCategory.Q.obj J) ≫
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
          ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorObjQIso J).hom ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryFactors.hom.app
          (((lowerStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj J) ≫
        _root_.DerivedCategory.Q.map
          (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j)) := by
    rw [he]
    infer_instance
  simpa only [isIso_comp_left_iff] using hiso

end AlgebraicGeometry.ProEtale
