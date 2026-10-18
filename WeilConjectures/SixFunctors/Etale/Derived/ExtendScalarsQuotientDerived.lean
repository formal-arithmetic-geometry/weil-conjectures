/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalKFlat
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsQuotient
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension

/-!
# Derived extension of scalars of étale sheaves along a quotient ring

Let `J` be an ideal of a commutative ring `Λ` and `A = Λ ⧸ J`. Extension of scalars
`E = A ⊗_Λ -` of étale sheaves preserves quasi-isomorphisms between K-flat complexes, so it has
a total left derived functor `LE : D(X_ét, Λ) ⥤ D(X_ét, A)`, the derived base change
`K ↦ K ⊗ᴸ_Λ A`. We show:

- `LE` is left adjoint to restriction of scalars `Res : D(X_ét, A) ⥤ D(X_ét, Λ)`
  (`AlgebraicGeometry.Etale.derivedExtendScalarsAdjunction`);
- `Res (LE K) ≅ K ⊗ᴸ A_X` is the reduction of `K` modulo `J`
  (`AlgebraicGeometry.Etale.nonempty_iso_restrictScalars_leftDerived_obj`);
- `LE` is monoidal and, as a consequence, satisfies the internal adjunction
  `RHom_Λ(K, Res N) ≅ Res RHom_A(LE K, N)`
  (`AlgebraicGeometry.Etale.derivedHomCompIsoOfAdjunction`);
- every derived base change `η : K ⟶ Res K'` along `Λ ⟶ Λ ⧸ J`
  (`CategoryTheory.Sheaf.IsDerivedBaseChange`) is `LE K`, so that `Res K' ≅ K ⊗ᴸ A_X`
  (`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_of_isDerivedBaseChange`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

open Scheme

-- The derived tensor product of étale sheaves (`AlgebraicGeometry.Etale.derivedTensor`) is defined
-- for a symmetric monoidal coefficient category, with the braiding of the symmetric structure;
-- finding the braiding of `ModuleCat` through the same path avoids expensive kernel unfoldings.
attribute [local instance high] SymmetricCategory.toBraidedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] (J : Ideal Λ) (X : Scheme.{u})

/-- The small étale site of a scheme is locally small. Instance search does not find this in the
presence of the imports of this file. -/
local instance (X : Scheme.{u}) : LocallySmall.{u + 1} X.Etale :=
  @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)

/-- The small étale site of a scheme is essentially small. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  essentiallySmall_of_small_of_locallySmall _

/-- Restriction of scalars of étale sheaves reflects isomorphisms, being computed sectionwise. -/
instance reflectsIsomorphisms_sheafRestrictScalars {Λ' : Type (u + 1)} [CommRing Λ']
    (φ : Λ →+* Λ') :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).ReflectsIsomorphisms where
  reflects {F G} f hf := by
    have : IsIso ((sheafToPresheaf _ _).map
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).map f)) := inferInstance
    have : IsIso f.hom := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro U
      have : IsIso ((ModuleCat.restrictScalars.{u + 1} φ).map (f.hom.app U)) :=
        NatIso.isIso_app_of_isIso
          ((sheafToPresheaf _ _).map ((Sheaf.restrictScalars X.smallEtaleTopology φ).map f)) U
      have : IsIso ((forget (ModuleCat Λ)).map
          ((ModuleCat.restrictScalars.{u + 1} φ).map (f.hom.app U))) := inferInstance
      have : IsIso ((forget (ModuleCat Λ')).map (f.hom.app U)) := this
      exact isIso_of_reflects_iso _ (forget (ModuleCat Λ'))
    have : IsIso ((sheafToPresheaf _ _).map f) := this
    exact isIso_of_reflects_iso f (sheafToPresheaf _ _)

/-- Extension of scalars along `Λ ⟶ Λ ⧸ J` preserves quasi-isomorphisms between K-flat
complexes: after restricting scalars back to `Λ`, it is tensoring with `(Λ ⧸ J)_X`. -/
instance preservesKFlatQuasiIso_etaleSheafExtendScalars :
    (ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X).PreservesKFlatQuasiIso where
  quasiIso_map {K L} hK hL f _ := by
    let R := Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)
    let e := Functor.mapHomologicalComplexCompIso
      (etaleSheafExtendScalarsCompRestrictScalarsIso J X) (.up ℤ)
    have h := CochainComplex.quasiIso_mapHomologicalComplex_tensorRight_map_of_kFlat
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ J))) hK hL f
    have h' : QuasiIso ((R.mapHomologicalComplex (.up ℤ)).map
        (((ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X).mapHomologicalComplex
          (.up ℤ)).map f)) :=
      (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality f).symm)).2 h
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso] at h' ⊢
    have : IsIso (R.mapDerivedCategory.map (DerivedCategory.Q.map
        (((ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X).mapHomologicalComplex
          (.up ℤ)).map f))) :=
      (NatIso.isIso_map_iff R.mapDerivedCategoryFactors _).2 h'
    exact isIso_of_reflects_iso _ R.mapDerivedCategory

/-- The derived extension of scalars `K ↦ K ⊗ᴸ_Λ (Λ ⧸ J)` is left adjoint to restriction of
scalars on the derived categories of étale sheaves. -/
noncomputable def derivedExtendScalarsAdjunction :
    (ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X).leftDerivedFunctor ⊣
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).mapDerivedCategory :=
  (ProEtale.etaleSheafExtendScalarsAdjunction _ X).derivedAdjunction.ofNatIsoRight
    (Functor.rightDerivedFunctorIsoMapDerivedCategory _)

section

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X}

/-- For a K-flat complex `P` of étale sheaves, the derived tensor product `P ⊗ᴸ F[0]` is
computed by the tensor product of complexes `P ⊗ F`. This is
`DerivedCategory.QObjTensorSingleFunctorObjIso`, stated with
`AlgebraicGeometry.Etale.derivedTensor` so that it specialises to `A = ModuleCat Λ` without
comparing monoidal instances. -/
noncomputable def derivedTensorQObjSingleFunctorObjIsoOfKFlat
    (P : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) (F : Sheaf X.smallEtaleTopology A) :
    ((derivedTensor A X).obj ((_root_.DerivedCategory.Q).obj P)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F) ≅
      (_root_.DerivedCategory.Q).obj (((tensorRight F).mapHomologicalComplex _).obj P) :=
  _root_.DerivedCategory.QObjTensorSingleFunctorObjIso P hP F

end

section

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {B : Type u'} [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B] {X}
  {F : Sheaf X.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology B} [F.Additive]
  [F.PreservesKFlatQuasiIso] [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  {R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}

/-- For a monoidal functor `F` of étale sheaves with derived functor `LF` left adjoint to `R`,
`R ⋙ RHom(K, -) ≅ RHom(LF K, -) ⋙ R`: both are right adjoint to
`T ↦ LF(K ⊗ᴸ T) ≅ LF K ⊗ᴸ LF T`. -/
noncomputable def derivedHomCompIsoOfAdjunction (adj : F.leftDerivedFunctor ⊣ R)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    R ⋙ (derivedHom A X).obj (op K) ≅ (derivedHom B X).obj (op (F.leftDerivedFunctor.obj K)) ⋙ R :=
  (((derivedTensorHomAdjunction A K).comp adj).ofNatIsoLeft
    (F.leftDerivedTensorIsoOfKFlat K)).rightAdjointUniq
    (adj.comp (derivedTensorHomAdjunction B _))

end

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The derived base change `K ⊗ᴸ_Λ (Λ ⧸ J)`, with scalars restricted back to `Λ`, is the
reduction `K ⊗ᴸ (Λ ⧸ J)_X` of `K` (`AlgebraicGeometry.Etale.reductionModIdeal`): on a K-flat
complex `P` both are computed by `P ⊗ (Λ ⧸ J)_X`. -/
theorem nonempty_iso_restrictScalars_leftDerived_obj (K : 𝐃(X, Λ)) :
    Nonempty ((Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj
        ((ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X).leftDerivedFunctor.obj K) ≅
      (reductionModIdeal Λ X J).obj K) := by
  let E := ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X
  let R := Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)
  obtain ⟨P, hP, ⟨e⟩⟩ := _root_.DerivedCategory.exists_kFlat_iso K
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  rw [HomotopyCategory.kFlat_quotient_obj_iff] at hP
  have := E.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  let c := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ (Λ ⧸ J))
  let e' : _root_.DerivedCategory.Q.obj P ≅ K :=
    (_root_.DerivedCategory.quotientCompQhIso _).symm.app P ≪≫ e
  exact ⟨R.mapDerivedCategory.mapIso (E.leftDerivedFunctor.mapIso e.symm ≪≫
      asIso (E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P)) ≪≫
      _root_.DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      (_root_.DerivedCategory.quotientCompQhIso _).app
        ((E.mapHomologicalComplex (.up ℤ)).obj P)) ≪≫
    R.mapDerivedCategoryFactors.app _ ≪≫
    _root_.DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
      (etaleSheafExtendScalarsCompRestrictScalarsIso J X) (.up ℤ)).app P) ≪≫
    (derivedTensorQObjSingleFunctorObjIsoOfKFlat P hP c).symm ≪≫
    ((derivedTensor _ X).flip.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj c)).mapIso e'⟩

section BaseChange

variable {J X}

/-- A derived base change `η : K ⟶ Res K'` along `Λ ⟶ Λ ⧸ J`
(`CategoryTheory.Sheaf.IsDerivedBaseChange`) is the derived extension of scalars of `K`: there is
an isomorphism `LE K ≅ K'` compatible with `η` and the unit of
`AlgebraicGeometry.Etale.derivedExtendScalarsAdjunction`. -/
lemma exists_iso_leftDerived_of_isDerivedBaseChange {K : 𝐃(X, Λ)} {K' : 𝐃(X, Λ ⧸ J)}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) :
    ∃ e : (ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X).leftDerivedFunctor.obj K ≅
        K',
      (derivedExtendScalarsAdjunction J X).unit.app K ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).map e.hom =
          η := by
  let adj := derivedExtendScalarsAdjunction J X
  let R := Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)
  obtain ⟨h, hh⟩ := (hη _).2 (adj.unit.app K)
  have hh' : η ≫ R.map h = adj.unit.app K := hh
  let g := (adj.homEquiv K K').symm η
  have hg : adj.unit.app K ≫ R.map g = η := by
    have := (adj.homEquiv K K').apply_symm_apply η
    rwa [Adjunction.homEquiv_unit] at this
  refine ⟨⟨g, h, ?_, ?_⟩, hg⟩
  · apply (adj.homEquiv _ _).injective
    change adj.unit.app K ≫ R.map (g ≫ h) = adj.unit.app K ≫ R.map (𝟙 _)
    rw [Functor.map_comp, reassoc_of% hg, hh']
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  · apply (hη K').1
    change η ≫ R.map (h ≫ g) = η ≫ R.map (𝟙 _)
    rw [Functor.map_comp, reassoc_of% hh', hg]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The restriction of scalars of a derived base change `η : K ⟶ Res K'` of `K` along
`Λ ⟶ Λ ⧸ J` is the reduction `K ⊗ᴸ (Λ ⧸ J)_X` (`AlgebraicGeometry.Etale.reductionModIdeal`). -/
theorem nonempty_iso_reductionModIdeal_of_isDerivedBaseChange {K : 𝐃(X, Λ)}
    {K' : 𝐃(X, Λ ⧸ J)}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) :
    Nonempty ((Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj K' ≅
      (reductionModIdeal Λ X J).obj K) := by
  obtain ⟨e, -⟩ := exists_iso_leftDerived_of_isDerivedBaseChange hη
  obtain ⟨e'⟩ := nonempty_iso_restrictScalars_leftDerived_obj J X K
  exact ⟨(Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).mapIso
    e.symm ≪≫ e'⟩

/-- **Internal adjunction for a derived base change.** For a derived base change
`η : K ⟶ Res K'` of `K` along `Λ ⟶ Λ ⧸ J` and `N ∈ D(X_ét, Λ ⧸ J)`,
`RHom_Λ(K, Res N) ≅ Res RHom_{Λ ⧸ J}(K', N)`
(`AlgebraicGeometry.Etale.derivedHomCompIsoOfAdjunction`). -/
theorem nonempty_iso_derivedHom_restrictScalars_of_isDerivedBaseChange {K : 𝐃(X, Λ)}
    {K' : 𝐃(X, Λ ⧸ J)}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) (N : 𝐃(X, Λ ⧸ J)) :
    Nonempty (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj N) ≅
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj
        (((derivedHom (ModuleCat.{u + 1} (Λ ⧸ J)) X).obj (op K')).obj N)) := by
  obtain ⟨eK, -⟩ := exists_iso_leftDerived_of_isDerivedBaseChange hη
  exact ⟨(derivedHomCompIsoOfAdjunction (derivedExtendScalarsAdjunction J X) K).app N ≪≫
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).mapIso
      (((derivedHom (ModuleCat.{u + 1} (Λ ⧸ J)) X).mapIso eK.symm.op).app N)⟩

end BaseChange

end AlgebraicGeometry.Etale
