/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Algebra.Homology.Additive
import Sheaf.RingTheory.LocalizationCotangentVanishing
import Sheaf.RingTheory.CotangentFlatBaseChange
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-!
# The derived diagonal criterion for cotangent vanishing

Source: Stacks Project, Cotangent Complex, Tag 08R0, lemma-derived-diagonal
(blueprint: lem-trf-derived-diagonal-cotangent-vanishing).

The canonical multiplication is represented using any projective resolution of the
underlying A-module B. Extension of scalars followed by the ordinary adjunction counit
is the map b ⊗ p ↦ b ε(p), so its derived source is B ⊗ᴸ[A] B.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra.CotangentResolution

/-- The canonical derived multiplication B ⊗ᴸ[A] B → B[0], computed using a projective
resolution of B as an A-module. Apply B ⊗[A] - to the augmentation, identify its value
on the single complex with the single complex of its value, and apply the extension/
restriction adjunction counit. Finally extend degree n to cochain degree -n and localize.
Source: Stacks, Tag 08R0 (blueprint: lem-trf-derived-diagonal-cotangent-vanishing). -/
noncomputable def derivedDiagonalMultiplication
    {A B : CommRingCat.{u}}
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} B)] (f : A ⟶ B)
    (P : ProjectiveResolution
      ((ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B B))) :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap
    (((ModuleCat.extendScalars f.hom).mapHomologicalComplex (ComplexShape.down ℕ)).map P.π ≫
      (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars f.hom)
        (ComplexShape.down ℕ) 0).hom.app _ ≫
      (ChainComplex.single₀ (ModuleCat.{u} B)).map
        ((ModuleCat.extendRestrictScalarsAdj f.hom).counit.app (ModuleCat.of B B)))
    ComplexShape.embeddingDownNat)

private local instance {A B : CommRingCat.{u}} (f : A ⟶ B) :
    (ModuleCat.extendScalars.{u, u, u} f.hom).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom).left_adjoint_additive

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isIso_derived_transpose
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    {A B : CommRingCat.{u}} (f : A ⟶ B)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat K)
    (Y : HomotopyCategory (ModuleCat.{u} B) (.up ℤ))
    (g : (HomotopyCategory.quotient _ _).obj K ⟶
      ((ModuleCat.restrictScalars f.hom).mapHomotopyCategory (.up ℤ)).obj Y)
    (hg : IsIso (DerivedCategory.Qh.map
      (((ModuleCat.extendRestrictScalarsAdj f.hom).mapHomotopyCategory (.up ℤ)).homEquiv
        _ _ |>.symm g))) :
    IsIso (((baseChangeAdjunction f).homEquiv _ _).symm
      (DerivedCategory.Qh.map g ≫
        (ModuleCat.restrictScalars f.hom).mapDerivedCategoryFactorsh.inv.app Y)) := by
  let : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  let (M : ModuleCat.{u} A) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).flip.obj M) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight M))
  let : (ModuleCat.extendScalars f.hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj f.hom).left_adjoint_additive
  let := ModuleCat.extendScalars_preservesKFlatQuasiIso f.hom
  let F := ModuleCat.extendScalars f.hom
  let G := ModuleCat.restrictScalars f.hom
  let a := ModuleCat.extendRestrictScalarsAdj f.hom
  let ah := a.mapHomotopyCategory (.up ℤ)
  let X := (HomotopyCategory.quotient _ _).obj K
  let t := (ah.homEquiv X Y).symm g
  have hu := ah.derivedη_fac_app
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ))
    F.leftDerivedFunctorCounit G.rightDerivedFunctorUnit X
  have hb := NatTrans.congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac Y
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hb
  have he : ((baseChangeAdjunction f).homEquiv _ _)
      (F.leftDerivedFunctorCounit.app X ≫ DerivedCategory.Qh.map t) =
      DerivedCategory.Qh.map g ≫ G.mapDerivedCategoryFactorsh.inv.app Y := by
    rw [baseChangeAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply]
    change a.derivedAdjunction.homEquiv _ _
        (F.leftDerivedFunctorCounit.app X ≫ DerivedCategory.Qh.map t) ≫
        G.rightDerivedFunctorIsoMapDerivedCategory.hom.app _ = _
    rw [Adjunction.homEquiv_unit, Functor.map_comp]
    simp only [← Category.assoc]
    have hu' : a.derivedAdjunction.unit.app (DerivedCategory.Qh.obj X) ≫
        G.rightDerivedFunctor.map (F.leftDerivedFunctorCounit.app X) =
        DerivedCategory.Qh.map (ah.unit.app X) ≫
          G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) := hu
    rw [hu']
    simp only [Category.assoc]
    erw [← G.rightDerivedFunctorUnit.naturality_assoc]
    rw [hb, ← Category.assoc]
    simp only [Functor.comp_map]
    rw [← DerivedCategory.Qh.map_comp]
    exact congrArg (fun k ↦ DerivedCategory.Qh.map k ≫
      G.mapDerivedCategoryFactorsh.inv.app Y) ((ah.homEquiv _ _).apply_symm_apply g)
  rw [← he, Equiv.symm_apply_apply]
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat K hK
  exact IsIso.comp_isIso' inferInstance hg

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isIso_diagonal_square
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    {A B : CommRingCat.{u}} (f : A ⟶ B)
    (P : ProjectiveResolution
      ((ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B B)))
    (hμ : IsIso (derivedDiagonalMultiplication f P)) :
    IsIso (derivedSquareMultiplication
      (Arrow.homMk f (𝟙 B) : Arrow.mk f ⟶ Arrow.mk (𝟙 B))) := by
  let F := ModuleCat.extendScalars f.hom
  let G := ModuleCat.restrictScalars f.hom
  let N := ModuleCat.of B B
  let Z := G.obj N
  let e := ComplexShape.embeddingDownNat
  have he0 : e.f 0 = 0 := rfl
  let K : CochainComplex (ModuleCat.{u} A) ℤ := P.complex.extend e
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj Z
  let H := (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj N
  let a := ModuleCat.extendRestrictScalarsAdj f.hom
  let s : K ⟶ S := HomologicalComplex.extendMap P.π e ≫
    (HomologicalComplex.extendSingleIso e Z 0 0 he0).hom
  have hs : QuasiIso s := by dsimp [s]; infer_instance
  have hK : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat K := by
    let : K.IsStrictlyLE 0 := (K.isStrictlyLE_iff 0).2 (fun i hi ↦
      P.complex.isZero_extend_X e i (fun n hn ↦ by
        change -(n : ℤ) = i at hn
        omega))
    exact CochainComplex.kFlat_of_isStrictlyLE_of_flat K 0
      (fun i ↦ (ModuleCat.flat_iff_flat (K.X i)).2 inferInstance)
  let j := (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app N
  let g := s ≫ j
  let gh := (HomotopyCategory.quotient _ _).map g
  let t := ((a.mapHomologicalComplex (.up ℤ)).homEquiv K H).symm g
  have ht : IsIso (DerivedCategory.Q.map t) := by
    let m :=
      ((F.mapHomologicalComplex (.down ℕ)).map P.π ≫
        (HomologicalComplex.singleMapHomologicalComplex F (.down ℕ) 0).hom.app Z ≫
        (ChainComplex.single₀ (ModuleCat.{u} B)).map (a.counit.app N))
    have hm : t = (P.complex.mapExtendIso e F).hom ≫
        HomologicalComplex.extendMap m e ≫
        (HomologicalComplex.extendSingleIso e N 0 0 he0).hom := by
      apply HomologicalComplex.to_single_hom_ext
      dsimp only [K] at *
      simp only [t, Adjunction.homEquiv_counit, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplex_map_f,
        Adjunction.mapHomologicalComplex_counit_app_f, g, s, j, m,
        HomologicalComplex.extendMap_f _ e he0,
        HomologicalComplex.extendSingleIso_hom_f,
        HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        ChainComplex.single₀_map_f_zero]
      simp only [Category.assoc, Functor.map_comp]
      simp only [F, G, H, N, Z, ChainComplex.single₀, CochainComplex.singleFunctor,
        Functor.id_obj] at *
      simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]
      simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
        Category.id_comp, Category.comp_id, Functor.map_comp]
      have hx : (P.complex.mapExtendIso e F).hom.f 0 ≫
          (((F.mapHomologicalComplex (.down ℕ)).obj P.complex).extendXIso e he0).hom =
          F.map (P.complex.extendXIso e he0).hom := by
        have aux (o : Option ℕ) (ho : o = some 0) :
            (HomologicalComplex.mapExtendX P.complex F o).hom ≫
              (HomologicalComplex.extend.XIso
                ((F.mapHomologicalComplex (.down ℕ)).obj P.complex) ho).hom =
              F.map (HomologicalComplex.extend.XIso P.complex ho).hom := by
          subst ho
          simp [HomologicalComplex.mapExtendX, HomologicalComplex.extend.XIso]
        exact aux (e.r 0) (e.r_eq_some he0)
      dsimp only [F] at hx
      rw [reassoc_of% hx]
      erw [Category.id_comp]
      have hn := a.counit.naturality
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv
      exact congrArg (fun k ↦ F.map (P.complex.extendXIso e he0).hom ≫
        F.map (P.π.f 0) ≫ k) hn
    rw [hm, Functor.map_comp, Functor.map_comp]
    have : IsIso (DerivedCategory.Q.map (HomologicalComplex.extendMap m e)) := hμ
    infer_instance
  have ht' : IsIso (DerivedCategory.Qh.map
      (((a.mapHomotopyCategory (.up ℤ)).homEquiv _ _).symm gh)) := by
    let X : HomotopyCategory (ModuleCat.{u} A) (.up ℤ) :=
      (HomotopyCategory.quotient _ _).obj K
    let Y : HomotopyCategory (ModuleCat.{u} B) (.up ℤ) :=
      (HomotopyCategory.quotient _ _).obj H
    let th : ((F.mapHomotopyCategory (.up ℤ)).obj X) ⟶ Y :=
      (HomotopyCategory.quotient _ _).map t
    have hg : ((a.mapHomotopyCategory (.up ℤ)).homEquiv X Y) th = gh := by
      change (a.mapHomotopyCategory (.up ℤ)).unit.app X ≫
        (G.mapHomotopyCategory (.up ℤ)).map th = gh
      have hu := a.mapHomotopyCategory_unit_app_quotient (.up ℤ) K
      change (a.mapHomotopyCategory (.up ℤ)).unit.app X = _ at hu
      rw [hu]
      change (HomotopyCategory.quotient _ _).map _ ≫
        (HomotopyCategory.quotient _ _).map _ = _
      rw [← Functor.map_comp]
      exact congrArg (HomotopyCategory.quotient _ _).map
        (((a.mapHomologicalComplex (.up ℤ)).homEquiv K H).apply_symm_apply g)
    have hth : (((a.mapHomotopyCategory (.up ℤ)).homEquiv X Y).symm gh) = th :=
      ((a.mapHomotopyCategory (.up ℤ)).homEquiv X Y).symm_apply_eq.mpr hg.symm
    change IsIso (DerivedCategory.Qh.map
      (((a.mapHomotopyCategory (.up ℤ)).homEquiv X Y).symm gh))
    rw [hth]
    exact ht
  have hd := isIso_derived_transpose f K hK
    ((HomotopyCategory.quotient _ _).obj H) gh ht'
  let q : Arrow.mk f ⟶ Arrow.mk (𝟙 B) := Arrow.homMk f (𝟙 B)
  have he : ((baseChangeAdjunction f).homEquiv _ _).symm
      (DerivedCategory.Qh.map gh ≫ G.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient _ _).obj H)) =
      (baseChangeExtension f).map (DerivedCategory.Q.map s) ≫
        derivedSquareMultiplication q := by
    have hrep : DerivedCategory.Qh.map gh ≫ G.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient _ _).obj H) =
        DerivedCategory.Q.map s ≫
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (squareModuleMap q) ≫
            (G.mapDerivedCategorySingleFunctor 0).inv.app
              ((ModuleCat.restrictScalars (𝟙 B : B ⟶ B).hom).obj N)) := by
      have hj : DerivedCategory.Q.map j ≫ G.mapDerivedCategoryFactors.inv.app H =
          (G.mapDerivedCategorySingleFunctor 0).inv.app N := by
        have hj' := G.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app N
        change (G.mapDerivedCategorySingleFunctor 0).inv.app N ≫
          G.mapDerivedCategoryFactors.hom.app H = DerivedCategory.Q.map j at hj'
        rw [← hj']
        simp only [Category.assoc, Iso.hom_inv_id_app]
        erw [Category.comp_id]
      have hfac : G.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ _).obj H) =
          G.mapDerivedCategoryFactors.inv.app H := by
        have hh := G.mapDerivedCategoryFactorsh_hom_app H
        simp only [DerivedCategory.quotientCompQhIso,
          HomologicalComplexUpToQuasiIso.quotientCompQhIso,
          Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
          Quotient.lift.isLift_inv] at hh
        erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
          Category.id_comp, Category.comp_id, Category.comp_id] at hh
        apply (cancel_mono (G.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ _).obj H))).1
        erw [Iso.inv_hom_id_app, hh, Iso.inv_hom_id_app]
        rfl
      change DerivedCategory.Q.map (s ≫ j) ≫ _ = _
      rw [Functor.map_comp, Category.assoc, hfac, hj]
      have hsq : squareModuleMap q = 𝟙 Z := by ext x; rfl
      rw [hsq]
      change DerivedCategory.Q.map s ≫ (G.mapDerivedCategorySingleFunctor 0).inv.app N =
        DerivedCategory.Q.map s ≫
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (𝟙 Z) ≫
            (G.mapDerivedCategorySingleFunctor 0).inv.app N
      erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [hrep]
    exact (baseChangeAdjunction f).homEquiv_naturality_left_symm _ _
  rw [he] at hd
  have : IsIso (DerivedCategory.Q.map s) := inferInstance
  exact IsIso.of_isIso_comp_left ((baseChangeExtension f).map (DerivedCategory.Q.map s)) _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isZero_cotangent_of_arrowIso
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (C : Coherence.{u}) {f g : Arrow CommRingCat.{u}} (e : f ≅ g)
    (h : IsZero (cotangentComplex C g)) : IsZero (cotangentComplex C f) := by
  let d := (C.differentialMap (C.standardMap e.hom)).map
  have hd (i : ℤ) : IsIso (d.f i) := by
    apply (ConcreteCategory.isIso_iff_bijective (d.f i)).2
    let r := (C.differentialMap (C.standardMap e.inv)).map
    have hl : Function.LeftInverse (r.f i) (d.f i) := by
      intro x
      have hc := C.standardDifferentialMap_comp e.hom e.inv i x
      rw [e.hom_inv_id] at hc
      exact hc.symm.trans (C.standardDifferentialMap_id f i x)
    have hr : Function.RightInverse (r.f i) (d.f i) := by
      intro x
      have hc := C.standardDifferentialMap_comp e.inv e.hom i x
      rw [e.inv_hom_id] at hc
      exact hc.symm.trans (C.standardDifferentialMap_id g i x)
    exact ⟨hl.injective, hr.surjective⟩
  let : ∀ i, IsIso (d.f i) := hd
  have := HomologicalComplex.Hom.isIso_of_components d
  have hm : IsIso (cotangentMap C e.hom) := by
    dsimp [cotangentMap]
    infer_instance
  exact ((ModuleCat.restrictScalars e.hom.right.hom).mapDerivedCategory.map_isZero h).of_iso
    (asIso (cotangentMap C e.hom))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isZero_cotangent_identity
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (C : Coherence.{u}) (B : CommRingCat.{u}) :
    IsZero (cotangentComplex C (Arrow.mk (𝟙 B))) := by
  let e := (IsLocalization.atUnits B (⊥ : Submonoid B)
    (S := Localization (⊥ : Submonoid B)) bot_le).toRingEquiv.toCommRingCatIso
  let q : Arrow.mk (𝟙 B) ≅
      Arrow.mk (CommRingCat.ofHom (algebraMap B (Localization (⊥ : Submonoid B)))) :=
    Arrow.isoMk (Iso.refl B) e (by ext x; rfl)
  exact isZero_cotangent_of_arrowIso C q
    (localization_cotangent_vanishing C B ⊥).1

/-- If the canonical derived multiplication is an isomorphism, the standard cotangent
complex is a zero object in D(B). The projective resolution is arbitrary and is only a
representative for the canonical derived tensor product, with no flatness hypothesis
on B over A. Source: Stacks, Tag 08R0
(blueprint: lem-trf-derived-diagonal-cotangent-vanishing).

Proof: Apply lem-trf-cotangent-flat-base-change to the commutative square with both
maps out of A equal to f and both maps into the lower-right B equal to the identity.
Its canonical derived multiplication is precisely the assumed isomorphism. Base change
identifies L[B/A] ⊗ᴸ[B] B with L[B/B]. Extension of scalars along the identity is
naturally the exact identity functor, so this gives L[B/A] ≅ L[B/B]. Apply
lem-trf-localization-cotangent-vanishing with R = B and S = {1}. The localization is
canonically B, hence L[B/B] is zero. Transport zero-object vanishing across the displayed
isomorphism to conclude. Projective modules are flat; the nonpositive projective
resolution computes the derived tensor product in the hypothesis. -/
theorem derived_diagonal_cotangent_vanishing
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (C : Coherence.{u}) {A B : CommRingCat.{u}} (f : A ⟶ B)
    (P : ProjectiveResolution
      ((ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B B)))
    (hμ : IsIso (derivedDiagonalMultiplication f P)) :
    IsZero (cotangentComplex C (Arrow.mk f)) := by
  let q : Arrow.mk f ⟶ Arrow.mk (𝟙 B) := Arrow.homMk f (𝟙 B)
  have := isIso_diagonal_square f P hμ
  have := isIso_cotangentBaseChange C q this
  have hz := (isZero_cotangent_identity C B).of_iso (asIso (cotangentBaseChange C q))
  let : (ModuleCat.restrictScalars (𝟙 B : B ⟶ B).hom).IsEquivalence :=
    Functor.isEquivalence_of_iso (ModuleCat.restrictScalarsId B).symm
  let G := (ModuleCat.restrictScalars (𝟙 B : B ⟶ B).hom).mapDerivedCategory
  have : G.IsEquivalence :=
    CategoryTheory.Functor.isEquivalence_mapDerivedCategory _
  have := (baseChangeAdjunction (𝟙 B)).isEquivalence_left_of_isEquivalence_right
  change IsZero ((baseChangeExtension (𝟙 B)).obj (cotangentComplex C (Arrow.mk f))) at hz
  apply (IsZero.iff_id_eq_zero _).2
  apply (baseChangeExtension (𝟙 B)).map_injective
  simpa only [CategoryTheory.Functor.map_id, Functor.map_zero] using (IsZero.iff_id_eq_zero _).1 hz

end Algebra.CotangentResolution
