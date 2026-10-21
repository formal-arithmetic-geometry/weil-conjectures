/-*
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Sheaf.Paper.StrictPerfectPackageOnSite
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.Paper.RingedProjectionRestriction
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.CategoryTheory.Adjunction.Triple
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# The open-immersion piece of the projection formula

Source: Weil conjectures blueprint, proper base change, lemma 1269;
Stacks Project, Tags 03DI, 03DJ, 03EL, 06YQ and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction

namespace SheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}

/-- The full subcategory on objects admitting a bounded finite-projective representative.
This is a global strict-perfect condition, with degreewise splittings and variable ranks;
it imposes no compatibility of the splittings with the differentials.
Source: blueprint lemma 1269
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
def openTensorCoefficients (R : Sheaf J CommRingCat.{u + 1}) : ObjectProperty (Der R) :=
  fun Q ↦ ∃ F : CochainComplex (Mod R) ℤ,
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) ∧
      Nonempty (StrictPerfectCoefficientPackageOnSite
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) F) ∧
      Nonempty (Q ≅ DerivedCategory.Q.obj F)

/-- The left side of the open formula, as a bifunctor on unbounded E and strict-perfect F.
Source: blueprint lemma 1269
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
def openTensorSource (R : Sheaf J CommRingCat.{u + 1}) (U : C) (a : TensorModel R) :
    Der (R.over U) × (openTensorCoefficients R).FullSubcategory ⥤ Der R :=
  ((localizedModuleExtension R U).mapDerivedCategory.prod (openTensorCoefficients R).ι) ⋙
    a.functor

/-- The right side of the open formula; restriction and extension are computed termwise.
Source: blueprint lemma 1269
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
def openTensorTarget (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (b : TensorModel (R.over U)) :
    Der (R.over U) × (openTensorCoefficients R).FullSubcategory ⥤ Der R :=
  ((𝟭 (Der (R.over U))).prod
    ((openTensorCoefficients R).ι ⋙ (localizedModuleRestriction R U).mapDerivedCategory)) ⋙
      b.functor ⋙ (localizedModuleExtension R U).mapDerivedCategory

/-- The canonical restriction-tensor interface, at fixed original site universes.
Source: Stacks 03EL and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
abbrev openTensorRestrictionComparison (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (a : TensorModel R) (b : TensorModel (R.over U)) (r : Restriction R U) :=
  letI : (localizedModuleRestriction R U).Additive :=
    localizedModuleRestriction_additive R U
  TensorComparison (R := R) (S := R.over U)
    (localizedModuleRestriction R U) r.model a b r.ordinaryTensor

/-- The natural open tensor isomorphism with its exact adjunction-unit normalization.
This predicate spells out the canonical map using the existing normalized tensor models.
Source: blueprint lemma 1269; Stacks 03DI and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
def openTensorFormula (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (a : TensorModel R) (b : TensorModel (R.over U)) (r : Restriction R U)
    (t : openTensorRestrictionComparison R U a b r) : Prop :=
  letI : (localizedModuleRestriction R U).Additive :=
    localizedModuleRestriction_additive R U
  ∃! beta : openTensorSource R U a ≅ openTensorTarget R U b,
      ∀ (E : Der (R.over U)) (F : (openTensorCoefficients R).FullSubcategory),
        (localizedModuleDerivedAdjunction R U).homEquiv _ _
            (beta.inv.app (E, F)) =
          b.functor.map (CategoryTheory.Prod.mkHom
            ((localizedModuleDerivedAdjunction R U).unit.app E)
            (𝟙 ((localizedModuleRestriction R U).mapDerivedCategory.obj F.obj))) ≫
              t.comparison.inv.app
                ((localizedModuleExtension R U).mapDerivedCategory.obj E, F.obj)

private theorem localizedUnit_isIso {Z : Scheme.{u}} {X : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j]
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    IsIso (localizedModuleAdjunctionIndependent R (ProEt.mk j)).unit := by
  let U := ProEt.mk j
  let A := (sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let a := localizedModuleAdjunctionIndependent R U
  let b := SheafOfModules.overPushforwardOverAdj (R := A) U
  have : (Over.forget U).Full := by
    constructor
    intro V V' f
    refine ⟨Over.homMk f ?_, rfl⟩
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono j).1
    exact (MorphismProperty.Over.w (f ≫ V'.hom)).trans
      (MorphismProperty.Over.w V.hom).symm
  have : IsIso (Over.forgetAdjStar U).unit := inferInstance
  have : IsIso b.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [← isIso_iff_of_reflects_iso _
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    change IsIso (M.val.presheaf.map ((Over.forgetAdjStar U).unit.app V.unop).op)
    infer_instance
  let triple : Adjunction.Triple _ _ _ := ⟨a, b⟩
  exact triple.isIso_unit_iff_isIso_counit.mpr inferInstance

private theorem localizedDerivedUnit_isIso {Z X : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j]
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    IsIso (localizedModuleDerivedAdjunction R (ProEt.mk j)).unit := by
  let U := ProEt.mk j
  let adj := localizedModuleDerivedAdjunction R U
  letI := localizedUnit_isIso j R
  have hQ (P : CochainComplex (Mod (R.over U)) ℤ) :
      IsIso (adj.unit.app (DerivedCategory.Q.obj P)) := by
    have hP : IsIso
        (((localizedModuleAdjunctionIndependent R U).mapHomologicalComplex (.up ℤ)).unit.app
          P) := by
      have hn : ∀ n : ℤ, IsIso
          ((((localizedModuleAdjunctionIndependent R U).mapHomologicalComplex (.up ℤ)).unit.app
            P).f n) := fun n ↦ inferInstanceAs
        (IsIso ((localizedModuleAdjunctionIndependent R U).unit.app (P.X n)))
      exact HomologicalComplex.Hom.isIso_of_components _
    have hu : adj.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map
          (((localizedModuleAdjunctionIndependent R U).mapHomologicalComplex (.up ℤ)).unit.app
            P) ≫
          (localizedModuleRestriction R U).mapDerivedCategoryFactors.inv.app _ ≫
            (localizedModuleRestriction R U).mapDerivedCategory.map
              ((localizedModuleExtension R U).mapDerivedCategoryFactors.inv.app P) := by
      simp only [adj, localizedModuleDerivedAdjunction, Adjunction.localization_unit_app]
      rfl
    rw [hu]
    infer_instance
  have h (M : Der (R.over U)) : IsIso (adj.unit.app M) :=
    (NatTrans.isIso_app_iff_of_iso adj.unit (DerivedCategory.Q.objObjPreimageIso M)).mp
      (hQ (DerivedCategory.Q.objPreimage M))
  exact NatIso.isIso_of_isIso_app adj.unit

private theorem mixedTensor {R : Sheaf J CommRingCat.{u + 1}} (a : TensorModel R)
    (P Q : CochainComplex (Mod R) ℤ) (hq : resolving R Q) :
    Nonempty (a.functor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj ((total R).obj (P, Q))) := by
  letI := SheafOfModules.monoidalCategory R
  letI := a.preadditive
  obtain ⟨A, f, hk, hf, hqf, _⟩ := CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  let ha : resolving R A := ⟨hk, fun n ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (A.X n)).symm (hf n)⟩
  haveI : QuasiIso f := hqf
  haveI : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hqf
  let g := HomologicalComplex.mapBifunctorMap f (𝟙 Q) (tensor R) (.up ℤ)
  have hg : QuasiIso g := by
    have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hqf
    have ht := hq.1 (CochainComplex.mappingCone f) hc
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
    intro i
    exact (ht i).of_iso (CochainComplex.mapBifunctorMappingCone₁Iso f Q (tensor R))
  letI : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hg
  exact ⟨a.functor.mapIso (Iso.prod (asIso (DerivedCategory.Q.map f)).symm
      (Iso.refl _)) ≪≫
    (a.representative.app (⟨A, ha⟩, ⟨Q, hq⟩)).symm ≪≫ asIso (DerivedCategory.Q.map g)⟩

private theorem tensor_sheafification_naturality
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    (R : Sheaf J CommRingCat.{u + 1})
    [(J.W.inverseImage (PresheafOfModules.toPresheaf.{u + 1} ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).IsMonoidal] :
    let := monoidalCategory R
    ∀ (A B X Y : SheafOfModules.{u + 1} ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (f : A ⟶ B) (g : X ⟶ Y),
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification B Y).hom =
      (tensorObjIsoSheafification A X).hom ≫
        (PresheafOfModules.sheafification.{u + 1} (𝟙 _)).map (f.val ⊗ₘ g.val) := by
  let := monoidalCategory R
  dsimp only
  intro A B X Y f g
  let S := PresheafOfModules.sheafification.{u + 1}
    (R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (𝟙 _)
  let c := asIso (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (𝟙 _)).counit
  have hf := c.inv.naturality f
  have hg := c.inv.naturality g
  change f ≫ c.inv.app B = c.inv.app A ≫ S.map f.val at hf
  change g ≫ c.inv.app Y = c.inv.app X ≫ S.map g.val at hg
  change (f ⊗ₘ g) ≫ ((c.inv.app B ⊗ₘ c.inv.app Y) ≫
    Functor.LaxMonoidal.μ S B.val Y.val) =
    ((c.inv.app A ⊗ₘ c.inv.app X) ≫ Functor.LaxMonoidal.μ S A.val X.val) ≫
      S.map (f.val ⊗ₘ g.val)
  rw [← Category.assoc, tensorHom_comp_tensorHom, hf, hg,
    ← tensorHom_comp_tensorHom, Category.assoc, Functor.LaxMonoidal.μ_natural,
    Category.assoc]
  rfl

private theorem naturality_comp {D : Type*} [Category* D]
    {A B C A' B' C' : D} {f : A ⟶ A'} {g : B ⟶ B'} {h : C ⟶ C'}
    {s : A ⟶ B} {s' : A' ⟶ B'} {t : B ⟶ C} {t' : B' ⟶ C'}
    (hs : f ≫ s' = s ≫ g) (ht : g ≫ t' = t ≫ h) :
    f ≫ (s' ≫ t') = (s ≫ t) ≫ h := by
  rw [← Category.assoc, hs, Category.assoc, ht, Category.assoc]

private theorem naturality_inv {D : Type*} [Category* D]
    {A B A' B' : D} (i : A ≅ B) (j : A' ≅ B')
    {f : A ⟶ A'} {g : B ⟶ B'} (h : f ≫ j.hom = i.hom ≫ g) :
    g ≫ j.inv = i.inv ≫ f := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem extension_tensor_natural
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R : Sheaf J CommRingCat.{u + 1}) (U : C) :
    let := isMonoidal_W_independentCoefficients R
    let : HasSheafify (J.over U) AddCommGrpCat.{u + 1} :=
      hasSheafify_coefficientUniverse.{u + 1, u, u + 1} (J := J.over U)
    let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1} (J := J.over U)
    let := isMonoidal_W_independentCoefficients (R.over U)
    let := monoidalCategory R
    let : MonoidalCategory (SheafOfModules.{u + 1}
      (((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U)) :=
      monoidalCategory (R.over U)
    let A := (sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
    let L := localizedModuleExtension R U
    let V := localizedModuleRestriction R U
    ∃ e : ∀ (G : SheafOfModules.{u + 1} (A.over U))
      (F : SheafOfModules.{u + 1} A), L.obj (G ⊗ V.obj F) ≅ L.obj G ⊗ F,
      ∀ (G H : SheafOfModules.{u + 1} (A.over U))
        (F E : SheafOfModules.{u + 1} A) (a : G ⟶ H) (b : F ⟶ E),
        L.map (a ⊗ₘ V.map b) ≫ (e H E).hom =
          (e G F).hom ≫ (L.map a ⊗ₘ b) := by
  let := isMonoidal_W_independentCoefficients R
  let : HasSheafify (J.over U) AddCommGrpCat.{u + 1} :=
    hasSheafify_coefficientUniverse.{u + 1, u, u + 1} (J := J.over U)
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1} (J := J.over U)
  let := isMonoidal_W_independentCoefficients (R.over U)
  let := monoidalCategory R
  let := monoidalCategory (R.over U)
  let A := (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let : MonoidalCategory (SheafOfModules.{u + 1} (A.over U)) :=
    monoidalCategory (R.over U)
  let L := localizedModuleExtension R U
  let V := localizedModuleRestriction R U
  obtain ⟨e⟩ := ringedSlice_extension_tensor.{u + 1, u + 1, u} J R U
  refine ⟨fun G F ↦ L.mapIso (tensorObjIsoSheafification (R := R.over U) G (V.obj F)) ≪≫
    e.app (G, F) ≪≫ (tensorObjIsoSheafification (R := R) (L.obj G) F).symm, ?_⟩
  intro G H F E a b
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  have h₁ := congrArg L.map (tensor_sheafification_naturality (R.over U)
    G H (V.obj F) (V.obj E) a (V.map b))
  have h₂ := e.hom.naturality (X := (G, F)) (Y := (H, E)) (a, b)
  have h₃ := tensor_sheafification_naturality R (L.obj G) (L.obj H) F E (L.map a) b
  simp only [Functor.map_comp] at h₁
  simp only [Functor.comp_map, Functor.prod_map, MonoidalCategory.tensor_map] at h₂
  exact naturality_comp h₁ (naturality_comp h₂
    (naturality_inv (tensorObjIsoSheafification (R := R) (L.obj G) F)
      (tensorObjIsoSheafification (R := R) (L.obj H) E) h₃))

private theorem extension_total_iso (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (P : CochainComplex (Mod (R.over U)) ℤ) (Q : CochainComplex (Mod R) ℤ) :
    Nonempty (((localizedModuleExtension R U).mapHomologicalComplex (.up ℤ)).obj
        ((total (R.over U)).obj
          (P, ((localizedModuleRestriction R U).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      (total R).obj
        (((localizedModuleExtension R U).mapHomologicalComplex (.up ℤ)).obj P, Q)) := by
  classical
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory (R.over U)
  letI : MonoidalCategory (SheafOfModules.{u + 1}
      (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U)) :=
    SheafOfModules.monoidalCategory (R.over U)
  let L := localizedModuleExtension R U
  let V := localizedModuleRestriction R U
  haveI : L.IsLeftAdjoint := (localizedModuleAdjunctionIndependent R U).isLeftAdjoint
  let LC := L.mapHomologicalComplex (.up ℤ)
  let VC := V.mapHomologicalComplex (.up ℤ)
  obtain ⟨e, he⟩ := extension_tensor_natural J R U
  let T := (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj P).obj
    (VC.obj Q)
  haveI : L.PreservesTotalComplex T (.up ℤ) := fun _ ↦ inferInstance
  let t := (HomologicalComplex₂.mapTotalIso L T (.up ℤ)).symm
  let f :
      (((L.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj T) ≅
      (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        (LC.obj P)).obj Q :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ e (P.X p) (Q.X q)) (by
          intro q q' hq
          change (e (P.X p) (Q.X q)).hom ≫
            whiskerLeft (L.obj (P.X p)) (Q.d q q') =
            L.map (whiskerLeft (P.X p) (V.map (Q.d q q'))) ≫
              (e (P.X p) (Q.X q')).hom
          have hh := he (P.X p) (P.X p) (Q.X q) (Q.X q') (𝟙 _) (Q.d q q')
          rw [L.map_id, id_tensorHom, id_tensorHom] at hh
          exact hh.symm))
      (by
        intro p p' hp
        apply HomologicalComplex.Hom.ext
        funext q
        change (e (P.X p) (Q.X q)).hom ≫
          whiskerRight (L.map (P.d p p')) (Q.X q) =
          L.map (whiskerRight (P.d p p') (V.obj (Q.X q))) ≫
            (e (P.X p') (Q.X q)).hom
        have hh := he (P.X p) (P.X p') (Q.X q) (Q.X q) (P.d p p') (𝟙 _)
        rw [V.map_id, tensorHom_id, tensorHom_id] at hh
        exact hh.symm)
  exact ⟨t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ)⟩

private theorem tensor_extension_supported (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (a : TensorModel R) (E : Der (R.over U)) (F : Der R) :
    (localizedModuleExtension R U).mapDerivedCategory.essImage
      (a.functor.obj ((localizedModuleExtension R U).mapDerivedCategory.obj E, F)) := by
  let L := localizedModuleExtension R U
  let P := DerivedCategory.Q.objPreimage E
  let N := DerivedCategory.Q.objPreimage F
  obtain ⟨Q, q, hk, hf, hq, _⟩ := CochainComplex.exists_isKFlatResolutionIndependentCoefficients N
  haveI : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  let hQ : resolving R Q := ⟨hk, fun n ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (Q.X n)).symm (hf n)⟩
  let eF : DerivedCategory.Q.obj Q ≅ F :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso F
  let eE : L.mapDerivedCategory.obj E ≅
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P) :=
    L.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
      L.mapDerivedCategoryFactors.app P
  obtain ⟨mixed⟩ := mixedTensor a ((L.mapHomologicalComplex (.up ℤ)).obj P) Q hQ
  obtain ⟨totalIso⟩ := extension_total_iso R U P Q
  let W := (total (R.over U)).obj
    (P, ((localizedModuleRestriction R U).mapHomologicalComplex (.up ℤ)).obj Q)
  let e : a.functor.obj (L.mapDerivedCategory.obj E, F) ≅
      L.mapDerivedCategory.obj (DerivedCategory.Q.obj W) :=
    a.functor.mapIso (Iso.prod eE eF.symm) ≪≫ mixed ≪≫
      DerivedCategory.Q.mapIso totalIso.symm ≪≫ (L.mapDerivedCategoryFactors.app W).symm
  exact Functor.essImage.ofIso e.symm
    (L.mapDerivedCategory.obj_mem_essImage (DerivedCategory.Q.obj W))

/-- The canonical open tensor map is an isomorphism, natural in both derived variables.
The equation characterizes its inverse as the adjunction projection map: its adjunct
is the unit tensored with the restricted coefficient, followed by the inverse of the
canonical restriction-tensor comparison. Thus the direction and normalization are fixed.
The open site is presented on the slice at `ProEt.mk c.i`, with the restricted ring R;
no comparison with any independently chosen coefficient sheaf occurs.

Source: blueprint lemma 1269; Stacks 03DI, 03DJ, 03EL, 06YQ and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece).

Proof:
1. Use lem-weil-proetale-weakly-etale-localization to identify the open site with the
   slice, using only its underlying-site equivalence. Exact extension and restriction
   from lem-pur-site-restriction-module-adjunction-exact act termwise on unbounded
   complexes by lem-sf-exact-functor-derived-triangulated. Choose any representative I
   of E; there is no boundedness requirement on I.
2. Transpose the ordinary unit tensored with the restricted module, using the canonical
   comparison of lem-weil-pbc-ringed-topoi-module-pullback-tensor. For a finite free
   coefficient the resulting map is the finite-sum comparison: identify each inclusion
   by its adjunct. The adjunction proves this comparison invertible, including rank zero.
3. For a splitting i,p from def-weil-pbc-strict-perfect-coefficient-package, first apply
   tensor i, then the finite-free inverse, then extension of tensor p. Naturality and pi=1
   give both inverse laws. Inverting the naturality equation proves naturality for
   arbitrary term maps, independently of the chosen splitting.
4. Both coefficient complexes are K-flat: each term is flat as a retract of a finite
   free sheaf, and lem-pc-bounded-above-flat-kflat-site applies. By
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
   lem-weil-pbc-site-derived-tensor-descent, signed total tensor computes derived tensor.
   For an arbitrary representative I use lem-pc-kflat-resolution; tensoring its
   quasi-isomorphism with the K-flat coefficient preserves quasi-isomorphisms, by
   def-pc-kflat-complex applied to its cone. Exact extension preserves these maps.
5. In degree n sum the inverse term maps over a+r=n. These sums are finite since F is
   bounded. Naturality commutes with both differentials; the second has the same sign
   (-1)^a on each side by def-pc-tensor-complex-sheaves. The total maps are inverse.
   Naturality also holds for homotopies (with sign (-1)^a in the second variable),
   then descends through inversion of quasi-isomorphisms to both derived variables.
   The unit definition identifies the inverse with the stated projection map.
   Adjunction bijectivity determines that inverse, hence the natural isomorphism uniquely.
   (blueprint: lemma-weil-pbc-projection-formula-open-piece-projection-existence). -/
/-
Existence of the normalized open tensor isomorphism. The construction follows
the finite-free retract argument in the proof of blueprint lemma 1269: first
construct the adjunct comparison for finite free coefficients, then transport
it through the degreewise strict-perfect splittings and signed totalization.
The K-flat resolution and descent steps identify this total comparison with the
two derived tensor models. This is the only non-formal existence step; the
main theorem below supplies the formal uniqueness argument.
Source: Stacks 03DI, 03DJ, 03EL, 06YQ and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece).
-/
/- The component of the normalized open projection, written as the adjunction transpose.
This is the local morphism whose natural assembly and invertibility are the two separate
non-formal parts of the existence construction.
Source: Stacks 03DI, 03EL and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece-existence). -/
noncomputable def openTensorProjectionComponent {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) [QuasiCompact c.i]
    (R : Sheaf (ProEt.topology c.Z) CommRingCat.{u + 1})
    (a : TensorModel R) (b : TensorModel (R.over (ProEt.mk c.i)))
    (r : Restriction R (ProEt.mk c.i))
    (t : openTensorRestrictionComparison R (ProEt.mk c.i) a b r)
    (E : Der (R.over (ProEt.mk c.i)))
    (F : (openTensorCoefficients R).FullSubcategory) :
    (openTensorTarget R (ProEt.mk c.i) b).obj (E, F) ⟶
      (openTensorSource R (ProEt.mk c.i) a).obj (E, F) := by
  letI : (localizedModuleRestriction R (ProEt.mk c.i)).Additive :=
    localizedModuleRestriction_additive R (ProEt.mk c.i)
  exact (localizedModuleDerivedAdjunction R (ProEt.mk c.i)).homEquiv
      (b.functor.obj
        (E, (localizedModuleRestriction R (ProEt.mk c.i)).mapDerivedCategory.obj F.obj))
      ((openTensorSource R (ProEt.mk c.i) a).obj (E, F)) |>.symm
    (b.functor.map (CategoryTheory.Prod.mkHom
      ((localizedModuleDerivedAdjunction R (ProEt.mk c.i)).unit.app E) (𝟙 _)) ≫
      t.comparison.inv.app
        ((localizedModuleExtension R (ProEt.mk c.i)).mapDerivedCategory.obj E, F.obj))

/- The component maps assemble naturally in both variables.
The proof is the naturality calculation for the adjunction transpose and the canonical
restriction-tensor comparison; it is isolated so the main theorem only performs the
formal assembly and transport of isomorphisms.
Source: Stacks 03DI, 03EL and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece-existence). -/
theorem openTensorProjection_exists {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) [QuasiCompact c.i]
    (R : Sheaf (ProEt.topology c.Z) CommRingCat.{u + 1})
    (a : TensorModel R) (b : TensorModel (R.over (ProEt.mk c.i)))
    (r : Restriction R (ProEt.mk c.i))
    (t : openTensorRestrictionComparison R (ProEt.mk c.i) a b r) :
    ∃ p : openTensorTarget R (ProEt.mk c.i) b ⟶ openTensorSource R (ProEt.mk c.i) a,
      (∀ (E : Der (R.over (ProEt.mk c.i)))
        (F : (openTensorCoefficients R).FullSubcategory), IsIso (p.app (E, F))) ∧
      ∀ (E : Der (R.over (ProEt.mk c.i)))
        (F : (openTensorCoefficients R).FullSubcategory),
        p.app (E, F) = openTensorProjectionComponent c R a b r t E F  := by
  -- Use support instead of the original finite-free plan: tensoring an extended
  -- object remains extended, so the counit on that tensor is invertible.
  letI : (localizedModuleRestriction R (ProEt.mk c.i)).Additive :=
    localizedModuleRestriction_additive R (ProEt.mk c.i)
  let L := (localizedModuleExtension R (ProEt.mk c.i)).mapDerivedCategory
  let V := (localizedModuleRestriction R (ProEt.mk c.i)).mapDerivedCategory
  let adj := localizedModuleDerivedAdjunction R (ProEt.mk c.i)
  let H := (𝟭 (Der (R.over (ProEt.mk c.i)))).prod
    ((openTensorCoefficients R).ι ⋙ V) ⋙ b.functor
  let tau : H ⟶ openTensorSource R (ProEt.mk c.i) a ⋙ V :=
    { app X := b.functor.map (Prod.mkHom (adj.unit.app X.1) (𝟙 _)) ≫
        t.comparison.inv.app (L.obj X.1, X.2.obj)
      naturality X Y f := by
        have hn :
            Prod.mkHom f.1 (V.map f.2.hom) ≫
                Prod.mkHom (adj.unit.app Y.1) (𝟙 _) =
              Prod.mkHom (adj.unit.app X.1) (𝟙 _) ≫
                (V.prod V).map (Prod.mkHom (L.map f.1) f.2.hom) := by
          ext
          · exact adj.unit.naturality f.1
          · simp
        change b.functor.map (Prod.mkHom f.1 (V.map f.2.hom)) ≫
            (b.functor.map (Prod.mkHom (adj.unit.app Y.1) (𝟙 _)) ≫
              t.comparison.inv.app (L.obj Y.1, Y.2.obj)) =
          (b.functor.map (Prod.mkHom (adj.unit.app X.1) (𝟙 _)) ≫
            t.comparison.inv.app (L.obj X.1, X.2.obj)) ≫
              V.map (a.functor.map (Prod.mkHom (L.map f.1) f.2.hom))
        rw [← Category.assoc, ← b.functor.map_comp, hn,
          b.functor.map_comp, Category.assoc, Category.assoc]
        congr 1
        exact t.comparison.inv.naturality (Prod.mkHom (L.map f.1) f.2.hom) }
  let p : openTensorTarget R (ProEt.mk c.i) b ⟶ openTensorSource R (ProEt.mk c.i) a :=
    { app := fun X ↦ (adj.homEquiv _ _).symm (tau.app X)
      naturality := by
        intro X Y f
        exact adj.homEquiv_naturality_right_square _ _ _ _ (tau.naturality f) }
  refine ⟨p, ?_, ?_⟩
  · intro E F
    letI : IsIso adj.unit := localizedDerivedUnit_isIso c.i R
    letI : L.Full := adj.fullyFaithfulLOfIsIsoUnit.full
    letI : L.Faithful := adj.fullyFaithfulLOfIsIsoUnit.faithful
    haveI : IsIso (adj.counit.app (a.functor.obj (L.obj E, F.obj))) :=
      adj.isIso_counit_app_iff_mem_essImage.mpr
        (tensor_extension_supported R (ProEt.mk c.i) a E F.obj)
    let q : (E, V.obj F.obj) ⟶ (V.obj (L.obj E), V.obj F.obj) :=
      Prod.mkHom (adj.unit.app E) (𝟙 _)
    haveI : IsIso q := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    change IsIso ((adj.homEquiv _ _).symm
      (b.functor.map q ≫ t.comparison.inv.app (L.obj E, F.obj)))
    rw [Adjunction.homEquiv_counit]
    infer_instance
  · intro E F
    rfl

theorem openImmersionTensor_exists {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) [QuasiCompact c.i]
    (R : Sheaf (ProEt.topology c.Z) CommRingCat.{u + 1})
    (a : TensorModel R) (b : TensorModel (R.over (ProEt.mk c.i)))
    (r : Restriction R (ProEt.mk c.i))
    (t : openTensorRestrictionComparison R (ProEt.mk c.i) a b r) :
    letI : (localizedModuleRestriction R (ProEt.mk c.i)).Additive :=
      localizedModuleRestriction_additive R (ProEt.mk c.i)
    ∃ beta : openTensorSource R (ProEt.mk c.i) a ≅
        openTensorTarget R (ProEt.mk c.i) b,
      ∀ (E : Der (R.over (ProEt.mk c.i)))
        (F : (openTensorCoefficients R).FullSubcategory),
        (localizedModuleDerivedAdjunction R (ProEt.mk c.i)).homEquiv _ _
            (beta.inv.app (E, F)) =
          b.functor.map (CategoryTheory.Prod.mkHom
            ((localizedModuleDerivedAdjunction R (ProEt.mk c.i)).unit.app E)
            (𝟙 ((localizedModuleRestriction R (ProEt.mk c.i)).mapDerivedCategory.obj F.obj))) ≫
              t.comparison.inv.app
                ((localizedModuleExtension R (ProEt.mk c.i)).mapDerivedCategory.obj E, F.obj) := by
  obtain ⟨p, hcomp, hp⟩ := openTensorProjection_exists c R a b r t
  haveI : IsIso p := NatIso.isIso_of_isIso_app p
  let beta : openTensorSource R (ProEt.mk c.i) a ≅
      openTensorTarget R (ProEt.mk c.i) b := (asIso p).symm
  refine ⟨beta, ?_⟩
  intro E F
  change (localizedModuleDerivedAdjunction R (ProEt.mk c.i)).homEquiv _ _
      (p.app (E, F)) = _
  rw [hp E F]
  simp [openTensorProjectionComponent]

theorem openImmersionTensor_iso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) [QuasiCompact c.i]
    (R : Sheaf (ProEt.topology c.Z) CommRingCat.{u + 1})
    (a : TensorModel R) (b : TensorModel (R.over (ProEt.mk c.i)))
    (r : Restriction R (ProEt.mk c.i))
    (t : openTensorRestrictionComparison R (ProEt.mk c.i) a b r) :
    openTensorFormula R (ProEt.mk c.i) a b r t := by
  dsimp [openTensorFormula]
  obtain ⟨beta, hbeta⟩ := openImmersionTensor_exists c R a b r t
  refine ⟨beta, hbeta, ?_⟩
  intro beta' hbeta'
  apply Iso.ext_inv
  ext obj
  apply (localizedModuleDerivedAdjunction R (ProEt.mk c.i)).homEquiv _ _ |>.injective
  exact (hbeta' obj.1 obj.2).trans (hbeta obj.1 obj.2).symm

end SheafOfModules
