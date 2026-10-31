/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.RegularQuotientConeBasic
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.RegularQuotientConeAugmentation
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Tor amplitude after restriction from a regular principal ring-sheaf quotient

Source: Stacks Project, sites-cohomology.tex, Tag 08G1 (bounded flat representatives),
with the regular-principal change-of-rings consequence in the DAG; current blueprint,
sec-smooth-purity/sk-lem-sp-tower/lem-coef-integral-hom-reduction.proof.md, first paragraph
(blueprint: lem-sf-ringed-principal-tor-restriction).

The tensor is the published K-flat site-derived tensor. The coefficient sequence uses
its actual multiplication and ring maps, and restriction is the localization of the
actual termwise restriction functor. Site and coefficient universes remain independent.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r wR wS

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

namespace SheafOfModules

attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] siteDerivedTensorIndependentCoefficients
  KFlatFixedTensor.representativeIso

open RegularQuotientCone

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (ρ : R ⟶ S)
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]

/-- Termwise restriction of ring-sheaf scalars on unbounded derived categories.
This is Mathlib's exact-functor localization of the recorded `restrictScalars`, with
exactness supplied by the recorded ordinary coefficient adjunction. Choosing witnesses
here chooses only proofs of exactness, not a functor or a map.
Source: Stacks Project, Tags 03D7 and 07A6
(blueprint: lem-sf-ringed-principal-tor-restriction). -/
abbrev principalTorRestriction : DerivedCategory (Modules S) ⥤ DerivedCategory (Modules R) :=
  letI := (sheafRingCoefficientOrdinaryAdjunction ρ).choose
  letI := (sheafRingCoefficientOrdinaryAdjunction ρ).choose_spec.choose
  (restriction ρ).mapDerivedCategory

omit [EssentiallySmall.{r} C] in
private theorem twoTerm_tensor_bound
    (F : DerivedCategory (Modules S) ⥤ DerivedCategory (Modules R))
    [F.CommShift ℤ] [F.IsTriangulated]
    (a b : ℤ)
    (hF : ∀ (M : Modules S) (q : ℤ), q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj
        (F.obj ((DerivedCategory.singleFunctor (Modules S) 0).obj M))))
    (E : DerivedCategory (Modules S)) [E.IsGE (-1)] [E.IsLE 0]
    (q : ℤ) (hq : q < a - 1 ∨ b < q) :
    IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj (F.obj E)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE 0).obj E
  have hT : T ∈ distTriang _ := DerivedCategory.TStructure.t.triangleLTGE_distinguished 0 E
  have : T.obj₁.IsGE (-1) := inferInstanceAs
    (DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.TStructure.t.truncLT 0).obj E) (-1))
  have : T.obj₁.IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj E 0 (-1) (by omega)
  have : T.obj₃.IsGE 0 := inferInstanceAs
    (DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.TStructure.t.truncGE 0).obj E) 0)
  have : T.obj₃.IsLE 0 := inferInstanceAs
    (DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncGE 0).obj E) 0)
  obtain ⟨L, ⟨eL⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₁ (-1)
  obtain ⟨H, ⟨eH⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ 0
  have hL : IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj (F.obj T.obj₁)) := by
    apply IsZero.of_iso (hF L (q - (-1)) (by omega))
    exact (DerivedCategory.homologyFunctor (Modules R) q).mapIso (F.mapIso eL ≪≫
      F.mapIso ((((DerivedCategory.singleFunctors (Modules S)).shiftIso
        (1 : ℤ) (-1) 0 (by omega)).app L).symm) ≪≫
      (F.commShiftIso (1 : ℤ)).app _) ≪≫
      ((DerivedCategory.homologyFunctor (Modules R) 0).shiftIso
        (1 : ℤ) q (q - (-1)) (by omega)).app _
  have hH : IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj (F.obj T.obj₃)) := by
    exact (hF H q (by omega)).of_iso
      ((DerivedCategory.homologyFunctor (Modules R) q).mapIso (F.mapIso eH))
  have hex := (F ⋙ DerivedCategory.homologyFunctor (Modules R) q).map_distinguished_exact T hT
  exact hex.isZero_of_both_isZero hL hH

private theorem coefficient_extension_bound
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (d : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} ρ)
    (A : Augmentation ρ t d) (N : Modules R) :
    (d.T.obj ((DerivedCategory.singleFunctor (Modules R) 0).obj N)).IsGE (-1) ∧
      (d.T.obj ((DerivedCategory.singleFunctor (Modules R) 0).obj N)).IsLE 0 := by
  classical
  have hlim := (sheafRingCoefficientOrdinaryAdjunction ρ).choose
  have hcol := (sheafRingCoefficientOrdinaryAdjunction ρ).choose_spec.choose
  let U := restriction ρ
  let V := principalTorRestriction ρ
  let Q₀ : CochainComplex (Modules R) ℤ ⥤ DerivedCategory (Modules R) := DerivedCategory.Q
  let N₀ := (HomologicalComplex.single (Modules R) (.up ℤ) 0).obj N
  let E := d.T.obj (Q₀.obj N₀)
  let UV₀ := U.mapHomologicalComplex (.up ℤ) ⋙
    (DerivedCategory.Q : CochainComplex (Modules R) ℤ ⥤ DerivedCategory (Modules R))
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules S) (.up ℤ)) UV₀ A.V :=
    ⟨A.restriction_factor⟩
  let eV : A.V ≅ V := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules S) (.up ℤ)) UV₀ UV₀ A.V V (Iso.refl _)
  let ec : V.obj E ≅ Q₀.obj ((cone R t).obj N₀) :=
    (eV.app E).symm ≪≫ (A.A.app (Q₀.obj N₀)).symm ≪≫ A.cone_factor.app N₀
  let T := Q₀.mapTriangle.obj (CochainComplex.mappingCone.triangle
    ((complexScalar R t).app N₀))
  have hT : T ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished _
  have hz (q : ℤ) (hq : q < -1 ∨ 0 < q) :
      IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj (V.obj E)) := by
    have hN (i : ℤ) (hi : i ≠ 0) :
        IsZero ((DerivedCategory.homologyFunctor (Modules R) i).obj (Q₀.obj N₀)) := by
      have es := (DerivedCategory.singleFunctorIsoCompQ (Modules R) 0).app N
      apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor (Modules R) i).mapIso es.symm)
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE _ 0 i hi
      · exact DerivedCategory.isZero_of_isLE _ 0 i hi
    have hc : IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj
        (Q₀.obj ((cone R t).obj N₀))) := by
      have hex := DerivedCategory.HomologySequence.exact₃ T hT q (q + 1) rfl
      exact hex.isZero_of_both_isZero (hN q (by omega)) (hN (q + 1) (by omega))
    exact hc.of_iso ((DerivedCategory.homologyFunctor (Modules R) q).mapIso ec)
  have hzE (q : ℤ) (hq : q < -1 ∨ 0 < q) :
      IsZero ((DerivedCategory.homologyFunctor (Modules S) q).obj E) := by
    have he := (U.mapDerivedCategoryHomologyFunctorIso q).app E
    have hu : IsZero (U.obj ((DerivedCategory.homologyFunctor (Modules S) q).obj E)) :=
      (hz q hq).of_iso he
    apply (IsZero.iff_id_eq_zero _).2
    ext W x
    exact congrArg (fun f ↦ f.val.app W x) (hu.eq_of_src (𝟙 _) 0)
  have hE : E.IsGE (-1) ∧ E.IsLE 0 :=
    ⟨(DerivedCategory.isGE_iff E (-1)).2 (fun q hq ↦ hzE q (Or.inl hq)),
      (DerivedCategory.isLE_iff E 0).2 (fun q hq ↦ hzE q (Or.inr hq))⟩
  have : E.IsGE (-1) := hE.1
  have : E.IsLE 0 := hE.2
  let e : E ≅ d.T.obj ((DerivedCategory.singleFunctor (Modules R) 0).obj N) :=
    d.T.mapIso ((DerivedCategory.singleFunctorIsoCompQ (Modules R) 0).app N).symm
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e (-1),
    DerivedCategory.TStructure.t.isLE_of_iso e 0⟩

private theorem complex_tensor_cancellation
    (d : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} ρ)
    (F : CochainComplex (Modules S) ℤ) (P : CochainComplex (Modules R) ℤ) :
    Nonempty (((restriction ρ).mapHomologicalComplex (.up ℤ)).obj
      (((KFlatFixedTensor.totalTensor S).obj F).obj
        ((d.E.mapHomologicalComplex (.up ℤ)).obj P)) ≅
      ((KFlatFixedTensor.totalTensor R).obj
        (((restriction ρ).mapHomologicalComplex (.up ℤ)).obj F)).obj P) := by
  classical
  let := isMonoidal_W_independentCoefficients R
  let := isMonoidal_W_independentCoefficients S
  let := monoidalCategory R
  let := monoidalCategory S
  let E := d.E
  let U := restriction ρ
  obtain ⟨e₀, he₀⟩ := exists_changeOfRings_tensorCancellation_independentCoefficients ρ
  let e (M : SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
      (N : SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
    U.mapIso (((curriedTensor _).obj M).mapIso (eqToIso (d.obj_eq N))) ≪≫ e₀ M N
  have he {M M' : SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj S)}
      {N N' : SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)} (f : M ⟶ M') (g : N ⟶ N') :
      U.map (tensorHom f (E.map g)) ≫ (e M' N').hom =
        (e M N).hom ≫ tensorHom (U.map f) g := by
    have hs : tensorHom f (E.map g) ≫ whiskerLeft M' (eqToHom (d.obj_eq N')) =
        whiskerLeft M (eqToHom (d.obj_eq N)) ≫ tensorHom f (changeOfRingsHom ρ N g) := by
      rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom,
        tensorHom_comp_tensorHom]
      dsimp only [E]
      simp only [Category.comp_id, Category.id_comp, d.map_eq, Category.assoc,
        eqToHom_trans, eqToHom_refl]
    change U.map (tensorHom f (E.map g)) ≫
        U.map (whiskerLeft M' (eqToHom (d.obj_eq N'))) ≫ (e₀ M' N').hom =
      U.map (whiskerLeft M (eqToHom (d.obj_eq N))) ≫ (e₀ M N).hom ≫ tensorHom (U.map f) g
    rw [← U.map_comp_assoc, hs, U.map_comp, Category.assoc, he₀ f g]
  let T := (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj F).obj
    ((E.mapHomologicalComplex (.up ℤ)).obj P)
  have hcolim (D : Type) [Category.{0} D] : PreservesColimitsOfShape D U := by
    have : PreservesColimitsOfShape D (U ⋙ toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape D (toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)))
    have : ReflectsColimitsOfShape D (toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves U (toSheaf _)
  have : PreservesColimitsOfSize.{0, 0} U := ⟨fun {D} instD ↦ @hcolim D instD⟩
  have : U.PreservesTotalComplex T (.up ℤ) := fun _ ↦ inferInstance
  let t := (HomologicalComplex₂.mapTotalIso U T (.up ℤ)).symm
  let f :
      (((U.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj T) ≅
      (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        ((U.mapHomologicalComplex (.up ℤ)).obj F)).obj P :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ HomologicalComplex.Hom.isoOfComponents
        (fun j ↦ e (F.X i) (P.X j)) (by
          intro j j' hj
          change (e (F.X i) (P.X j)).hom ≫ whiskerLeft (U.obj (F.X i)) (P.d j j') =
            U.map (whiskerLeft (F.X i) (E.map (P.d j j'))) ≫
              (e (F.X i) (P.X j')).hom
          have hh := he (𝟙 (F.X i)) (P.d j j')
          change U.map (tensorHom (𝟙 (F.X i)) (E.map (P.d j j'))) ≫
              (e (F.X i) (P.X j')).hom =
            (e (F.X i) (P.X j)).hom ≫ tensorHom (U.map (𝟙 (F.X i))) (P.d j j') at hh
          rw [U.map_id, id_tensorHom, id_tensorHom] at hh
          exact hh.symm))
      (by
        intro i i' hi
        apply HomologicalComplex.Hom.ext
        funext j
        change (e (F.X i) (P.X j)).hom ≫ whiskerRight (U.map (F.d i i')) (P.X j) =
          U.map (whiskerRight (F.d i i') (E.obj (P.X j))) ≫
            (e (F.X i') (P.X j)).hom
        simpa only [E.map_id, tensorHom_id]
          using (he (F.d i i') (𝟙 (P.X j))).symm)
  exact ⟨t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ)⟩

private theorem derived_tensor_cancellation
    (d : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} ρ)
    (F : CochainComplex (Modules S) ℤ) (P : CochainComplex (Modules R) ℤ)
    (hF : CochainComplex.IsKFlatIndependentCoefficients F)
    (hP : CochainComplex.IsKFlatIndependentCoefficients P)
    (hFf : ∀ i, IsFlatOnSite (J := J) (R := S) (F.X i))
    (hPf : ∀ i, IsFlatOnSite (J := J) (R := R) (P.X i)) :
    Nonempty ((principalTorRestriction ρ).obj
      ((siteDerivedTensorIndependentCoefficients J S).obj
        (DerivedCategory.Q.obj F, d.T.obj (DerivedCategory.Q.obj P))) ≅
      (siteDerivedTensorIndependentCoefficients J R).obj
        ((principalTorRestriction ρ).obj (DerivedCategory.Q.obj F),
          DerivedCategory.Q.obj P)) := by
  classical
  have hlim := (sheafRingCoefficientOrdinaryAdjunction ρ).choose
  have hcol := (sheafRingCoefficientOrdinaryAdjunction ρ).choose_spec.choose
  let U := restriction ρ
  let V := principalTorRestriction ρ
  let EP := (d.E.mapHomologicalComplex (.up ℤ)).obj P
  let UF := (U.mapHomologicalComplex (.up ℤ)).obj F
  obtain ⟨sS, hS⟩ := KFlatFixedTensor.kFlat_fixed_tensor_triangulated S
  obtain ⟨sR, hR⟩ := KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
  obtain ⟨cL, _, _⟩ := (hS F hF hFf).2.2.2.1
  obtain ⟨cR, _, _⟩ := (hR P hP hPf).2.2.2.2.1
  have := d.computes P hP
  let eP : d.T.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj EP := asIso (d.ε.app P)
  obtain ⟨e⟩ := complex_tensor_cancellation ρ d F P
  exact ⟨V.mapIso ((siteDerivedTensorIndependentCoefficients J S).mapIso
      (Iso.prod (Iso.refl (DerivedCategory.Q.obj F)) eP)) ≪≫
    V.mapIso (cL.app EP).symm ≪≫
    U.mapDerivedCategoryFactors.app (((KFlatFixedTensor.totalTensor S).obj F).obj EP) ≪≫
    DerivedCategory.Q.mapIso e ≪≫ cR.app UF ≪≫
    (siteDerivedTensorIndependentCoefficients J R).mapIso
      (Iso.prod (U.mapDerivedCategoryFactors.app F).symm (Iso.refl (DerivedCategory.Q.obj P)))⟩

/-- Restriction along a regular principal quotient takes Tor amplitude `[a,b]` to
`[a-1,b]`, testing against every degree-zero module sheaf. The section, multiplication,
ring map and short exactness are the existing ringed-site constructions. No constant
coefficient, constructibility, nonzero-ring or boundedness assumption is added.
Source: Stacks Project, sites-cohomology.tex, Tag 08G1, regular-principal change-of-rings
consequence in the DAG; blueprint lem-coef-integral-hom-reduction.proof.md, first paragraph
(blueprint: lem-sf-ringed-principal-tor-restriction).

Proof:
1. Choose flat-term K-flat representatives F of K and P of each test module N[0].
The fixed-tensor localization comparisons compute the published tensor using F on
one side and P on the other; restriction of F need not be K-flat.
2. The normalized principal quotient augmentation identifies the restriction of
E = N tensor_R^L S with the localized scalar cone on N[0]. Its cone triangle shows
that cohomology vanishes outside [-1,0]. Restriction is exact and retains underlying
sections, so it commutes with cohomology and reflects zero objects. Hence E itself
has cohomology in [-1,0].
3. The natural ordinary tensor cancellation isomorphism extends degreewise to
bicomplexes and then to their signed direct-sum total complexes. Restriction preserves
these direct sums. The fixed-tensor comparisons and the universal extension counit
therefore identify Res(F tensor_S^L E) with Res(F) tensor_R^L N[0].
4. The exact functor Res(F tensor_S^L -) has cohomology in [a,b] on every degree-zero
S-module by the hypothesis. The truncation triangle of E has outer terms concentrated
in degree -1 and degree 0. Their images have cohomology in [a-1,b-1] and [a,b],
respectively, by shift compatibility. The homology exact sequence gives [a-1,b]
for the middle term. Apply the preceding cancellation and representative isomorphisms.
-/
theorem ringedPrincipalTorRestriction
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (hzero : (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) ≫
      ringMap ρ = 0)
    (hexact : (ShortComplex.mk
      ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)))
      (ringMap ρ) hzero).ShortExact)
    (a b : ℤ) (hab : a ≤ b) (K : DerivedCategory (Modules S))
    (hK : ∀ (M : Modules S) (q : ℤ), q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Modules S) q).obj
        ((siteDerivedTensorIndependentCoefficients J S).obj
          (K, (DerivedCategory.singleFunctor (Modules S) 0).obj M)))) :
    ∀ (N : Modules R) (q : ℤ), q < a - 1 ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj
        ((siteDerivedTensorIndependentCoefficients J R).obj
          ((principalTorRestriction ρ).obj K,
            (DerivedCategory.singleFunctor (Modules R) 0).obj N))) := by
  have _hab := hab
  classical
  have hlim := (sheafRingCoefficientOrdinaryAdjunction ρ).choose
  have hcol := (sheafRingCoefficientOrdinaryAdjunction ρ).choose_spec.choose
  let U := restriction ρ
  let V := principalTorRestriction ρ
  let G := (DerivedCategory.Q : CochainComplex (Modules S) ℤ ⥤
    DerivedCategory (Modules S)).objPreimage K
  obtain ⟨F, f, hF, hFflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := S) G
  have : QuasiIso f := hf
  let eF : DerivedCategory.Q.obj F ≅ K := asIso (DerivedCategory.Q.map f) ≪≫
    DerivedCategory.Q.objObjPreimageIso K
  have hFf (i : ℤ) : IsFlatOnSite (J := J) (R := S) (F.X i) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso S _).symm (hFflat i)
  obtain ⟨s, hs⟩ := KFlatFixedTensor.kFlat_fixed_tensor_triangulated S
  let := s
  have : ((KFlatFixedTensor.derivedTensor S).obj (DerivedCategory.Q.obj F)).IsTriangulated :=
    (hs F hF hFf).2.2.1.1
  let Ψ := (KFlatFixedTensor.derivedTensor S).obj (DerivedCategory.Q.obj F) ⋙ V
  have hΨ (M : Modules S) (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj
        (Ψ.obj ((DerivedCategory.singleFunctor (Modules S) 0).obj M))) := by
    let X := (siteDerivedTensorIndependentCoefficients J S).obj
      (DerivedCategory.Q.obj F, (DerivedCategory.singleFunctor (Modules S) 0).obj M)
    have hx : IsZero ((DerivedCategory.homologyFunctor (Modules S) q).obj X) :=
      (hK M q hq).of_iso ((DerivedCategory.homologyFunctor (Modules S) q).mapIso
        ((siteDerivedTensorIndependentCoefficients J S).mapIso (Iso.prod eF (Iso.refl _))))
    exact (U.map_isZero hx).of_iso ((U.mapDerivedCategoryHomologyFunctorIso q).app X).symm
  obtain ⟨d⟩ := nonempty_derivedChangeOfRingsCochainModel.{u, v, r, wR, wS} ρ
  obtain ⟨A⟩ := nonempty_augmentation ρ t hzero hexact d
  intro N q hq
  let N₀ := (HomologicalComplex.single (Modules R) (.up ℤ) 0).obj N
  obtain ⟨P, p, hP, hPflat, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) N₀
  have : QuasiIso p := hp
  let eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (Modules R) 0).obj N :=
    asIso (DerivedCategory.Q.map p) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (Modules R) 0).app N).symm
  have hPf (i : ℤ) : IsFlatOnSite (J := J) (R := R) (P.X i) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R _).symm (hPflat i)
  let E := d.T.obj ((DerivedCategory.singleFunctor (Modules R) 0).obj N)
  obtain ⟨hEge, hEle⟩ := coefficient_extension_bound ρ t d A N
  have hz := twoTerm_tensor_bound Ψ a b hΨ E q hq
  obtain ⟨ec⟩ := derived_tensor_cancellation ρ d F P hF hP hFf hPf
  let e : Ψ.obj E ≅ (siteDerivedTensorIndependentCoefficients J R).obj
      (V.obj K, (DerivedCategory.singleFunctor (Modules R) 0).obj N) :=
    V.mapIso ((siteDerivedTensorIndependentCoefficients J S).mapIso
      (Iso.prod (Iso.refl _) (d.T.mapIso eP.symm))) ≪≫ ec ≪≫
      (siteDerivedTensorIndependentCoefficients J R).mapIso (Iso.prod (V.mapIso eF) eP)
  exact hz.of_iso ((DerivedCategory.homologyFunctor (Modules R) q).mapIso e).symm

end SheafOfModules
