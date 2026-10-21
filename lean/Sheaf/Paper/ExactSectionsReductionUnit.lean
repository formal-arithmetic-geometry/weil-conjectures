/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.DerivedReductionResolutionIndependence
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Sheaf.Paper.DerivedReductionResolutionIndependence
import Sheaf.CategoryTheory.DerivedCategory.ResolvingAdjunction
import Sheaf.CategoryTheory.DerivedCategory.DerivedMateComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import Mathlib.RingTheory.Flat.CategoryTheory
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Algebra.Homology.PrincipalQuotientQuasiIso

/-! # Exact sections and the principal scalar-extension unit

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 07A6;
derived.tex, Tag 0FND (blueprint: lem-coef-exact-sections-reduction-unit).

The coefficient data and all derived tensor models are those of `PrincipalReduction.Setup`.
The restriction square below is the identity on sections, with its scalar linearity supplied
by the specified coefficient square. In particular it is a canonical identification.

## Main statements

* `SheafOfModules.PrincipalReduction.Setup.exactSectionsReductionUnit`: the natural
  isomorphism, its normalized unit equation, uniqueness, and resolution formulas.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r wO wS wR wA

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

/-- Transport the normalized resolving-class adjunction to a specified counit that
computes on the resolving class. The universal comparison is an isomorphism on that
class, and resolutions and naturality extend this to every derived object.
Source: Stacks 0FND (blueprint: lem-coef-exact-sections-reduction-unit). -/
private theorem transportDerivedAdjunction
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (E : A ⥤ B) (R : B ⥤ A) [E.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : E ⊣ R)
    (p : CochainComplex A ℤ → Prop)
    (res : ∀ X, ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ X), p Y ∧ QuasiIso s)
    (pres : ∀ {X Y} (f : X ⟶ Y), p X → p Y → QuasiIso f →
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f))
    (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (comp : ∀ X, p X → IsIso (ε.app X)) :
    ∃ d : T ⊣ R.mapDerivedCategory, ∀ X K
      (f : (E.mapHomologicalComplex (.up ℤ)).obj X ⟶ K),
      d.homEquiv _ _ (ε.app X ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv X K f) ≫
          R.mapDerivedCategoryFactors.inv.app K := by
  classical
  obtain ⟨_, T₀, ε₀, hu, hc, d₀, hd₀⟩ :=
    Adjunction.exists_leftDerived_adjunction E R a p res pres
  let := hu
  let i := T₀.leftDerivedLift ε₀ (HomologicalComplex.quasiIso A (.up ℤ)) T ε
  have hi X : i.app (DerivedCategory.Q.obj X) ≫ ε₀.app X = ε.app X :=
    T₀.leftDerived_fac_app ε₀ (HomologicalComplex.quasiIso A (.up ℤ)) T ε X
  have hgood X (hX : p X) : IsIso (i.app (DerivedCategory.Q.obj X)) := by
    have := hc X hX
    have := comp X hX
    have : IsIso (i.app (DerivedCategory.Q.obj X) ≫ ε₀.app X) := by
      rw [hi]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (ε₀.app X)
  have : IsIso i := by
    apply (NatTrans.isIso_iff_isIso_app i).2
    intro N
    obtain ⟨P, q, hP, hq⟩ := res (DerivedCategory.Q.objPreimage N)
    have := hq
    let e : DerivedCategory.Q.obj P ≅ N :=
      asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso N
    have := hgood P hP
    exact IsIso.of_isIso_fac_left (i.naturality e.hom)
  refine ⟨d₀.ofNatIsoLeft (asIso i).symm, ?_⟩
  intro X K f
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  simp only [Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app]
  rw [← hi]
  simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hd₀ X K f

namespace SheafOfModules.PrincipalReduction.Setup

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r} ⋙
    forget₂ RingCat.{r} AddCommGrpCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R : Type r} [CommRing R] (D : Setup (C := C) (J := J) R)

/-- Sheaf coefficient restriction, using the recorded Mathlib functor.
Source: Stacks 03DA, 07A6 (blueprint: lem-coef-exact-sections-reduction-unit). -/
abbrev reductionRestriction :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map D.φ)

/-- Exactness of restriction, supplied by the normalized coefficient adjunction.
Source: Stacks 03DA (blueprint: lem-coef-exact-sections-reduction-unit). -/
instance reductionRestrictionLimits : PreservesFiniteLimits D.reductionRestriction :=
  (sheafRingCoefficientOrdinaryAdjunction D.φ).choose

/-- Exactness of restriction, supplied by the normalized coefficient adjunction.
Source: Stacks 03DA (blueprint: lem-coef-exact-sections-reduction-unit). -/
instance reductionRestrictionColimits : PreservesFiniteColimits D.reductionRestriction :=
  (sheafRingCoefficientOrdinaryAdjunction D.φ).choose_spec.choose

/-- Sections and coefficient restriction commute by the identity on the underlying group.
Source: Stacks 03DA, 06YY (blueprint: lem-coef-exact-sections-reduction-unit). -/
def sectionsReductionRestrictionIso :
    D.reductionRestriction ⋙ D.sections ≅
      D.quotientSections ⋙ ModuleCat.restrictScalars D.quotientMap :=
  NatIso.ofComponents (fun M ↦
    (LinearEquiv.toModuleIso
      ({
        toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a x ↦ by
          change ((M.val.obj (op D.U)).smul ((D.φ.hom.app (op D.U)) (D.ρ a))).hom x =
            ((M.val.obj (op D.U)).smul (D.quotientSectionsMap (D.quotientMap a))).hom x
          rw [D.quotient_sections_comm] } :
        ((D.reductionRestriction ⋙ D.sections).obj M) ≃ₗ[R]
          ((D.quotientSections ⋙ ModuleCat.restrictScalars D.quotientMap).obj M))))
    (by intro M N f; ext x; rfl)

variable [HasDerivedCategory.{wO}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S))]
  [HasDerivedCategory.{wR} (ModuleCat.{r} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{r} D.A)]

/-- The derived restriction square induced by the identity on section groups.
Source: Stacks 05RU, 06YY (blueprint: lem-coef-exact-sections-reduction-unit). -/
def derivedSectionsReductionRestrictionIso :
    D.reductionRestriction.mapDerivedCategory ⋙ D.G ≅
      D.G' ⋙ (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso D.reductionRestriction D.sections).symm ≪≫
    Functor.mapDerivedCategoryNatIso D.sectionsReductionRestrictionIso ≪≫
    Functor.mapDerivedCategoryCompIso D.quotientSections
      (ModuleCat.restrictScalars D.quotientMap)

/-- The ordinary quotient representative: extend q and then take quotient sections.
Source: Stacks 06Y6, 06YY (blueprint: lem-coef-exact-sections-reduction-unit). -/
def reductionRepresentative
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
    {Q : CochainComplex (ModuleCat.{r} R) ℤ}
    (q : Q ⟶ (D.sections.mapHomologicalComplex (.up ℤ)).obj P) :=
  ((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).map q ≫
    (D.theta P hf).hom

/-- The ordinary extension/restriction adjunct of the quotient representative.
Source: Stacks 07A6, 0FND (blueprint: lem-coef-exact-sections-reduction-unit). -/
def reductionRepresentativeAdjunct
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
    {Q : CochainComplex (ModuleCat.{r} R) ℤ}
    (q : Q ⟶ (D.sections.mapHomologicalComplex (.up ℤ)).obj P) :=
  ((ModuleCat.extendRestrictScalarsAdj D.quotientMap).mapHomologicalComplex (.up ℤ)).homEquiv
    Q _ (D.reductionRepresentative P hf q)

omit [HasDerivedCategory.{wR} (ModuleCat.{r} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{r} D.A)] in
private theorem ordinaryAdjunction :
    ∃ a : D.extension.E ⊣ D.reductionRestriction,
      ∀ (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))
        (N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S))
        (f : changeOfRings D.φ M ⟶ N) (V : Cᵒᵖ) (x : M.val.obj V),
        (a.homEquiv M N (eqToHom (D.extension.obj_eq M) ≫ f)).val.app V x =
          f.val.app V
            ((CategoryTheory.toSheafify J (changeOfRingsPresheaf D.φ M).presheaf).app V
              ((1 : D.S.obj.obj V) ⊗ₜ[D.O.obj.obj V,(D.φ.hom.app V).hom] x)) :=
  (sheafRingCoefficientOrdinaryAdjunction D.φ).choose_spec.choose_spec
    D.extension.E D.extension.obj_eq D.extension.map_eq

omit [HasDerivedCategory.{wR} (ModuleCat.{r} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{r} D.A)] in
private theorem sheafCounit_adjunction
    (a : D.extension.E ⊣ D.reductionRestriction) :
    ∃ b : D.T ⊣ D.reductionRestriction.mapDerivedCategory,
      ∀ P K (f : D.quotientComplex.obj P ⟶ K),
        b.homEquiv _ _ (D.extension.ε.app P ≫ DerivedCategory.Q.map f) =
          DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
            D.reductionRestriction.mapDerivedCategoryFactors.inv.app K := by
  apply transportDerivedAdjunction D.extension.E D.reductionRestriction a
    (CochainComplex.IsKFlatIndependentCoefficients (R := D.O))
    ?_ D.extension.preserves D.T D.extension.ε D.extension.computes
  intro K
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := D.O) K
  exact ⟨P, p, hP, hp⟩

private theorem restrictionSquare_factors
    (K : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S)) ℤ) :
    D.derivedSectionsReductionRestrictionIso.hom.app (DerivedCategory.Q.obj K) ≫
        (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory.map
          (D.quotientSections.mapDerivedCategoryFactors.hom.app K) ≫
        (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategoryFactors.hom.app
          ((D.quotientSections.mapHomologicalComplex (.up ℤ)).obj K) =
      D.G.map (D.reductionRestriction.mapDerivedCategoryFactors.hom.app K) ≫
        D.sections.mapDerivedCategoryFactors.hom.app
          ((D.reductionRestriction.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex D.sectionsReductionRestrictionIso (.up ℤ)).hom.app K)
    := by
  simp only [derivedSectionsReductionRestrictionIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors D.reductionRestriction D.sections K]
  erw [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact Category.assoc _ _ _

private def ordinaryComparison :
    D.sections ⋙ ModuleCat.extendScalars D.quotientMap ⟶
      D.extension.E ⋙ D.quotientSections where
  app M := D.quotientSectionsTensorHom M
  naturality M N f := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (D.quotientSectionsTensorHom N)
      ((ModuleCat.extendScalars D.quotientMap).map (D.sections.map f)
        ((1 : D.A) ⊗ₜ[R, D.quotientMap] x)) =
      D.quotientSections.map (D.extension.E.map f)
        (D.quotientSectionsTensorHom M ((1 : D.A) ⊗ₜ[R, D.quotientMap] x))
    rw [ModuleCat.ExtendScalars.map_tmul, D.quotientSectionsTensorHom_tmul,
      D.quotientSectionsTensorHom_tmul]
    simp only [map_one, one_smul]
    exact (D.quotientSection_naturality f x).symm

private theorem ordinaryComparison_mate
    (a : D.extension.E ⊣ D.reductionRestriction)
    (ha : ∀ M N (f : changeOfRings D.φ M ⟶ N) V (x : M.val.obj V),
      (a.homEquiv M N (eqToHom (D.extension.obj_eq M) ≫ f)).val.app V x =
        f.val.app V
          ((CategoryTheory.toSheafify J (changeOfRingsPresheaf D.φ M).presheaf).app V
            ((1 : D.S.obj.obj V) ⊗ₜ[D.O.obj.obj V,(D.φ.hom.app V).hom] x)))
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) :
    (ModuleCat.extendRestrictScalarsAdj D.quotientMap).homEquiv _ _
      (D.ordinaryComparison.app M) =
        D.sections.map (a.unit.app M) ≫
          D.sectionsReductionRestrictionIso.hom.app (D.extension.E.obj M) := by
  ext x
  have h := ha M (D.extension.E.obj M) (eqToHom (D.extension.obj_eq M).symm) (op D.U) x
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at h
  change D.quotientSectionsTensorHom M ((1 : D.A) ⊗ₜ[R, D.quotientMap] x) =
    (a.unit.app M).val.app (op D.U) x
  rw [D.quotientSectionsTensorHom_tmul]
  simp only [map_one, one_smul]
  exact h.symm

omit [HasDerivedCategory.{wO}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S))]
  [HasDerivedCategory.{wR} (ModuleCat.{r} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{r} D.A)] in
private theorem sections_t_regular (M : ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J D.O)) (hf : IsFlatOnSite (R := D.O) M) :
    Function.Injective (fun x : D.sections.obj M ↦ D.t • x) := by
  have := D.sectionsLimits
  have := D.sectionsColimits
  have hs := (D.tensorShortComplex_shortExact M hf).map_of_exact D.sections
  have hi := (ModuleCat.mono_iff_injective _).1 hs.mono_f
  intro x y hxy
  apply hi
  change (D.tensorMultiplication M).val.app (op D.U) x =
    (D.tensorMultiplication M).val.app (op D.U) y
  rw [D.tensorMultiplication_apply, D.tensorMultiplication_apply,
    D.terminal.hom_ext (D.terminal.from D.U) (𝟙 D.U)]
  change D.ρ D.t • (show M.val.obj (op D.U) from x) =
    D.ρ D.t • (show M.val.obj (op D.U) from y) at hxy
  simpa using hxy

omit [HasDerivedCategory.{wO}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S))] in
private theorem module_c_isIso
    (K : CochainComplex (ModuleCat.{r} R) ℤ)
    (hK : (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)).kFlat K) :
    IsIso (D.c K) := by
  have := (DerivedCategory.exists_mixedTensor_pointwise_leftDerived
    D.quotientMap D.quotientSingle).choose_spec.choose_spec.2.2 K hK
  unfold c
  infer_instance

/-- A termwise t-regular complex computes principal reduction even without K-flatness:
resolve by flat K-flat terms and apply the principal-quotient quasi-isomorphism lemma.
Source: Stacks 06YY (blueprint: lem-coef-exact-sections-reduction-unit). -/
private theorem c_regular_isIso
    (ht : Function.Injective (fun x : R ↦ D.t * x))
    (K : CochainComplex (ModuleCat.{r} R) ℤ)
    (hK : ∀ i : ℤ, Function.Injective (fun x : K.X i ↦ D.t • x)) :
    IsIso (D.c K) := by
  obtain ⟨Q, q, hq, hf, hQ⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
  have := hq
  have hreg (i : ℤ) : Function.Injective (fun x : Q.X i ↦ D.t • x) := by
    have : Module.Flat R (Q.X i) :=
      (Module.Flat.iff_preservesFiniteLimits_tensorLeft _).2
        ((ObjectProperty.flat_iff_preservesFiniteLimits _).1 (hf i))
    have htr : _root_.IsRegular D.t :=
      ⟨ht, fun x y h ↦ ht (by simpa only [mul_comm] using h)⟩
    exact Module.Flat.isSMulRegular_of_isRegular (M := Q.X i) htr
  have := D.module_c_isIso Q hQ
  have := CochainComplex.PrincipalQuotient.quasiIso_map D.quotientMap D.t
    D.quotient_surjective D.quotient_kernel q hq hreg hK
  have hn := D.c_naturality q
  have : IsIso (D.L.map (DerivedCategory.Q.map q) ≫ D.c K) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (D.L.map (DerivedCategory.Q.map q)) (D.c K)

private theorem alpha_regular_isIso
    (ht : Function.Injective (fun x : R ↦ D.t * x))
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) :
    IsIso (D.alpha P hP hf) := by
  have := D.c_regular_isIso ht ((D.sections.mapHomologicalComplex (.up ℤ)).obj P)
    (fun i ↦ D.sections_t_regular (P.X i) (hf i))
  unfold alpha
  infer_instance

private def moduleCounit : DerivedCategory.Q ⋙ D.L ⟶
    (ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q where
  app := D.c
  naturality _ _ f := (D.c_naturality f).symm

private theorem moduleCounit_adjunction :
    ∃ d : D.L ⊣ (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory,
      ∀ Q K (f : ((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex
          (.up ℤ)).obj Q ⟶ K),
        d.homEquiv _ _ (D.c Q ≫ DerivedCategory.Q.map f) =
          DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj D.quotientMap).mapHomologicalComplex
              (.up ℤ)).homEquiv Q K f) ≫
            (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategoryFactors.inv.app K := by
  apply transportDerivedAdjunction (ModuleCat.extendScalars D.quotientMap)
    (ModuleCat.restrictScalars D.quotientMap)
    (ModuleCat.extendRestrictScalarsAdj D.quotientMap)
    ((HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)).kFlat)
    ?_ ?_ D.L D.moduleCounit D.module_c_isIso
  · intro K
    obtain ⟨Q, q, hq, _, hQ⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
    exact ⟨Q, q, hQ, hq⟩
  · intro K K' f hK hK' hf
    have := hf
    exact (ModuleCat.extendScalars_preservesKFlatQuasiIso D.quotientMap).quasiIso_map hK hK' f

private theorem representative_apply
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
    {Q : CochainComplex (ModuleCat.{r} R) ℤ}
    (q : Q ⟶ (D.sections.mapHomologicalComplex (.up ℤ)).obj P) (i : ℤ) (x : Q.X i) :
    (D.reductionRepresentative P hf q).f i ((1 : D.A) ⊗ₜ[R, D.quotientMap] x) =
      D.quotientSection (P.X i) (q.f i x) := by
  change (D.theta P hf).hom.f i
    ((ModuleCat.extendScalars D.quotientMap).map (q.f i)
      ((1 : D.A) ⊗ₜ[R, D.quotientMap] x)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  have h := (D.existsUnique_theta P hf).exists.choose_spec i 1 (q.f i x)
  simpa only [theta, map_one, one_smul] using h

private theorem representativeAdjunct_apply
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
    {Q : CochainComplex (ModuleCat.{r} R) ℤ}
    (q : Q ⟶ (D.sections.mapHomologicalComplex (.up ℤ)).obj P) (i : ℤ) (x : Q.X i) :
    (D.reductionRepresentativeAdjunct P hf q).f i x =
      D.quotientSection (P.X i) (q.f i x) := by
  change (D.reductionRepresentative P hf q).f i
    ((ModuleCat.extendRestrictScalarsAdj D.quotientMap).unit.app (Q.X i) x) = _
  exact D.representative_apply P hf q i x

/-- Exact sections commute with principal derived reduction, with its actual normalized
scalar-extension unit and both resolution formulas. The coefficient ring need not be a domain.
The auxiliary ordinary adjunction is fixed by its sectionwise formula, and the two derived
adjunctions are fixed by their K-flat unit formulas. Thus none is an arbitrary adjunction.

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 07A6;
derived.tex, Tag 0FND (blueprint: lem-coef-exact-sections-reduction-unit).

Proof:
1. Use the ordinary coefficient adjunction with its sectionwise normalization. Derive it
on the K-flat resolving class and transport it to the specified functor T and counit.
The universal comparison is invertible on K-flat models, hence everywhere by resolutions.
Apply the same construction to ordinary modules and the mixed-tensor counit of L. Both
normalized transpose formulas hold for every cochain map, and imply the required units.
2. Take the adjoint mate of the identity-on-sections restriction square. The mate equation
is the required unit equation, and the adjunction bijection makes its solution unique.
The ordinary comparison sends a tensor x to a times the quotient section of x; its
transpose is sections of the sheaf coefficient unit. The derived mate comparison therefore
identifies this mate on a flat-term K-flat P with the existing theta_P c_Gamma(P).
3. Tensor the coefficient short exact sequence with a flat sheaf and apply exact sections;
this makes t injective on its sections. Resolve an ordinary termwise t-regular complex K
by a flat-term K-flat Q. Regularity of t on R implies regularity on the flat terms of Q,
without any domain hypothesis. The principal-quotient quasi-isomorphism lemma makes the
ordinary extension of q a quasi-isomorphism. Counit naturality and its K-flat computation
then make c_K invertible. Thus the mate is invertible on flat-term K-flat sheaf models.
Resolve any derived object by such a model and use mate naturality to prove invertibility
everywhere, giving the natural isomorphism.
4. The ordinary representative and its adjunct have the stated formulas on 1 tensor x
and x respectively. Counit naturality and cancellation of the model isomorphisms give
the derived representative equation. Its transpose follows from the normalized derived
adjunction. Naturality of the mate along any sheaf resolution identifies the existing
resolvedComparison with this same intrinsic map, proving independence of both resolutions.
At no point is K-flatness of Gamma(P) asserted.
-/
theorem exactSectionsReductionUnit
    (ht : Function.Injective (fun x : R ↦ D.t * x)) :
    ∃ a : D.extension.E ⊣ D.reductionRestriction,
      (∀ (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))
        (V : Cᵒᵖ) (x : M.val.obj V),
        ((eqToHom (D.extension.obj_eq M)).val.app V)
            ((a.unit.app M).val.app V x) =
          ((PresheafOfModules.sheafificationAdjunction
            (R := derivedChangeRingIndependentCoefficients J D.S) (𝟙 _)).unit.app
              (changeOfRingsPresheaf D.φ M)).app V
                ((1 : D.S.obj.obj V) ⊗ₜ[D.O.obj.obj V, (D.φ.hom.app V).hom] x)) ∧
      ∃ b : D.T ⊣ D.reductionRestriction.mapDerivedCategory,
        (∀ (P : CochainComplex
            (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ),
          CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P →
          (∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) →
          b.unit.app (DerivedCategory.Q.obj P) ≫
              D.reductionRestriction.mapDerivedCategory.map (D.extension.ε.app P) ≫
              D.reductionRestriction.mapDerivedCategoryFactors.hom.app
                (D.quotientComplex.obj P) =
            DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P)) ∧
        ∃ d : D.L ⊣ (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory,
          (∀ (Q : CochainComplex (ModuleCat.{r} R) ℤ),
            (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)).kFlat Q →
            (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
            d.unit.app (DerivedCategory.Q.obj Q) ≫
                (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory.map (D.c Q) ≫
                (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategoryFactors.hom.app
                  (((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).obj Q) =
              DerivedCategory.Q.map
                (((ModuleCat.extendRestrictScalarsAdj D.quotientMap).mapHomologicalComplex
                  (.up ℤ)).unit.app Q)) ∧
          ∃ α : D.G ⋙ D.L ≅ D.T ⋙ D.G',
            (∀ N : DerivedCategory
                (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)),
              d.unit.app (D.G.obj N) ≫
                  (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory.map
                    (α.hom.app N) =
                D.G.map (b.unit.app N) ≫
                  D.derivedSectionsReductionRestrictionIso.hom.app (D.T.obj N)) ∧
            (∀ (N : DerivedCategory
                (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)))
              (f : (D.G ⋙ D.L).obj N ⟶ (D.T ⋙ D.G').obj N),
              d.unit.app (D.G.obj N) ≫
                  (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory.map f =
                D.G.map (b.unit.app N) ≫
                  D.derivedSectionsReductionRestrictionIso.hom.app (D.T.obj N) →
              f = α.hom.app N) ∧
            (∀ (P : CochainComplex
                (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
              (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
              (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)),
              α.hom.app (DerivedCategory.Q.obj P) = D.alpha P hP hf) ∧
            (∀ (P : CochainComplex
                (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
              (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
              (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
              (Q : CochainComplex (ModuleCat.{r} R) ℤ)
              (q : Q ⟶ (D.sections.mapHomologicalComplex (.up ℤ)).obj P),
              QuasiIso q →
              (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)).kFlat Q →
              (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
              (∀ (i : ℤ) (x : Q.X i),
                (D.reductionRepresentative P hf q).f i
                    ((1 : D.A) ⊗ₜ[R, D.quotientMap] x) =
                  D.quotientSection (P.X i) (q.f i x)) ∧
              (∀ (i : ℤ) (x : Q.X i),
                (D.reductionRepresentativeAdjunct P hf q).f i x =
                  D.quotientSection (P.X i) (q.f i x)) ∧
              (D.L.map (DerivedCategory.Q.map q) ≫
                  D.L.map (D.sections.mapDerivedCategoryFactors.inv.app P) ≫
                  α.hom.app (DerivedCategory.Q.obj P) ≫
                  D.G'.map (D.modelIso P hP).hom ≫
                  D.quotientSections.mapDerivedCategoryFactors.hom.app (D.quotientComplex.obj P) =
                D.c Q ≫ DerivedCategory.Q.map (D.reductionRepresentative P hf q)) ∧
              (d.homEquiv _ _
                  (D.c Q ≫ DerivedCategory.Q.map (D.reductionRepresentative P hf q)) =
                DerivedCategory.Q.map (D.reductionRepresentativeAdjunct P hf q) ≫
                  (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategoryFactors.inv.app
                    ((D.quotientSections.mapHomologicalComplex (.up ℤ)).obj
                      (D.quotientComplex.obj P)))) ∧
            (∀ (M P : CochainComplex
                (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
              (p : P ⟶ M) [QuasiIso p]
              (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
              (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)),
              D.resolvedComparison p hP hf = α.hom.app (DerivedCategory.Q.obj M)) := by
  classical
  obtain ⟨a, ha⟩ := D.ordinaryAdjunction
  obtain ⟨b, hb⟩ := D.sheafCounit_adjunction a
  obtain ⟨d, hd⟩ := D.moduleCounit_adjunction
  let τ := TwoSquare.mk _ _ _ _ D.derivedSectionsReductionRestrictionIso.hom
  let β : D.G ⋙ D.L ⟶ D.T ⋙ D.G' := ((mateEquiv b d).symm τ).natTrans
  have hβunit N : d.unit.app (D.G.obj N) ≫
      (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategory.map (β.app N) =
    D.G.map (b.unit.app N) ≫
      D.derivedSectionsReductionRestrictionIso.hom.app (D.T.obj N) :=
    (unit_mateEquiv_symm b d τ N).symm
  have hβrep (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ) :
      β.app (DerivedCategory.Q.obj P) ≫ D.G'.map (D.extension.ε.app P) ≫
        D.quotientSections.mapDerivedCategoryFactors.hom.app (D.quotientComplex.obj P) =
      D.L.map (D.sections.mapDerivedCategoryFactors.hom.app P) ≫
        D.c ((D.sections.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((D.ordinaryComparison.mapHomologicalComplex (.up ℤ)).app P) := by
    exact derivedMate_comparison
      (a.mapHomologicalComplex (.up ℤ))
      ((ModuleCat.extendRestrictScalarsAdj D.quotientMap).mapHomologicalComplex (.up ℤ))
      b d D.extension.ε D.moduleCounit
      D.reductionRestriction.mapDerivedCategoryFactors
      (ModuleCat.restrictScalars D.quotientMap).mapDerivedCategoryFactors
      D.sections.mapDerivedCategoryFactors D.quotientSections.mapDerivedCategoryFactors
      hb hd
      (TwoSquare.mk _ _ _ _
        (D.sectionsReductionRestrictionIso.hom.mapHomologicalComplex (.up ℤ)))
      τ D.restrictionSquare_factors
      (D.ordinaryComparison.mapHomologicalComplex (.up ℤ))
      (fun P ↦ by
        ext i : 1
        exact D.ordinaryComparison_mate a ha (P.X i)) P
  have hβmodel (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
      (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) :
      β.app (DerivedCategory.Q.obj P) = D.alpha P hP hf := by
    have hθ : (D.ordinaryComparison.mapHomologicalComplex (.up ℤ)).app P =
        (D.theta P hf).hom := by
      ext i : 1
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      exact (D.quotientSectionsTensorHom_tmul (P.X i) 1 x).trans
        ((D.existsUnique_theta P hf).exists.choose_spec i 1 x).symm
    have hr := hβrep P
    rw [hθ] at hr
    apply (cancel_mono (D.G'.map (D.modelIso P hP).hom)).1
    apply (cancel_mono
      (D.quotientSections.mapDerivedCategoryFactors.hom.app (D.quotientComplex.obj P))).1
    dsimp only [alpha]
    simp only [Category.assoc]
    rw [← D.G'.map_comp_assoc, Iso.inv_hom_id, D.G'.map_id, Category.id_comp,
      Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact hr
  have hβiso : IsIso β := by
    apply (NatTrans.isIso_iff_isIso_app β).2
    intro N
    obtain ⟨P, p, hP, hf, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := D.O)
        (DerivedCategory.Q.objPreimage N)
    have := hp
    have hf' (i : ℤ) : IsFlatOnSite (R := D.O) (P.X i) :=
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso D.O (P.X i)).symm (hf i)
    have : IsIso (β.app (DerivedCategory.Q.obj P)) := by
      rw [hβmodel P hP hf']
      exact D.alpha_regular_isIso ht P hP hf'
    let e : DerivedCategory.Q.obj P ≅ N :=
      asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso N
    exact IsIso.of_isIso_fac_left (β.naturality e.hom)
  refine ⟨a, ?_, b, ?_, d, ?_, asIso β, hβunit, ?_, hβmodel, ?_, ?_⟩
  · intro M V x
    have h := ha M (D.extension.E.obj M) (eqToHom (D.extension.obj_eq M).symm) V x
    simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at h
    have h' := congrArg
      (fun y ↦ ((eqToHom (D.extension.obj_eq M)).val.app V) y) h
    have hu := congrArg (fun f ↦ f.app V
      ((1 : D.S.obj.obj V) ⊗ₜ[D.O.obj.obj V,(D.φ.hom.app V).hom] x))
      (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
        (𝟙 _) (changeOfRingsPresheaf D.φ M))
    simp only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, ← comp_val,
      eqToHom_trans, eqToHom_refl, id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] at h'
    exact h'.trans hu.symm
  · intro P _ _
    have h := hb P (D.quotientComplex.obj P) (𝟙 _)
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id,
      Adjunction.homEquiv_unit] at h
    rw [← Category.assoc, h]
    simp
  · intro Q _ _
    have h := hd Q _ (𝟙 _)
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id,
      Adjunction.homEquiv_unit] at h
    rw [← Category.assoc, h]
    simp
  · intro N f hf
    apply (d.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, hf, ← hβunit]
    rfl
  · intro P hP hf Q q _ _ _
    refine ⟨D.representative_apply P hf q, D.representativeAdjunct_apply P hf q, ?_,
      hd Q _ (D.reductionRepresentative P hf q)⟩
    change D.L.map (DerivedCategory.Q.map q) ≫
      D.L.map (D.sections.mapDerivedCategoryFactors.inv.app P) ≫
        β.app (DerivedCategory.Q.obj P) ≫ D.G'.map (D.modelIso P hP).hom ≫
          D.quotientSections.mapDerivedCategoryFactors.hom.app (D.quotientComplex.obj P) = _
    rw [hβmodel P hP hf]
    dsimp only [alpha]
    simp only [Category.assoc]
    rw [← D.G'.map_comp_assoc, Iso.inv_hom_id, D.G'.map_id,
      Category.id_comp, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rw [← D.L.map_comp_assoc (D.sections.mapDerivedCategoryFactors.inv.app P)
      (D.sections.mapDerivedCategoryFactors.hom.app P), Iso.inv_hom_id_app,
      D.L.map_id, Category.id_comp]
    rw [← Category.assoc, ← D.c_naturality q, Category.assoc,
      ← DerivedCategory.Q.map_comp]
    rfl
  · intro M P p hp hP hf
    dsimp only [resolvedComparison]
    rw [← hβmodel]
    have h := β.naturality (DerivedCategory.Q.map p)
    change (D.G ⋙ D.L).map (inv (DerivedCategory.Q.map p)) ≫
      β.app (DerivedCategory.Q.obj P) ≫ (D.T ⋙ D.G').map (DerivedCategory.Q.map p) = _
    rw [← h, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl

end SheafOfModules.PrincipalReduction.Setup
