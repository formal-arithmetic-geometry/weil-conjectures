module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import Mathlib.Algebra.Homology.ModelCategory.Injective
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections

/-! # Module injective resolutions compute derived abelian presheaf inclusion

Source: Stacks Project, Cohomology on Sites, Tag 03FD; Derived Categories,
Tags 013K, 013P, 013S, 015E and 05TD
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison).

The comparison is the canonical bounded-below right-derived unit followed by
inverse transport along the augmentation. All choices of resolution and all
strict lifts are quantified over. No injectivity of the underlying abelian
sheaf of an injective module is asserted.

## Main statements

* `exists_resolution`: a nonnegative, degreewise monomorphic module resolution.
* `module_resolution_derived_presheaf_comparison`: termwise inclusion-acyclicity
  and invertibility of the specified derived comparison.
* `abelian_resolution_comparison`: strict comparison to any abelian injective
  resolution, homotopy uniqueness, and the derived identification.
* `module_map_comparison` and `identity_comparison`: naturality and independence.
* `degreeZero_normalization`: identity after the two augmentation identifications.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uA vA uB vB wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ModuleResolutionDerivedPresheaf

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

/-- The localization of a bounded-below quasi-isomorphism, as an isomorphism.
Source: Stacks Project, Derived Categories, Definition 05RU.
This is obtained by the fully faithful inclusion of D⁺ in D, without a choice
of resolution or of a new localized category.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
noncomputable def qIso {K L : CochainComplex.Plus A} (r : K ⟶ L)
    [QuasiIso r.hom] : (DerivedCategory.Plus.Q.obj K) ≅ (DerivedCategory.Plus.Q.obj L) :=
  DerivedCategory.Plus.ι.preimageIso (asIso (DerivedCategory.Q.map r.hom))

/-- The canonical comparison `c_r = R F(Q r)⁻¹ ∘ α_L`.
Source: Stacks Project, Derived Categories, Tag 015E and the canonical
comparison in its statement. `rightDerivedFunctorPlusUnit` is Mathlib's
injective-resolution right-derived unit on bounded-below homotopy categories;
`qIso` retains the actual localization of the augmentation.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
noncomputable def comparison (F : A ⥤ B) [F.Additive] [EnoughInjectives A]
    {K L : CochainComplex.Plus A} (r : K ⟶ L) [QuasiIso r.hom] :
    DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj L) ⟶
      F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) :=
  F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj L) ≫
    (F.rightDerivedFunctorPlus.mapIso (qIso r)).inv

/-- The usual degree-zero single complex, bundled as bounded below.
Source: Stacks Project, Derived Categories, Tag 013K.
The data are Mathlib's single complex; the bound is zero.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
def single (M : A) : CochainComplex.Plus A :=
  ⟨(CochainComplex.singleFunctor A 0).obj M, ⟨0, inferInstance⟩⟩

/-- The canonical identification H⁰(Q(F(M[0]))) ≅ F(M).
Source: Stacks Project, Derived Categories, Tag 05TD, degree-zero calculation.
It composes localization/homology compatibility, the canonical single-complex
comparison, and the homology of a single complex. No derived comparison is
chosen here.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
noncomputable def singleH0 (F : A ⥤ B) [F.Additive] (M : A) :
    (DerivedCategory.Plus.homologyFunctor B 0).obj
      (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj (single M))) ≅ F.obj M :=
  (DerivedCategory.homologyFunctorFactors B 0).app _ ≪≫
    (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) 0).mapIso
      ((F.mapCochainComplexSingleFunctor 0).app M) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj M)

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The underlying ring sheaf of the given commutative ring sheaf.
Source: Stacks Project, Cohomology on Sites, Tag 03FD.
This is the existing sheaf-composition functor, retaining the same sections.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
abbrev ring (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

/-- Enough injectives for ordinary module sheaves on the small ringed site.
Source: Stacks Project, Tags 07A5 and 079H.
This specializes the existing Grothendieck-abelian and enough-injectives
constructions. It introduces no new categorical structure or hypothesis.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
instance moduleEnoughInjectives (R : Sheaf J CommRingCat.{u}) :
    EnoughInjectives (ringedSiteModules.{u} (ring J R)) :=
  letI := SheafOfModules.isGrothendieckAbelian (ring J R)
  inferInstance

/-- Forgetting scalars, using the existing module-to-abelian-sheaf functor.
Source: Stacks Project, Cohomology on Sites, Tag 03FD.
This transparent abbreviation retains Mathlib's objects and natural maps.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
abbrev forget (R : Sheaf J CommRingCat.{u}) := SheafOfModules.toSheaf.{u} (ring J R)

/-- The resolution data quantified over in this node, retaining the actual
ℤ-indexed complex and its augmentation.
Source: Stacks Project, Derived Categories, Tags 013K and 013P.
The separate fields impose exactly termwise monicity, quasi-isomorphism,
injective terms, and vanishing in every negative degree. Using ℤ here allows
all such resolutions, including any choices of zero objects below zero,
rather than replacing the supplied resolution by an ℕ-indexed choice.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
structure Resolution {A : Type uA} [Category.{vA} A] [Abelian A] (M : CochainComplex.Plus A) where
  /-- The given bounded-below complex, not a replacement by a chosen resolution. -/
  complex : CochainComplex.Plus A
  /-- Its specified augmentation. -/
  augmentation : M ⟶ complex
  /-- The augmentation is a monomorphism in every degree. -/
  monic : ∀ n : ℤ, Mono (augmentation.hom.f n)
  /-- The augmentation is a quasi-isomorphism. -/
  quasiIso : QuasiIso augmentation.hom
  /-- All terms are injective objects in the original abelian category. -/
  injective : ∀ n : ℤ, Injective (complex.obj.X n)
  /-- All negative terms are zero objects. -/
  nonnegative : ∀ n : ℤ, n < 0 → IsZero (complex.obj.X n)

attribute [instance] Resolution.quasiIso

/-- The map on degree-zero single complexes induced by a morphism.
Source: Stacks Project, Derived Categories, Tags 013P and 013S.
It is Mathlib's single-functor map bundled in the full subcategory.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
def singleMap {M N : A} (f : M ⟶ N) : single M ⟶ single N :=
  ⟨(CochainComplex.singleFunctor A 0).map f⟩

omit [HasDerivedCategory A] in
private theorem exists_lift {K L T : CochainComplex.Plus A}
    (i : K ⟶ L) [QuasiIso i.hom] (hi : ∀ n, Mono (i.hom.f n))
    (hT : ∀ n, Injective (T.obj.X n)) (g : K ⟶ T) :
    ∃ b : L ⟶ T, i ≫ b = g := by
  open scoped CochainComplex.Plus.modelCategoryQuillen in
    have : Mono i.hom := HomologicalComplex.mono_of_mono_f i.hom hi
    have : Mono i := (CochainComplex.Plus.mono_iff i).2 inferInstance
    have : HomotopicalAlgebra.WeakEquivalence i :=
      (CochainComplex.Plus.modelCategoryQuillen.weakEquivalence_iff i).2 inferInstance
    have : HomotopicalAlgebra.IsFibrant T :=
      (CochainComplex.Plus.modelCategoryQuillen.isFibrant_iff T).2 hT
    let sq : CommSq g i (terminal.from T) (terminal.from L) := ⟨by simp⟩
    exact ⟨sq.lift, sq.fac_left⟩

omit [HasDerivedCategory A] in
private theorem homotopy_lifts {K L T : CochainComplex.Plus A}
    (i : K ⟶ L) [QuasiIso i.hom] (hT : ∀ n, Injective (T.obj.X n))
    (b₁ b₂ : L ⟶ T) (h : i ≫ b₁ = i ≫ b₂) :
    Nonempty (Homotopy b₁.hom b₂.hom) := by
  have : ∀ n, Injective (T.obj.X n) := hT
  obtain ⟨a, ha⟩ := T.property
  exact CochainComplex.homotopy_of_comp_quasiIso_of_injective
    ⟨a, fun n hn ↦ CochainComplex.isZero_of_isStrictlyGE _ a n hn⟩
    i.hom b₁.hom b₂.hom ⟨Homotopy.ofEq (congrArg (fun f ↦ f.hom) h)⟩

private theorem qIso_hom {K L : CochainComplex.Plus A} (r : K ⟶ L)
    [QuasiIso r.hom] : (qIso r).hom = DerivedCategory.Plus.Q.map r := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [qIso, Functor.preimageIso_hom, Functor.map_preimage]
  change DerivedCategory.Q.map r.hom =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map r.hom)
  rfl

omit [HasDerivedCategory A] [HasDerivedCategory B] in
private theorem map_quasiIso_of_acyclic (F : A ⥤ B) [F.Additive]
    [EnoughInjectives A] [PreservesFiniteLimits F]
    {K L : CochainComplex.Plus A} (b : K ⟶ L) [QuasiIso b.hom]
    (hK : ∀ n, F.rightAcyclic (K.obj.X n))
    (hL : ∀ n, F.rightAcyclic (L.obj.X n)) :
    QuasiIso (F.mapCochainComplexPlus.map b).hom := by
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨c, hc⟩ := L.property
  have : K.obj.IsStrictlyGE (min a c) :=
    K.obj.isStrictlyGE_of_ge _ a (min_le_left _ _)
  have : L.obj.IsStrictlyGE (min a c) :=
    L.obj.isStrictlyGE_of_ge _ c (min_le_right _ _)
  exact F.quasiIso_map_of_rightAcyclic b.hom (min a c) hK hL

omit [HasDerivedCategory A] [HasDerivedCategory B] in
private theorem map_quasiIsoAt_zero (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] {K L : CochainComplex.Plus A}
    (r : K ⟶ L) [QuasiIso r.hom]
    (hK : IsZero (K.obj.X (-1))) (hL : IsZero (L.obj.X (-1))) :
    QuasiIsoAt (F.mapCochainComplexPlus.map r).hom 0 := by
  have : F.PreservesLeftHomologyOf (K.obj.sc 0) :=
    F.preservesLeftHomology_of_zero_f _ (by
      have hz : IsZero ((K.obj.sc 0).X₁) := by simpa using hK
      exact hz.eq_of_src _ _)
  have : F.PreservesLeftHomologyOf (L.obj.sc 0) :=
    F.preservesLeftHomology_of_zero_f _ (by
      have hz : IsZero ((L.obj.sc 0).X₁) := by simpa using hL
      exact hz.eq_of_src _ _)
  have : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor A (.up ℤ) 0).map r.hom) :=
    (quasiIsoAt_iff r.hom 0).1 inferInstance
  rw [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F
    ((HomologicalComplex.shortComplexFunctor A (.up ℤ) 0).map r.hom)

private theorem isIso_H0_Q_map {K L : CochainComplex.Plus B} (r : K ⟶ L)
    [QuasiIsoAt r.hom 0] :
    IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map
      (DerivedCategory.Plus.Q.map r)) := by
  have h := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality r 0
  rw [← Iso.eq_comp_inv] at h
  rw [h]
  infer_instance

private theorem comparison_naturality (F : A ⥤ B) [F.Additive] [EnoughInjectives A]
    {K K' L L' : CochainComplex.Plus A}
    (r : K ⟶ L) (r' : K' ⟶ L') [QuasiIso r.hom] [QuasiIso r'.hom]
    (f : K ⟶ K') (t : L ⟶ L') (h : r ≫ t = f ≫ r') :
    DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map t) ≫ comparison F r' =
      comparison F r ≫ F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) := by
  have hn := F.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient A).map t)
  dsimp only [Functor.comp_map] at hn
  have hh : F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map r) ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map t) =
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
        F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map r') := by
    simp only [← Functor.map_comp, h]
  rw [← cancel_mono (F.rightDerivedFunctorPlus.mapIso (qIso r')).hom]
  simp only [comparison, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Functor.mapIso_hom, qIso_hom r', ← hh, ← qIso_hom r]
  simp only [← Functor.mapIso_hom, Iso.inv_hom_id_assoc]
  exact hn

variable (R : Sheaf J CommRingCat.{u})
  [HasDerivedCategory.{wA} (Sheaf J AddCommGrpCat.{u})]
  [HasDerivedCategory.{wB} (Cᵒᵖ ⥤ AddCommGrpCat.{u})]

/-- The underlying abelian augmentation remains a quasi-isomorphism.
Source: Stacks Project, Modules on Sites, Tag 03CO; Cohomology on Sites, Tag 03FD.
This is the existing exact-functor preservation instance applied to forgetting
scalars. It is used only to type the canonical inverse in `comparison`.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
instance underlyingQuasiIso
    (M : ringedSiteModules.{u} (ring J R)) (r : Resolution (single M)) :
    QuasiIso (((forget J R).mapCochainComplexPlus.map r.augmentation).hom) :=
  HomologicalComplex.quasiIso_map_of_preservesHomology r.augmentation.hom (forget J R)

omit [HasDerivedCategory (Sheaf J AddCommGrpCat.{u})]
  [HasDerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u})] in
private theorem forgotten_injective_acyclic
    (I : ringedSiteModules.{u} (ring J R)) [Injective I] :
    (sheafToPresheaf J AddCommGrpCat.{u}).rightAcyclic ((forget J R).obj I) := by
  let : HasExt.{u} (Sheaf J AddCommGrpCat.{u}) := hasExt_of_enoughInjectives _
  intro q
  apply (Functor.isZero_iff _).2
  intro V
  let E := (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj V
  let : Subsingleton (Sheaf.H' ((forget J R).obj I) (q + 1) V.unop) :=
    injective_module_abelian_acyclic V.unop I (q + 1) (Nat.succ_pos q)
  obtain ⟨e⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
    J V.unop (q + 1)
  have hz : IsZero (Sheaf.H' ((forget J R).obj I) (q + 1) V.unop) :=
    AddCommGrpCat.isZero_of_subsingleton _
  exact (hz.of_iso (e.app _).symm).of_iso
    (Functor.rightDerivedCompObjIso (sheafToPresheaf J AddCommGrpCat.{u}) E
      (q + 1) ((forget J R).obj I)).symm

set_option linter.unusedSectionVars false in
/-- Every ordinary module sheaf admits a nonnegative injective resolution with
degreewise monomorphic augmentation.
Source: Stacks Project, Derived Categories, Tag 013K.
Proof (node steps 1–2): module sheaves are Grothendieck abelian by
`prop-pur-kinjective-resolutions-exist`, hence have enough injectives by
`lem-sp-grothendieck-enough-injectives`. Apply
`lem-weil-pbc-left-exact-injective-resolution-degree-zero` (1), extend its
nonnegative injective resolution by zero, and retain its augmentation.
It is monic in degree zero by exactness and in every other degree because
the source is zero. The augmentation is a quasi-isomorphism.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
theorem exists_resolution (M : ringedSiteModules.{u} (ring J R)) :
    Nonempty (Resolution (single M)) := by
  let I := injectiveResolution M
  refine ⟨{
    complex := ⟨I.cochainComplex, 0, inferInstance⟩
    augmentation := ⟨I.ι'⟩
    monic := ?_
    quasiIso := inferInstance
    injective := fun n ↦ inferInstance
    nonnegative := fun n hn ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 n hn }⟩
  intro n
  by_cases hn : n = 0
  · subst n
    change Mono (I.ι'.f 0)
    rw [I.ι'_f_zero]
    infer_instance
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).mono _

/-- Module-injective resolutions are inclusion-acyclic and compute the canonical
right-derived abelian presheaf inclusion as an isomorphism in D⁺.
Source: Stacks Project, Cohomology on Sites, Tag 03FD; Derived Categories, Tag 015E.
Proof (node steps 2–6): forgetting scalars is exact by
`lem-weil-pbc-module-sheaves-colimits-forgetful`, and inclusion is left exact by
`lem-weil-pbc-presheaf-finite-limits-objectwise`. Objectwise kernels and
cokernels (`lem-weil-pbc-presheaf-colimits-sectionwise`) identify
(R^q ι A)(W) with H^q(W,A), by `def-weil-pbc-sites-and-cohomology`.
`lem-sc-injective-module-abelian-acyclic-zariski` therefore gives termwise
ι-acyclicity. Resolve UM by abelian injectives and use
`lem-weil-pbc-lift-along-injective-quasi-iso` to obtain b with b Ur = s.
`lem-weil-pbc-leray-acyclicity-quasi-iso` makes ιb a quasi-isomorphism.
Naturality says α_J Q(ιb) = Rι(Qb) α_UI. Its other three factors are
invertible, so α_UI and then c_r are invertible. This does not require
that UIⁿ be an injective abelian sheaf.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
theorem module_resolution_derived_presheaf_comparison (M : ringedSiteModules.{u} (ring J R))
    (r : Resolution (single M)) :
    (∀ n : ℤ, (sheafToPresheaf J AddCommGrpCat.{u}).rightAcyclic
      ((forget J R).obj (r.complex.obj.X n))) ∧
    IsIso (comparison (sheafToPresheaf J AddCommGrpCat.{u})
      ((forget J R).mapCochainComplexPlus.map r.augmentation)) := by
  have hacyc (n : ℤ) : (sheafToPresheaf J AddCommGrpCat.{u}).rightAcyclic
      ((forget J R).obj (r.complex.obj.X n)) := by
    have := r.injective n
    exact forgotten_injective_acyclic J R _
  refine ⟨hacyc, ?_⟩
  have := Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic
    (sheafToPresheaf J AddCommGrpCat.{u})
      ((forget J R).mapCochainComplexPlus.obj r.complex) hacyc
  unfold comparison
  infer_instance

/-- Comparison with every nonnegative abelian injective resolution, with strict
augmentation compatibility, homotopy uniqueness and the canonical derived image.
Source: Stacks Project, Derived Categories, Tags 013P, 013S and 015E.
Proof (node steps 5–6): Ur is monic and a quasi-isomorphism because forgetting
is exact. Apply `lem-weil-pbc-lift-along-injective-quasi-iso` to Ur and s.
Apply `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy` to any two lifts.
The equality b Ur = s implies that b is a quasi-isomorphism. Its source
and target have ι-acyclic terms, so
`lem-weil-pbc-leray-acyclicity-quasi-iso` applies to ιb. The unit on J is
invertible in the injective-resolution model. Naturality of α and b Ur = s
then give d_s Q(ιb) = c_r, where d_s = Rι(Qs)⁻¹ α_J is exactly
`comparison` on s. Additivity preserves the homotopies.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
theorem abelian_resolution_comparison (M : ringedSiteModules.{u} (ring J R))
    (r : Resolution (single M))
    (s : Resolution ((forget J R).mapCochainComplexPlus.obj (single M))) :
    IsIso (comparison (sheafToPresheaf J AddCommGrpCat.{u}) s.augmentation) ∧
    (∃ b : (forget J R).mapCochainComplexPlus.obj r.complex ⟶ s.complex,
      (forget J R).mapCochainComplexPlus.map r.augmentation ≫ b = s.augmentation) ∧
    (∀ (b₁ b₂ : (forget J R).mapCochainComplexPlus.obj r.complex ⟶ s.complex),
      (forget J R).mapCochainComplexPlus.map r.augmentation ≫ b₁ = s.augmentation →
      (forget J R).mapCochainComplexPlus.map r.augmentation ≫ b₂ = s.augmentation →
      Nonempty (Homotopy b₁.hom b₂.hom)) ∧
    (∀ b : (forget J R).mapCochainComplexPlus.obj r.complex ⟶ s.complex,
      (forget J R).mapCochainComplexPlus.map r.augmentation ≫ b = s.augmentation →
      QuasiIso (((sheafToPresheaf J AddCommGrpCat.{u}).mapCochainComplexPlus.map b).hom) ∧
      DerivedCategory.Plus.Q.map
          ((sheafToPresheaf J AddCommGrpCat.{u}).mapCochainComplexPlus.map b) ≫
        comparison (sheafToPresheaf J AddCommGrpCat.{u}) s.augmentation =
      comparison (sheafToPresheaf J AddCommGrpCat.{u})
        ((forget J R).mapCochainComplexPlus.map r.augmentation)) := by
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  let U := (forget J R).mapCochainComplexPlus
  have hsacyc (n : ℤ) : F.rightAcyclic (s.complex.obj.X n) := by
    have := s.injective n
    exact F.rightAcyclic_of_injective _
  have hsunit := F.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic s.complex hsacyc
  have hs : IsIso (comparison F s.augmentation) := by
    unfold comparison
    infer_instance
  refine ⟨hs, ?_, ?_, ?_⟩
  · apply exists_lift (U.map r.augmentation) _ s.injective s.augmentation
    intro n
    have hm : Mono (r.augmentation.hom.f n) := r.monic n
    change Mono ((forget J R).map (r.augmentation.hom.f n))
    infer_instance
  · intro b₁ b₂ h₁ h₂
    exact homotopy_lifts (U.map r.augmentation) s.injective b₁ b₂
      (h₁.trans h₂.symm)
  · intro b hb
    have hcomp : QuasiIso ((U.map r.augmentation).hom ≫ b.hom) := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, hb]
      infer_instance
    have : QuasiIso b.hom := (quasiIso_iff_comp_left
      (U.map r.augmentation).hom b.hom).1 hcomp
    refine ⟨map_quasiIso_of_acyclic F b
      (module_resolution_derived_presheaf_comparison J R M r).1 hsacyc, ?_⟩
    have hn := comparison_naturality F (U.map r.augmentation) s.augmentation
      (𝟙 _) b (by rw [Category.id_comp]; exact hb)
    simpa only [Functor.map_id, Category.comp_id] using hn

/-- Every module map has strict resolution lifts, unique up to homotopy, and the
canonical comparisons are natural for every such lift.
Source: Stacks Project, Derived Categories, Tags 013P, 013S and 015E.
Proof (node steps 7–8): apply `lem-weil-pbc-lift-along-injective-quasi-iso`
in modules to r and r' f[0]. Apply
`lem-weil-pbc-lift-to-injective-unique-up-to-homotopy` for uniqueness.
Both forgetting and inclusion preserve the resulting homotopy equation.
Set a=Q(Ur), a'=Q(Ur'), g=Q(Ut), h=Q(Uf[0]); the lift equation is ga=a'h.
Naturality of α gives c_r' Q(ιUt) = Rι(a')⁻¹ Rι(g) α_UI
= Rι(h) Rι(a)⁻¹ α_UI = Rι(h)c_r. These equations use the actual
localized augmentation maps, not arbitrary isomorphisms.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
theorem module_map_comparison
    (M N : ringedSiteModules.{u} (ring J R)) (f : M ⟶ N)
    (r : Resolution (single M)) (r' : Resolution (single N)) :
    (∃ t : r.complex ⟶ r'.complex,
      r.augmentation ≫ t = singleMap f ≫ r'.augmentation) ∧
    (∀ t₁ t₂ : r.complex ⟶ r'.complex,
      r.augmentation ≫ t₁ = singleMap f ≫ r'.augmentation →
      r.augmentation ≫ t₂ = singleMap f ≫ r'.augmentation →
      Nonempty (Homotopy t₁.hom t₂.hom)) ∧
    (∀ t : r.complex ⟶ r'.complex,
      r.augmentation ≫ t = singleMap f ≫ r'.augmentation →
      DerivedCategory.Plus.Q.map
          ((sheafToPresheaf J AddCommGrpCat.{u}).mapCochainComplexPlus.map
            ((forget J R).mapCochainComplexPlus.map t)) ≫
        comparison (sheafToPresheaf J AddCommGrpCat.{u})
          ((forget J R).mapCochainComplexPlus.map r'.augmentation) =
      comparison (sheafToPresheaf J AddCommGrpCat.{u})
          ((forget J R).mapCochainComplexPlus.map r.augmentation) ≫
        (sheafToPresheaf J AddCommGrpCat.{u}).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map ((forget J R).mapCochainComplexPlus.map
            (singleMap f)))) := by
  obtain ⟨t, ht⟩ := exists_lift r.augmentation r.monic r'.injective
    (singleMap f ≫ r'.augmentation)
  refine ⟨⟨t, ht⟩, ?_, ?_⟩
  · intro t₁ t₂ h₁ h₂
    exact homotopy_lifts r.augmentation r'.injective t₁ t₂ (h₁.trans h₂.symm)
  · intro t ht
    apply comparison_naturality (sheafToPresheaf J AddCommGrpCat.{u})
    simpa only [← Functor.map_comp] using
      congrArg (forget J R).mapCochainComplexPlus.map ht

/-- The canonical comparison is independent of the chosen module resolution.
Source: Stacks Project, Derived Categories, Tags 013P, 013S and 015E.
Proof (node step 8): use the preceding module-map statement for f=id_M.
The lift t is a quasi-isomorphism since t r=r'. Its underlying abelian
complexes have inclusion-acyclic terms, so
`lem-weil-pbc-leray-acyclicity-quasi-iso` shows that ιUt is a
quasi-isomorphism. Naturality gives the displayed identification; homotopy
uniqueness makes it independent of the lift.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
theorem identity_comparison (M : ringedSiteModules.{u} (ring J R))
    (r r' : Resolution (single M)) :
    ∃ t : r.complex ⟶ r'.complex,
      r.augmentation ≫ t = r'.augmentation ∧
      QuasiIso (((sheafToPresheaf J AddCommGrpCat.{u}).mapCochainComplexPlus.map
        ((forget J R).mapCochainComplexPlus.map t)).hom) ∧
      DerivedCategory.Plus.Q.map
          ((sheafToPresheaf J AddCommGrpCat.{u}).mapCochainComplexPlus.map
            ((forget J R).mapCochainComplexPlus.map t)) ≫
        comparison (sheafToPresheaf J AddCommGrpCat.{u})
          ((forget J R).mapCochainComplexPlus.map r'.augmentation) =
      comparison (sheafToPresheaf J AddCommGrpCat.{u})
        ((forget J R).mapCochainComplexPlus.map r.augmentation)  := by
  obtain ⟨⟨t, ht⟩, _, hn⟩ := module_map_comparison J R M M (𝟙 M) r r'
  have hsingle : singleMap (𝟙 M) = 𝟙 (single M) := by
    apply ObjectProperty.hom_ext
    exact (CochainComplex.singleFunctor _ 0).map_id M
  rw [hsingle, Category.id_comp] at ht
  have hcomp : QuasiIso (r.augmentation.hom ≫ t.hom) := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, ht]
    infer_instance
  have : QuasiIso t.hom := (quasiIso_iff_comp_left
    r.augmentation.hom t.hom).1 hcomp
  have : QuasiIso ((forget J R).mapCochainComplexPlus.map t).hom :=
    HomologicalComplex.quasiIso_map_of_preservesHomology t.hom (forget J R)
  refine ⟨t, ht, map_quasiIso_of_acyclic (sheafToPresheaf J AddCommGrpCat.{u})
    ((forget J R).mapCochainComplexPlus.map t)
    (module_resolution_derived_presheaf_comparison J R M r).1
    (module_resolution_derived_presheaf_comparison J R M r').1, ?_⟩
  simpa only [hsingle, Functor.map_id, Category.comp_id] using
    hn t (by simpa only [hsingle, Category.id_comp] using ht)

/-- In degree zero the comparison is the identity under the kernel identifications
induced by the two augmentations. The equations on the homs specify both
identifications completely; the existential isomorphisms are not arbitrary.
Source: Stacks Project, Derived Categories, Tag 05TD; Tag 013P augmentation equation.
Proof (node step 9): U is exact by
`lem-weil-pbc-module-sheaves-colimits-forgetful`, and ι preserves kernels by
`lem-weil-pbc-presheaf-finite-limits-objectwise`. Since the complexes vanish
below zero, H⁰ is the kernel of d⁰. Thus the augmentation Ur induces eᵣ.
The augmentation s similarly identifies ιUM with H⁰(ιJ); follow it by
H⁰(d_s) to obtain e. The equality b⁰Ur⁰=s⁰ shows that H⁰(ιb) is the
identity between these kernel identifications. Finally d_s Q(ιb)=c_r
from the abelian-resolution comparison gives eᵣ H⁰(c_r) e⁻¹=id.
`singleH0` supplies the canonical H⁰(M[0]) identification in these formulas.
(blueprint: lem-sfb-module-resolution-derived-presheaf-comparison). -/
theorem degreeZero_normalization (M : ringedSiteModules.{u} (ring J R))
    (r : Resolution (single M))
    (s : Resolution ((forget J R).mapCochainComplexPlus.obj (single M))) :
    ∃ (eᵣ : (sheafToPresheaf J AddCommGrpCat.{u}).obj ((forget J R).obj M) ≅
        (DerivedCategory.Plus.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) 0).obj
          (DerivedCategory.Plus.Q.obj
            ((sheafToPresheaf J AddCommGrpCat.{u}).mapCochainComplexPlus.obj
              ((forget J R).mapCochainComplexPlus.obj r.complex))))
      (e : (sheafToPresheaf J AddCommGrpCat.{u}).obj ((forget J R).obj M) ≅
        (DerivedCategory.Plus.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) 0).obj
          ((sheafToPresheaf J AddCommGrpCat.{u}).rightDerivedFunctorPlus.obj
            (DerivedCategory.Plus.Q.obj
              ((forget J R).mapCochainComplexPlus.obj (single M))))),
      eᵣ.hom = (singleH0 (forget J R ⋙ sheafToPresheaf J AddCommGrpCat.{u}) M).inv ≫
        (DerivedCategory.Plus.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) 0).map
          (DerivedCategory.Plus.Q.map
            ((sheafToPresheaf J AddCommGrpCat.{u}).mapCochainComplexPlus.map
              ((forget J R).mapCochainComplexPlus.map r.augmentation))) ∧
      e.hom = (singleH0 (forget J R ⋙ sheafToPresheaf J AddCommGrpCat.{u}) M).inv ≫
        (DerivedCategory.Plus.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) 0).map
          (DerivedCategory.Plus.Q.map
            ((sheafToPresheaf J AddCommGrpCat.{u}).mapCochainComplexPlus.map
              s.augmentation)) ≫
        (DerivedCategory.Plus.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) 0).map
          (comparison (sheafToPresheaf J AddCommGrpCat.{u}) s.augmentation) ∧
      eᵣ.hom ≫
        (DerivedCategory.Plus.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) 0).map
          (comparison (sheafToPresheaf J AddCommGrpCat.{u})
            ((forget J R).mapCochainComplexPlus.map r.augmentation)) ≫
        e.inv = 𝟙 ((sheafToPresheaf J AddCommGrpCat.{u}).obj ((forget J R).obj M)) := by
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  let U := (forget J R).mapCochainComplexPlus
  let H := DerivedCategory.Plus.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) 0
  let a := H.map (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map
    (U.map r.augmentation)))
  let a' := H.map (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map s.augmentation))
  let c := comparison F (U.map r.augmentation)
  let c' := comparison F s.augmentation
  have hneg : IsZero ((U.obj (single M)).obj.X (-1)) :=
    (forget J R).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide))
  have har : QuasiIsoAt (F.mapCochainComplexPlus.map (U.map r.augmentation)).hom 0 :=
    map_quasiIsoAt_zero F (U.map r.augmentation) hneg
      ((forget J R).map_isZero (r.nonnegative (-1) (by decide)))
  have has : QuasiIsoAt (F.mapCochainComplexPlus.map s.augmentation).hom 0 :=
    map_quasiIsoAt_zero F s.augmentation hneg (s.nonnegative (-1) (by decide))
  have : IsIso a := isIso_H0_Q_map _
  have : IsIso a' := isIso_H0_Q_map _
  obtain ⟨hc', ⟨b, hb⟩, _, hbc⟩ := abelian_resolution_comparison J R M r s
  have : IsIso c' := hc'
  have hbcomp := (hbc b hb).2
  have hab : a ≫ H.map c = a' ≫ H.map c' := by
    dsimp only [a, a', c, c']
    rw [← H.map_comp, ← hbcomp, ← Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, hb, H.map_comp]
  let e₀ := singleH0 (forget J R ⋙ F) M
  let eᵣ := e₀.symm ≪≫ asIso a
  let e := e₀.symm ≪≫ asIso a' ≪≫ H.mapIso (asIso c')
  refine ⟨eᵣ, e, rfl, rfl, ?_⟩
  rw [← cancel_mono e.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  change e₀.inv ≫ a ≫ H.map c = e₀.inv ≫ a' ≫ H.map c'
  rw [hab]

end CategoryTheory.ModuleResolutionDerivedPresheaf
