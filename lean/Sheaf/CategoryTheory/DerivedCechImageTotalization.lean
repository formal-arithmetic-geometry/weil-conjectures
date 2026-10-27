/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.CategoryTheory.CoherentCechImageModel
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import all Sheaf.CategoryTheory.CechInjectiveColumnModel
import Sheaf.CategoryTheory.CechAugmentationNormalizedNaturality
import Sheaf.CategoryTheory.CechInjectiveImageAugmentation
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-! # Normalized derived Čech descent after exact inverse image

Source: Stacks Project, sites-cohomology.tex, Tag 03FC; homology.tex, Tag 0133;
derived.tex, Tags 015F and 070I (blueprint: lem-sfb-derived-cech-image-totalization).

The right side is the localization of the signed total of one compatible injective
resolution. Its columns are the ordinary derived direct images. All naturality equations
use actual resolution maps, and therefore also specify the noninvertible coefficient
comparisons. No unbounded product totalization occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u wX wY wB wSlice wR

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The Grothendieck module category has the existing K-injective replacements.
Source: Stacks 079P and 07A5 (blueprint: lem-sfb-derived-cech-image-totalization). -/
instance cechImage_moduleResolutions
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} R) :=
  letI := SheafOfModules.isGrothendieckAbelian R
  inferInstance

/-- Sectionwise localization of modules is additive.
Source: Stacks 04IE (blueprint: lem-sfb-derived-cech-image-totalization).

Proof: the canonical restriction evaluates a module and every morphism at the projected
site object. Addition of module morphisms is pointwise, so restriction preserves sums. -/
theorem cechImage_elementPullback_additive
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u)) :
    (elementModulePullback.{u, u} R A).Additive := by
  constructor
  intro M N f g
  ext U x
  rfl

attribute [instance] cechImage_elementPullback_additive

/-- Existence of the coherent localization presentation, without a chosen arbitrary
map or existence-only replacement for its defining adjunction equations.
Source: Stacks 04IE, 04J4 and 03FC
(blueprint: lem-sfb-derived-cech-image-totalization).

Proof: take the right adjoints of the element-site restriction adjunctions. Transpose
restriction of their counits to define maps for every map of sheaves. The adjunction
bijection and the triangle identities give identities, composition and compatibility
with the localization units. Additivity follows sectionwise. -/
theorem coherentCechImageModel_nonempty
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : Nonempty (CoherentCechImageModel R) := by
  exact ⟨CechColumnAux.model R⟩

namespace CoherentCechImageModel

attribute [local implicit_reducible] bicomplex totalFunctor total
  HomologicalComplex₂.flipFunctor HomologicalComplex₂.totalFunctor
  Functor.mapHomologicalComplex HomologicalComplex₂.flip

variable {C X B : Type u} [SmallCategory C] [SmallCategory X] [SmallCategory B]
  {J : GrothendieckTopology C} {L : GrothendieckTopology X} {N : GrothendieckTopology B}
  {R : Sheaf J RingCat.{u}} {S : Sheaf L RingCat.{u}} {T : Sheaf N RingCat.{u}}
  [HasDerivedCategory.{wX} (ringedSiteModules.{u} R)]
  [HasDerivedCategory.{wY} (ringedSiteModules.{u} S)]
  [HasDerivedCategory.{wB} (ringedSiteModules.{u} T)]

/-- The specified comparison from ordinary right derived direct image of `M[0]`
to the direct image of its resolution, followed by exact inverse image.
Source: Stacks 070I and 015F (blueprint: lem-sfb-derived-cech-image-totalization). -/
def resolutionComparison
    (F : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [F.Additive]
    (H : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} T) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {M : ringedSiteModules.{u} R} (I : InjectiveResolution M)
    (hI : CochainComplex.IsKInjective (I.cocomplex.extend ComplexShape.embeddingUpNat)) :
    H.mapDerivedCategory.obj (F.rightDerivedFunctor.obj
      (DerivedCategory.Q.obj (((CochainComplex.single₀ _).obj M).extend
        ComplexShape.embeddingUpNat))) ⟶
      DerivedCategory.Q.obj
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (I.cocomplex.extend ComplexShape.embeddingUpNat))) :=
  let := hI
  H.mapDerivedCategory.map
      (F.rightDerivedFunctor.map (DerivedCategory.Q.map
        (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)) ≫
        (F.rightDerivedFunctorObjQIso
          (I.cocomplex.extend ComplexShape.embeddingUpNat)).hom) ≫
    H.mapDerivedCategoryFactors.hom.app _

set_option linter.unusedSectionVars false in
/-- Exact inverse image commutes with the finite total. The comparison is fixed on
every diagonal summand, so it respects the sign and augmentation normalization.
Source: Stacks 015F and 0133 (blueprint: lem-sfb-derived-cech-image-totalization).

Proof: an additive functor preserves finite coproducts. At degree r the diagonal
contains only the pairs (n,q) with n+q=r; apply the coproduct comparison and check the
two differentials on summand inclusions. The vertical sign is (-1)^n. -/
theorem finite_total_comparison
    (D : CoherentCechImageModel R) (F : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S)
    [F.Additive] (H : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} T) [H.Additive]
    (V : Sheaf J (Type u)) (I : CochainComplex (ringedSiteModules.{u} R) ℕ) :
    ∃ e : (D.bicomplex (F ⋙ H) V I).total (ComplexShape.up ℕ) ≅
        (H.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((D.bicomplex F V I).total (ComplexShape.up ℕ)),
      ∀ (n q r : ℕ) (hnq : n + q = r),
        (D.bicomplex (F ⋙ H) V I).ιTotal (ComplexShape.up ℕ) n q r hnq ≫ e.hom.f r =
          H.map ((D.bicomplex F V I).ιTotal (ComplexShape.up ℕ) n q r hnq) := by
  classical
  have : H.PreservesTotalComplex (D.bicomplex F V I) (.up ℕ) := fun r ↦ by
    have : Finite ((ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {r}) := by
      apply Set.Finite.to_subtype
      refine (Set.finite_Iic (r, r)).subset ?_
      rintro ⟨n, q⟩ (h : n + q = r)
      simp only [Set.mem_Iic, Prod.mk_le_mk]
      omega
    infer_instance
  let j : D.bicomplex (F ⋙ H) V I ≅
      (H.mapHomologicalComplex₂ (.up ℕ) (.up ℕ)).obj (D.bicomplex F V I) :=
    HomologicalComplex.Hom.isoOfComponents (fun n ↦
      HomologicalComplex.Hom.isoOfComponents (fun q ↦ Iso.refl _) (by
        intros
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        rfl)) (by
          intros
          apply HomologicalComplex.Hom.ext
          funext q
          simp only [HomologicalComplex.comp_f,
            HomologicalComplex.Hom.isoOfComponents_hom_f,
            Iso.refl_hom, Category.comp_id, Category.id_comp]
          rfl)
  let e := HomologicalComplex₂.total.mapIso j (.up ℕ) ≪≫
    HomologicalComplex₂.mapTotalIso H (D.bicomplex F V I) (.up ℕ)
  refine ⟨e, ?_⟩
  intro n q r hnq
  change _ ≫ (HomologicalComplex₂.total.map j.hom (.up ℕ)).f r ≫
    (HomologicalComplex₂.mapTotalXIso H (D.bicomplex F V I) (.up ℕ) r).hom = _
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  change 𝟙 _ ≫ _ ≫ _ = _
  rw [Category.id_comp, HomologicalComplex₂.ι_mapTotalXIso_hom]

/-- Normalized derived descent for the nerve of an arbitrary covering epimorphism.
The complex on the right is the coherent first-quadrant total of the columns
`H R(f v_n)_* (v_n^* M[0])`, not an unspecified triangulated diagram.

Source: Stacks 03FC, 0133, 015F and 070I
(blueprint: lem-sfb-derived-cech-image-totalization).

Proof for stage 3, following the eight DAG steps.
1. Module sheaves are Grothendieck abelian, so take the ordinary nonnegative injective
resolution I. Its zero extension is K-injective (bounded-below injective criterion).
Apply the localization diagram to I; the alternating cofaces commute with its differential.
2. Restriction to every element site is exact and preserves injectives, because it has
an exact left adjoint (04IE, 04J4). Its restricted resolution is K-injective. Thus the
ordinary right-derived units identify all columns with R(f v_n)_* of the restricted module.
3. Evaluate a row at any target object, transpose through f, and localize at the resulting
source sheaf. Present that localization by a small site. Restriction of I^q is injective,
and is an injective module presheaf (03FB). Presheaf-nerve acyclicity (03FC) gives positive
row exactness. Local surjectivity of the cover and sheaf gluing identify degree zero.
4. The first-quadrant column-augmentation criterion makes the specified b a quasi-isomorphism.
Its degree-q component is the localization unit followed by the (0,q) total inclusion.
5. Exact H preserves this quasi-isomorphism. Additivity preserves the finite diagonal sums
and the signs d_Cech + (-1)^n d_res. This gives the claimed derived isomorphism e.
6. The displayed equation fixes e to that augmentation through the ordinary right-derived
comparison. The adjunction triangle identity fixes restriction evaluated on V to the counit.
7. Lift maps between module resolutions. Naturality of localization units gives the
augmentation square. Homotopic lifts give homotopic totals, with homotopy (-1)^n s on the
n-th column. The actual nerve maps give the same square for covering refinements.
8. For exact coefficient restriction P, compare P I to an injective resolution J of P M.
The canonical right-derived unit followed by that comparison represents the coefficient
map. The same augmentation square commutes, independently of the lift by the signed
homotopy calculation. No assertion that these coefficient maps are invertible is needed. -/
theorem derived_cech_image_totalization
    (f : RingedToposMorphism R S) (h : RingedToposMorphism T S)
    [IsIso f.ringMap] [IsIso h.ringMap]
    (fInverse : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} R)
    [fInverse.Additive] [PreservesFiniteLimits fInverse] [PreservesFiniteColimits fInverse]
    (_fAdj : fInverse ⊣ f.modules)
    (H : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} T) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (_hAdj : H ⊣ h.modules)
    (_hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hS : ∀ (U : Xᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    (_hT : ∀ (U : Bᵒᵖ) (a b : T.obj.obj U), a * b = b * a)
    (D : CoherentCechImageModel R)
    (V : Sheaf J (Type u)) [Epi (terminal.from V)]
    (M : ringedSiteModules.{u} R) (I : InjectiveResolution M) :
    ∃ (hI : CochainComplex.IsKInjective (I.cocomplex.extend ComplexShape.embeddingUpNat))
      (a : ((f.modules ⋙ H).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶
        (D.bicomplex (f.modules ⋙ H) V I.cocomplex).X 0)
      (b : ((f.modules ⋙ H).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶
        (D.bicomplex (f.modules ⋙ H) V I.cocomplex).total (ComplexShape.up ℕ))
      (e : H.mapDerivedCategory.obj (f.modules.rightDerivedFunctor.obj
        (DerivedCategory.Q.obj (((CochainComplex.single₀ _).obj M).extend
          ComplexShape.embeddingUpNat))) ≅
        DerivedCategory.Q.obj (D.total (f.modules ⋙ H) V I.cocomplex)),
      (∀ q : ℕ, a.f q = (f.modules ⋙ H).map
        ((D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).app
          (I.cocomplex.X q))) ∧
      (∀ q : ℕ, b.f q = a.f q ≫
        (D.bicomplex (f.modules ⋙ H) V I.cocomplex).ιTotal
          (ComplexShape.up ℕ) 0 q q (zero_add q)) ∧
      resolutionComparison f.modules H I hI ≫
        DerivedCategory.Q.map
          ((I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (f.modules ⋙ H)).hom ≫
            HomologicalComplex.extendMap b ComplexShape.embeddingUpNat) = e.hom := by
  have hI : CochainComplex.IsKInjective
      (I.cocomplex.extend ComplexShape.embeddingUpNat) := inferInstance
  let := hI
  obtain ⟨b₀, hb₀, hq₀, _⟩ :=
    (CechInjectiveImage.cech_injective_image_augmentation f fInverse _fAdj _hR _hS
      D V I.cocomplex (fun q ↦ inferInstance)).total_augmentation
  let := hq₀
  obtain ⟨c, hc⟩ := finite_total_comparison D f.modules H V I.cocomplex
  let b : ((f.modules ⋙ H).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
      (D.bicomplex (f.modules ⋙ H) V I.cocomplex).total (.up ℕ) :=
    (H.mapHomologicalComplex (.up ℕ)).map b₀ ≫ c.inv
  have hb (q : ℕ) : b.f q = (f.modules ⋙ H).map
      ((D.augmentation ((sheafCoverNerve V).obj (op (.mk 0)))).app (I.cocomplex.X q)) ≫
        (D.bicomplex (f.modules ⋙ H) V I.cocomplex).ιTotal
          (.up ℕ) 0 q q (zero_add q) := by
    change H.map (b₀.f q) ≫ c.inv.f q = _
    have hi := congrArg (fun k ↦ k ≫ c.inv.f q) (hc 0 q q (zero_add q))
    simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
      HomologicalComplex.id_f, Category.comp_id] at hi
    erw [hb₀ q, H.map_comp, Category.assoc, ← hi]
    rfl
  have : QuasiIso b := by dsimp only [b]; infer_instance
  have : IsIso (resolutionComparison f.modules H I hI) := by
    dsimp only [resolutionComparison]
    infer_instance
  let e := asIso (resolutionComparison f.modules H I hI ≫
    DerivedCategory.Q.map
      ((I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (f.modules ⋙ H)).hom ≫
        HomologicalComplex.extendMap b ComplexShape.embeddingUpNat))
  refine ⟨hI, CechAugmentationNormalized.columnUnit D (f.modules ⋙ H) V I.cocomplex,
    b, e, fun q ↦ rfl, hb, rfl⟩

set_option linter.unusedSectionVars false in
/-- Each coherent column is computed by the ordinary total right-derived unit at the
restricted injective resolution, followed by exact inverse image.
Source: Stacks 03FC, 04IE, 070I and 015F
(blueprint: lem-sfb-derived-cech-image-totalization).

Proof: exact extension by zero is left adjoint to slice restriction, so restriction
preserves injectives. The restricted nonnegative injective resolution is K-injective.
The right-derived unit is invertible there, and exact inverse image preserves it. -/
theorem column_comparison_isIso
    (D : CoherentCechImageModel R) (F : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S)
    [F.Additive] (H : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} T) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (V : Sheaf J (Type u)) {M : ringedSiteModules.{u} R} (I : InjectiveResolution M)
    (n : ℕ)
    [HasDerivedCategory.{wSlice} (ringedSiteModules.{u}
      (elementRing R ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))))] :
    IsIso (H.mapDerivedCategory.map
      (((D.push ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))) ⋙ F).rightDerivedFunctorUnitQ
          (((elementModulePullback R
            ((sheafCoverNerve V).obj (op (SimplexCategory.mk n)))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
                (I.cocomplex.extend ComplexShape.embeddingUpNat)))) := by
  let A := (sheafCoverNerve V).obj (op (SimplexCategory.mk n))
  obtain ⟨E⟩ := ringed_sheaf_slice_adjunction R A
  have he : E.extensionByZero ⊣ elementModulePullback R A := by
    simpa only [E.pullback_eq] using E.moduleAdjunction
  have : PreservesFiniteLimits E.extensionByZero := E.extensionByZero_exact.1
  have : (elementModulePullback R A).PreservesInjectiveObjects :=
    he.preservesInjectiveObjects_of_preservesFiniteLimits
  have : ∀ q : ℕ, Injective
      (((elementModulePullback R A).mapHomologicalComplex (.up ℕ)).obj I.cocomplex |>.X q) :=
    fun q ↦ Functor.injective_obj (elementModulePullback R A) (I.cocomplex.X q)
  have : CochainComplex.IsKInjective
      (((elementModulePullback R A).mapHomologicalComplex (.up ℤ)).obj
        (I.cocomplex.extend ComplexShape.embeddingUpNat)) :=
    CochainComplex.isKInjective_of_iso
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (elementModulePullback R A)).symm
  rw [Functor.rightDerivedFunctorUnitQ_eq]
  infer_instance

set_option linter.unusedSectionVars false in
/-- Naturality on resolution maps: the canonical augmentation square commutes before
localization. Thus its derived isomorphism is natural in the module and independent of
resolution lifts. Source: Stacks 03FC, 0141 and 070I
(blueprint: lem-sfb-derived-cech-image-totalization).

Proof: the localization units are natural; check the square at every (0,q) summand.
Maps of resolutions inducing a fixed module map are homotopic. Applying restriction and
direct image to that homotopy gives the total homotopy with component (-1)^n s. -/
theorem augmentation_resolution_naturality
    (D : CoherentCechImageModel R) (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} T)
    [G.Additive] (V : Sheaf J (Type u))
    (I I' : CochainComplex (ringedSiteModules.{u} R) ℕ) (t : I ⟶ I')
    (b : (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I ⟶
      (D.totalFunctor G V).obj I)
    (b' : (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I' ⟶
      (D.totalFunctor G V).obj I')
    (hb : D.IsAugmentation G V I b) (hb' : D.IsAugmentation G V I' b') :
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).map t ≫ b' =
      b ≫ (D.totalFunctor G V).map t := by
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hb q, hb' q]
  change G.map (t.f q) ≫ _ ≫ _ = (_ ≫ _) ≫
    (HomologicalComplex₂.total.map _ (.up ℕ)).f q
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
  change G.map (t.f q) ≫ G.map _ ≫ _ =
    G.map _ ≫ G.map (((D.cochains V).map (t.f q)).f 0) ≫ _
  rw [← Category.assoc, ← Category.assoc, ← G.map_comp, ← G.map_comp]
  exact congrArg (fun z ↦ G.map z ≫
    (D.bicomplex G V I').ιTotal (.up ℕ) 0 q q (zero_add q))
      ((D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).naturality
        (t.f q))

set_option linter.unusedSectionVars false in
/-- Naturality for the actual maps of covering nerves, including identities and composites.
Source: Stacks 03FC (blueprint: lem-sfb-derived-cech-image-totalization).

Proof: all nerve maps are restrictions along maps of fibre powers. The localization units
commute with these restrictions by the defining adjunction and its triangle identities.
The augmentation lands in Čech degree zero, where this identity is exactly the square.
Functoriality of the nerve supplies identity and composition compatibility. -/
theorem augmentation_refinement_naturality
    (D : CoherentCechImageModel R) (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} T)
    [G.Additive] {V W : Sheaf J (Type u)} (r : W ⟶ V)
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (b : (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I ⟶
      (D.totalFunctor G V).obj I)
    (b' : (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I ⟶
      (D.totalFunctor G W).obj I)
    (hb : D.IsAugmentation G V I b) (hb' : D.IsAugmentation G W I b') :
    b ≫ D.totalRefinement G r I = b' := by
  exact (CechAugmentationNormalized.refinement_laws D G r (𝟙 _) I I (𝟙 _)
    b b' hb hb').1

/-- The total map obtained from the specified underived coefficient comparisons and
one resolution comparison. No independent map of triangulated diagrams is chosen.
Source: Stacks 03FC, 015F and 070I
(blueprint: lem-sfb-derived-cech-image-totalization). -/
def coefficientTotalMap {R' : Sheaf J RingCat.{u}}
    (D : CoherentCechImageModel R) (D' : CoherentCechImageModel R')
    (P : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} R') [P.Additive]
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} T) [G.Additive]
    (G' : ringedSiteModules.{u} R' ⥤ ringedSiteModules.{u} T) [G'.Additive]
    (V : Sheaf J (Type u))
    (δ : D.cochains V ⋙ G.mapHomologicalComplex (ComplexShape.up ℕ) ⟶
      P ⋙ D'.cochains V ⋙ G'.mapHomologicalComplex (ComplexShape.up ℕ))
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (I' : CochainComplex (ringedSiteModules.{u} R') ℕ)
    (t : (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I ⟶ I') :
    (D.totalFunctor G V).obj I ⟶ (D'.totalFunctor G' V).obj I' :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor _ (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map
      ((NatTrans.mapHomologicalComplex δ (ComplexShape.up ℕ)).app I ≫
        ((D'.cochains V ⋙ G'.mapHomologicalComplex (ComplexShape.up ℕ)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map t)) (ComplexShape.up ℕ)

set_option linter.unusedSectionVars false in
/-- Coefficient naturality and its canonical right-derived normalization. Here `P` is
any exact coefficient restriction, `α` and `δ` are its specified underived commutations,
and `hδ` is their compatibility with restriction units. The map `t` may go from the
restricted resolution to an injective resolution; it need not be an isomorphism.

Source: Stacks 03FC, 015F and 070I
(blueprint: lem-sfb-derived-cech-image-totalization).

Proof: check the augmentation square on each (0,q) summand, where it is hδ followed
by naturality of the localization unit for t^q. For the derived normalization use the
universal right-derived unit at I, the defining factorization of rightDerivedPullback,
and naturality of the target unit at t. Therefore the same total square is the canonical
right-derived coefficient comparison. Replacing t by a homotopic lift gives the same
localized map by the signed total homotopy, so it is independent of the resolution lift. -/
theorem augmentation_coefficient_naturality {R' : Sheaf J RingCat.{u}}
    (D : CoherentCechImageModel R) (D' : CoherentCechImageModel R')
    (P : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} R') [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} T) [G.Additive]
    (G' : ringedSiteModules.{u} R' ⥤ ringedSiteModules.{u} T) [G'.Additive]
    (α : G ⟶ P ⋙ G') (V : Sheaf J (Type u))
    (δ : D.cochains V ⋙ G.mapHomologicalComplex (ComplexShape.up ℕ) ⟶
      P ⋙ D'.cochains V ⋙ G'.mapHomologicalComplex (ComplexShape.up ℕ))
    (hδ : ∀ M : ringedSiteModules.{u} R,
      G.map ((D.augmentation
        ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).app M) ≫ (δ.app M).f 0 =
      α.app M ≫ G'.map ((D'.augmentation
        ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).app (P.obj M)))
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (I' : CochainComplex (ringedSiteModules.{u} R') ℕ)
    (t : (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I ⟶ I')
    (b : (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I ⟶
      (D.totalFunctor G V).obj I)
    (b' : (G'.mapHomologicalComplex (ComplexShape.up ℕ)).obj I' ⟶
      (D'.totalFunctor G' V).obj I')
    (hb : D.IsAugmentation G V I b) (hb' : D'.IsAugmentation G' V I' b') :
    b ≫ coefficientTotalMap D D' P G G' V δ I I' t =
      (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app I ≫
        (G'.mapHomologicalComplex (ComplexShape.up ℕ)).map t ≫ b' := by
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, hb q, hb' q, Category.assoc]
  change _ ≫ _ ≫ (HomologicalComplex₂.total.map _ (.up ℕ)).f q = _
  rw [HomologicalComplex₂.ιTotal_map]
  change G.map _ ≫ (δ.app (I.X q)).f 0 ≫
    G'.map (((D'.cochains V).map (t.f q)).f 0) ≫ _ = _
  rw [← Category.assoc (G.map _) ((δ.app (I.X q)).f 0), hδ, Category.assoc]
  change α.app (I.X q) ≫ G'.map _ ≫
    G'.map ((D'.image.obj (op ((sheafCoverNerve V).obj (op (.mk 0))))).map (t.f q)) ≫ _ = _
  rw [← Category.assoc (G'.map _) (G'.map _), ← G'.map_comp]
  have hn := (D'.augmentation
    ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).naturality (t.f q)
  change t.f q ≫ _ = _ at hn
  erw [← hn, G'.map_comp]
  rfl

/-- The coefficient comparison is the canonical right-derived one, normalized at an
actual resolution map. In particular this statement does not assert its invertibility.
Source: Stacks 015F and 070I (blueprint: lem-sfb-derived-cech-image-totalization).

Proof: the universal right-derived factorization gives the unit square for α at I.
Compose with the right-derived image of t and apply naturality of the target unit.
This is the same comparison represented on the Čech total by coefficientTotalMap. -/
theorem coefficient_derived_normalization {R' : Sheaf J RingCat.{u}}
    [HasDerivedCategory.{wR} (ringedSiteModules.{u} R')]
    (P : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} R') [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} T) [G.Additive]
    (G' : ringedSiteModules.{u} R' ⥤ ringedSiteModules.{u} T) [G'.Additive]
    (α : G ⟶ P ⋙ G') (I : CochainComplex (ringedSiteModules.{u} R) ℤ)
    (I' : CochainComplex (ringedSiteModules.{u} R') ℤ)
    (t : (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ I') :
    G.rightDerivedFunctorUnitQ I ≫ (Functor.rightDerivedPullback P α).app
        (DerivedCategory.Q.obj I) ≫
      G'.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.hom.app I) ≫
      G'.rightDerivedFunctor.map (DerivedCategory.Q.map t) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I ≫
        (G'.mapHomologicalComplex (ComplexShape.up ℤ)).map t) ≫
      G'.rightDerivedFunctorUnitQ I' := by
  rw [Functor.rightDerivedFunctorUnitQ_rightDerivedPullback_app_assoc,
    ← Functor.rightDerivedFunctorUnitQ_naturality, ← DerivedCategory.Q.map_comp_assoc]

set_option linter.unusedSectionVars false in
/-- Independence of resolution lifts in the derived totalization.
Source: Stacks 0141 and 070I (blueprint: lem-sfb-derived-cech-image-totalization).

Proof: apply each localization and direct image to the given homotopy. On the n-th
Čech column multiply it by (-1)^n. The two horizontal contributions cancel and the
vertical contributions are the difference of the total maps. The extended homotopy
makes their images equal under Q. Injective-resolution comparisons of a fixed module
map are homotopic, so the derived naturality square is independent of that choice. -/
theorem total_map_eq_of_homotopy
    (D : CoherentCechImageModel R) (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} T)
    [G.Additive] (V : Sheaf J (Type u))
    {I I' : CochainComplex (ringedSiteModules.{u} R) ℕ} (t t' : I ⟶ I')
    (_s : Homotopy t t') :
    DerivedCategory.Q.map (HomologicalComplex.extendMap
      ((D.totalFunctor G V).map t) ComplexShape.embeddingUpNat) =
    DerivedCategory.Q.map (HomologicalComplex.extendMap
      ((D.totalFunctor G V).map t') ComplexShape.embeddingUpNat) := by
  obtain ⟨s, _⟩ := CechAugmentationNormalized.signed_total_homotopy D G V _s
  exact DerivedCategory.Q_map_eq_of_homotopy (C := ringedSiteModules.{u} T)
    (s.extend ComplexShape.embeddingUpNat)

end CoherentCechImageModel

end CategoryTheory
