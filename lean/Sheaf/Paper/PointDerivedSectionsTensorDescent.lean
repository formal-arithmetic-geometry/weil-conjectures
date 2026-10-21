/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.PointFiniteFreeSectionsTensor
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Sheaf.AlgebraicGeometry.WContractibleAffineEvaluation
import WeilConjectures.RingTheory.WContractibleGeometricCriterion
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Derived descent of the point sections-tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tag 06YY (lemma-derived-base-change),
derived.tex, Tags 015F and 06XN, and categories.tex, Tag 04VG
(blueprint: lem-weil-point-derived-sections-tensor-descent).

The ordinary and derived extensions and their counit are the published constructions.
The assertion retains the representative normalization, every K-flat resolution, and
naturality on roofs. All complexes and derived categories are unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u wE wL
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

section ScalarComparison
variable {l : ℕ} [Fact l.Prime]
  {E L : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  {ι : E →ₐ[ℚ_[l]] L}

attribute [local irreducible] completedScalarChangeData
  completedIntegralCoefficientSheafUnrestricted
private theorem exact_derived_comparison
    {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory C₁]
    {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LF : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    (ε : DerivedCategory.Qh (C := C₁) ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := C₂))
    [LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C₁ (.up ℤ))] :
    ∃ c : F.mapDerivedCategory ≅ LF, ∀ X : CochainComplex C₁ ℤ,
      c.inv.app ((DerivedCategory.Q (C := C₁)).obj X) ≫ F.mapDerivedCategoryFactors.hom.app X =
        ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X) := by
  let : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso C₁ (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  let c := Functor.leftDerivedUnique LF F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh.hom ε (HomotopyCategory.quasiIso C₁ (.up ℤ))
  refine ⟨c, ?_⟩
  intro X
  have hh := Functor.leftDerivedNatTrans_app LF F.mapDerivedCategory ε
    F.mapDerivedCategoryFactorsh.hom (HomotopyCategory.quasiIso C₁ (.up ℤ))
    (𝟙 _) ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
  have hφ : F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj X) =
        F.mapDerivedCategoryFactors.hom.app X := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change F.mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫ (DerivedCategory.Qh (C := C₂)).map (𝟙 _) = _
    erw [F.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := C₂)).map_id]
    simp only [Category.id_comp, Category.comp_id]
  change c.inv.app ((DerivedCategory.Q (C := C₁)).obj X) ≫
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X) =
      ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X) ≫ 𝟙 _ at hh
  simpa only [hφ, Category.comp_id] using hh

private theorem scalar_exact_comparison (Y : Scheme.{t})
    [PreservesFiniteLimits (completedOrdinaryScalarExtension l E L ι Y)]
    [PreservesFiniteColimits (completedOrdinaryScalarExtension l E L ι Y)] :
    ∃ c : (completedOrdinaryScalarExtension l E L ι Y).mapDerivedCategory ≅
      completedDerivedScalarExtension l E L ι Y,
      ∀ X : CochainComplex (integralTowerModules l E Y) ℤ,
        c.inv.app (DerivedCategory.Q.obj X) ≫
            (completedOrdinaryScalarExtension l E L ι Y).mapDerivedCategoryFactors.hom.app X =
          completedScalarCounit l E L ι Y X := by
  let T := (completedScalarChangeData l E L ι Y).choose
  have : T.Additive :=
    (completedScalarChangeData l E L ι Y).choose_spec.choose_spec.choose_spec.choose
  have : PreservesFiniteLimits T :=
    inferInstanceAs (PreservesFiniteLimits (completedOrdinaryScalarExtension l E L ι Y))
  have : PreservesFiniteColimits T :=
    inferInstanceAs (PreservesFiniteColimits (completedOrdinaryScalarExtension l E L ι Y))
  let LF := (completedScalarChangeData l E L ι Y)
    |>.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose
  let ε := (completedScalarChangeData l E L ι Y)
    |>.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose
  have hLF := (completedScalarChangeData l E L ι Y)
    |>.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.1
  have hk := exact_derived_comparison T LF ε
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `hk
        | throwError "missing universal comparison proof"
      (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkFVar hd.fvarId)
    Lean.Elab.Tactic.replaceMainGoal []

end ScalarComparison

namespace PointDerivedSectionsTensor

variable {k : Type t} [Field k] {l : ℕ} [Fact l.Prime]
  {E L : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  {ι : E →ₐ[ℚ_[l]] L} (d : PointFiniteFreeSectionsTensorData k l E L ι)

/-- Sections with their constant-value integral action, at the source coefficient field.
Source: Stacks 03CW (blueprint: lem-weil-point-derived-sections-tensor-descent). -/
abbrev sectionsE := pointFiniteFreeEvaluation k l E d.coefficientE

/-- Sections with their constant-value integral action, at the target coefficient field.
Source: Stacks 03CW (blueprint: lem-weil-point-derived-sections-tensor-descent). -/
abbrev sectionsL := pointFiniteFreeEvaluation k l L d.coefficientL

/-- The source ordinary composite A(C) = Gamma(C) tensor O_L, before localization.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-sections-tensor-descent). -/
abbrev A := sectionsE d ⋙ pointFiniteFreeModuleTensor.{t, u} l E L ι

/-- The target ordinary composite B(C) = Gamma(C tensor R_L), before localization.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-sections-tensor-descent). -/
abbrev B := completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙ sectionsL d

end PointDerivedSectionsTensor

open PointDerivedSectionsTensor

variable {k : Type t} [Field k] {l : ℕ} [Fact l.Prime]
  {E L : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  {ι : E →ₐ[ℚ_[l]] L}
  [HasDerivedCategory.{wE} (ModuleCat.{max u (t + 1)}
    (Padic.coefficientExtensionIntegers l E))]
  [HasDerivedCategory.{wL} (ModuleCat.{max u (t + 1)}
    (Padic.coefficientExtensionIntegers l L))]

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- All clauses of derived descent, with canonical normalization equations. Instance
fields assert exactness rather than assuming it. The equations use Mathlib's specified
factorizations of exact functors; these are the identifications suppressed in the node.
The resolution equation identifies the same theta component for every resolution, hence
also states independence without assuming any comparison map between resolutions.
Source: Stacks 06YY, 015F, 06XN and 04VG
(blueprint: lem-weil-point-derived-sections-tensor-descent). -/
structure PointDerivedSectionsTensorData (d : PointFiniteFreeSectionsTensorData k l E L ι) where
  [sectionsE_additive : (sectionsE d).Additive]
  [sectionsL_additive : (sectionsL d).Additive]
  [sectionsE_limits : PreservesFiniteLimits (sectionsE d)]
  [sectionsE_colimits : PreservesFiniteColimits (sectionsE d)]
  [sectionsL_limits : PreservesFiniteLimits (sectionsL d)]
  [sectionsL_colimits : PreservesFiniteColimits (sectionsL d)]
  [sheaf_limits : PreservesFiniteLimits
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))]
  [sheaf_colimits : PreservesFiniteColimits
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))]
  [module_limits : PreservesFiniteLimits (pointFiniteFreeModuleTensor.{t, u} l E L ι)]
  [module_colimits : PreservesFiniteColimits (pointFiniteFreeModuleTensor.{t, u} l E L ι)]
  sheaf_quasiIso : ∀ (C C' : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ)
    (f : C ⟶ C'), QuasiIso f →
      QuasiIso ((completedOrdinaryScalarComplex l E L ι (Spec (.of k))).map f)
  module_quasiIso : ∀ (C C' : CochainComplex
      (ModuleCat.{max u (t + 1)} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (f : C ⟶ C'), QuasiIso f →
      QuasiIso (((pointFiniteFreeModuleTensor.{t, u} l E L ι).mapHomologicalComplex
        (.up ℤ)).map f)
  sectionsE_quasiIso : ∀ (C C' : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ)
    (f : C ⟶ C'), QuasiIso f →
      QuasiIso (((sectionsE d).mapHomologicalComplex (.up ℤ)).map f)
  sectionsL_quasiIso : ∀ (C C' : CochainComplex (integralTowerModules l L (Spec (.of k))) ℤ)
    (f : C ⟶ C'), QuasiIso f →
      QuasiIso (((sectionsL d).mapHomologicalComplex (.up ℤ)).map f)
  comparison : (completedOrdinaryScalarExtension l E L ι (Spec (.of k))).mapDerivedCategory ≅
    completedDerivedScalarExtension l E L ι (Spec (.of k))
  comparison_counit : ∀ C : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ,
    comparison.inv.app (DerivedCategory.Q.obj C) ≫
        (completedOrdinaryScalarExtension l E L ι (Spec (.of k))).mapDerivedCategoryFactors.hom.app
          C = completedScalarCounit l E L ι (Spec (.of k)) C
  comparison_unique : ∀ δ :
      (completedOrdinaryScalarExtension l E L ι (Spec (.of k))).mapDerivedCategory ≅
        completedDerivedScalarExtension l E L ι (Spec (.of k)),
    (∀ C : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ,
      δ.inv.app (DerivedCategory.Q.obj C) ≫
          (completedOrdinaryScalarExtension l E L ι
            (Spec (.of k))).mapDerivedCategoryFactors.hom.app C =
        completedScalarCounit l E L ι (Spec (.of k)) C) → δ = comparison
  localized : (A d).mapDerivedCategory ≅ (B d).mapDerivedCategory
  localized_representative : ∀ C : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ,
    localized.hom.app (DerivedCategory.Q.obj C) ≫ (B d).mapDerivedCategoryFactors.hom.app C =
      (A d).mapDerivedCategoryFactors.hom.app C ≫ DerivedCategory.Q.map (d.complexes.hom.app C)
  localized_unique : ∀ τ : (A d).mapDerivedCategory ⟶ (B d).mapDerivedCategory,
    (∀ C : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ,
      τ.app (DerivedCategory.Q.obj C) ≫ (B d).mapDerivedCategoryFactors.hom.app C =
        (A d).mapDerivedCategoryFactors.hom.app C ≫
          DerivedCategory.Q.map (d.complexes.hom.app C)) → τ = localized.hom
  theta : (sectionsE d).mapDerivedCategory ⋙
      (pointFiniteFreeModuleTensor.{t, u} l E L ι).mapDerivedCategory ≅
    completedDerivedScalarExtension l E L ι (Spec (.of k)) ⋙ (sectionsL d).mapDerivedCategory
  theta_eq : theta =
    (Functor.mapDerivedCategoryCompIso (sectionsE d)
      (pointFiniteFreeModuleTensor.{t, u} l E L ι)).symm ≪≫ localized ≪≫
    Functor.mapDerivedCategoryCompIso
      (completedOrdinaryScalarExtension l E L ι (Spec (.of k))) (sectionsL d) ≪≫
    Functor.isoWhiskerRight comparison (sectionsL d).mapDerivedCategory
  resolution : ∀ (C P : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ)
    (q : P ⟶ C) [QuasiIso q],
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))) P →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology (Spec (.of k)))
      (R := completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))) (P.X i)) →
    (Functor.mapDerivedCategoryCompIso (sectionsE d)
        (pointFiniteFreeModuleTensor.{t, u} l E L ι)).hom.app (DerivedCategory.Q.obj C) ≫
      theta.hom.app (DerivedCategory.Q.obj C) ≫
        (sectionsL d).mapDerivedCategory.map
          (inv ((completedDerivedScalarExtension l E L ι (Spec (.of k))).map
            (DerivedCategory.Q.map q)) ≫ completedScalarCounit l E L ι (Spec (.of k)) P) ≫
        (sectionsL d).mapDerivedCategoryFactors.hom.app
          ((completedOrdinaryScalarComplex l E L ι (Spec (.of k))).obj P) =
      inv ((A d).mapDerivedCategory.map (DerivedCategory.Q.map q)) ≫
        (A d).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map (d.complexes.hom.app P)
  roof : ∀ (C H J : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ)
    (q : H ⟶ C) (f : H ⟶ J) [QuasiIso q],
    localized.hom.app (DerivedCategory.Q.obj C) ≫
        inv ((B d).mapDerivedCategory.map (DerivedCategory.Q.map q)) ≫
        (B d).mapDerivedCategory.map (DerivedCategory.Q.map f) =
      inv ((A d).mapDerivedCategory.map (DerivedCategory.Q.map q)) ≫
        (A d).mapDerivedCategory.map (DerivedCategory.Q.map f) ≫
        localized.hom.app (DerivedCategory.Q.obj J)

private theorem point_sections_surjective (k : Type t) [Field k] [IsAlgClosed k]
    (F G : Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (max u (t + 1))))
    (f : F ⟶ G) [Epi f] :
    Function.Surjective (f.hom.app (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := by
  classical
  have : WLocalSpace (PrimeSpectrum k) :=
    { eq_of_specializes := fun _ _ _ _ ↦ Subsingleton.elim _ _
      isClosed_closedPoints := by
        have : closedPoints (PrimeSpectrum k) = Set.univ := by
          ext x
          simp only [Set.mem_univ, iff_true]
          exact mem_closedPoints_iff.mpr isClosed_singleton
        rw [this]
        exact isClosed_univ }
  have : IsWLocalRing k := ⟨inferInstance⟩
  have : IsAlgClosed (IsLocalRing.ResidueField k) :=
    IsAlgClosed.of_ringEquiv k _
      (RingEquiv.ofBijective (IsLocalRing.residue k)
        ⟨(IsLocalRing.residue k).injective, IsLocalRing.residue_surjective⟩)
  have : IsStrictlyHenselianLocalRing k := ⟨inferInstance⟩
  have hstrict (m : Ideal k) [m.IsMaximal] :
      IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
    apply IsStrictlyHenselianLocalRing.of_ringEquiv
      (IsLocalization.atUnits k m.primeCompl (S := Localization.AtPrime m) ?_).toRingEquiv
    intro x hx
    exact isUnit_iff_ne_zero.mpr (fun he ↦ hx (he ▸ m.zero_mem))
  exact Scheme.ProEt.surjective_app_of_affine_ring_retractions (Spec (.of k)) k (𝟙 _)
    (fun B _ φ hf hw ↦
      RingHom.exists_retraction_of_wlocal_geometric_criterion hstrict φ hf hw) F G f

private theorem point_sections_exact (k : Type t) [Field k] [IsAlgClosed k]
    (R : Sheaf (Scheme.ProEt.topology (Spec (.of k))) RingCat.{max u (t + 1)})
    (S : Type u) [Ring S] (e : S →+* R.obj.obj (pointFiniteFreeFinal k)) :
    PreservesFiniteLimits
      (SheafOfModules.evaluation.{max u (t + 1)} R (pointFiniteFreeFinal k) ⋙
        ModuleCat.restrictScalars e) ∧
    PreservesFiniteColimits
      (SheafOfModules.evaluation.{max u (t + 1)} R (pointFiniteFreeFinal k) ⋙
        ModuleCat.restrictScalars e) := by
  let ev := SheafOfModules.evaluation.{max u (t + 1)} R (pointFiniteFreeFinal k)
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    let g := (SheafOfModules.toSheaf R).map f
    have : Epi g := inferInstance
    have : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u (t + 1)} g).mpr inferInstance
    let g' := (sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
      (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).map g
    have : Epi g' := inferInstance
    exact (ModuleCat.epi_iff_surjective (ev.map f)).mpr
      (point_sections_surjective k _ _ g')
  have : ev.Additive := ⟨by intros; rfl⟩
  have : ev.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels ev
  have : PreservesFiniteLimits ev := Functor.preservesFiniteLimits_of_preservesHomology ev
  have : PreservesFiniteColimits ev := Functor.preservesFiniteColimits_of_preservesHomology ev
  let T := ModuleCat.restrictScalars.{max u (t + 1)} e
  let V := forget₂ (ModuleCat.{max u (t + 1)} S) AddCommGrpCat.{max u (t + 1)}
  have : PreservesFiniteLimits (T ⋙ V) :=
    inferInstanceAs (PreservesFiniteLimits
      (forget₂ (ModuleCat.{max u (t + 1)} (R.obj.obj (pointFiniteFreeFinal k)))
        AddCommGrpCat.{max u (t + 1)}))
  have : PreservesFiniteColimits (T ⋙ V) := by
    change PreservesFiniteColimits
      (forget₂ (ModuleCat.{max u (t + 1)} (R.obj.obj (pointFiniteFreeFinal k)))
        AddCommGrpCat.{max u (t + 1)})
    infer_instance
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_reflects_of_preserves T V
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_reflects_of_preserves T V
  exact ⟨comp_preservesFiniteLimits ev T, comp_preservesFiniteColimits ev T⟩

private theorem resolution_naturality
    {C₁ : Type*} [Category C₁] {C₃ : Type*} [Category C₃] {C₄ : Type*} [Category C₄]
    (F : C₁ ⥤ C₃) (K : C₁ ⥤ C₃) (G : C₃ ⥤ C₄)
    (H : C₁ ⥤ C₄) (a : H ≅ F ⋙ G) (b : F ≅ K)
    {X Y : C₁} (q : Y ⟶ X) [IsIso q]
    {Z : C₃} (ε : K.obj Y ⟶ Z) {V : C₄} (φ : G.obj Z ⟶ V) :
    a.hom.app X ≫ G.map (b.hom.app X) ≫
        G.map (inv (K.map q) ≫ ε) ≫ φ =
      inv (H.map q) ≫ a.hom.app Y ≫ G.map (b.hom.app Y) ≫ G.map ε ≫ φ := by
  let ψ : H ⟶ K ⋙ G := a.hom ≫ Functor.whiskerRight b.hom G
  have hn := ψ.naturality (inv q)
  change H.map (inv q) ≫ (a.hom.app Y ≫ G.map (b.hom.app Y)) =
    (a.hom.app X ≫ G.map (b.hom.app X)) ≫ G.map (K.map (inv q)) at hn
  simp only [Functor.map_inv] at hn
  simpa only [Functor.map_comp, Functor.map_inv, Category.assoc] using
    congrArg (fun z ↦ z ≫ G.map ε ≫ φ) hn.symm

attribute [local irreducible] completedScalarChangeData
  completedIntegralCoefficientSheafUnrestricted
private theorem point_derived_sections_tensor_data [IsAlgClosed k]
    (d : PointFiniteFreeSectionsTensorData k l E L ι) :
    Nonempty (PointDerivedSectionsTensorData d) := by
  classical
  have hE := point_sections_exact k _ _ d.coefficientE.toRingHom
  have hL := point_sections_exact k _ _ d.coefficientL.toRingHom
  have := hE.1
  have := hE.2
  have := hL.1
  have := hL.2
  have := d.sheaf_limits
  have := d.sheaf_colimits
  have := d.module_limits
  have := d.module_colimits
  have hAddE : (sectionsE d).Additive := ⟨by intros; rfl⟩
  have hAddL : (sectionsL d).Additive := ⟨by intros; rfl⟩
  have := hAddE
  have := hAddL
  let T := completedOrdinaryScalarExtension l E L ι (Spec (.of k))
  let LT := completedDerivedScalarExtension l E L ι (Spec (.of k))
  obtain ⟨c, hc'⟩ := scalar_exact_comparison (l := l) (E := E) (L := L) (ι := ι)
    (Spec (.of k))
  let τ : (A d).mapDerivedCategory ≅ (B d).mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
      ((A d).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((B d).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (A d).mapDerivedCategory (B d).mapDerivedCategory
      (Functor.isoWhiskerRight d.complexes DerivedCategory.Q)
  have hτ : ∀ C, τ.hom.app (DerivedCategory.Q.obj C) ≫
      (B d).mapDerivedCategoryFactors.hom.app C =
        (A d).mapDerivedCategoryFactors.hom.app C ≫
          DerivedCategory.Q.map (d.complexes.hom.app C) := by
    intro C
    dsimp only [τ]
    rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
    change (_ ≫ _ ≫ (B d).mapDerivedCategoryFactors.inv.app C) ≫ _ = _
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rfl
  let θ := (Functor.mapDerivedCategoryCompIso (sectionsE d)
      (pointFiniteFreeModuleTensor.{t, u} l E L ι)).symm ≪≫ τ ≪≫
    Functor.mapDerivedCategoryCompIso T (sectionsL d) ≪≫
    Functor.isoWhiskerRight c (sectionsL d).mapDerivedCategory
  refine ⟨{
    sectionsE_additive := hAddE
    sectionsL_additive := hAddL
    sectionsE_limits := hE.1
    sectionsE_colimits := hE.2
    sectionsL_limits := hL.1
    sectionsL_colimits := hL.2
    sheaf_limits := d.sheaf_limits
    sheaf_colimits := d.sheaf_colimits
    module_limits := d.module_limits
    module_colimits := d.module_colimits
    sheaf_quasiIso := ?_
    module_quasiIso := ?_
    sectionsE_quasiIso := ?_
    sectionsL_quasiIso := ?_
    comparison := c
    comparison_counit := hc'
    comparison_unique := ?_
    localized := τ
    localized_representative := hτ
    localized_unique := ?_
    theta := θ
    theta_eq := rfl
    resolution := ?_
    roof := ?_ }⟩
  · intro C C' f hf
    have := hf
    exact HomologicalComplex.quasiIso_map_of_preservesHomology f T
  · intro C C' f hf
    have := hf
    exact HomologicalComplex.quasiIso_map_of_preservesHomology f _
  · intro C C' f hf
    have := hf
    exact HomologicalComplex.quasiIso_map_of_preservesHomology f _
  · intro C C' f hf
    have := hf
    exact HomologicalComplex.quasiIso_map_of_preservesHomology f _
  · intro δ hδ
    apply Iso.ext_inv
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
    intro C
    exact (cancel_mono (T.mapDerivedCategoryFactors.hom.app C)).mp
      ((hδ C).trans (hc' C).symm)
  · intro σ hσ
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
    intro C
    exact (cancel_mono ((B d).mapDerivedCategoryFactors.hom.app C)).mp
      ((hσ C).trans (hτ C).symm)
  · intro C P q hq _ _
    have hcomp (P : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ) :
        (Functor.mapDerivedCategoryCompIso T (sectionsL d)).hom.app
            (DerivedCategory.Q.obj P) ≫
          (sectionsL d).mapDerivedCategory.map (T.mapDerivedCategoryFactors.hom.app P) ≫
          (sectionsL d).mapDerivedCategoryFactors.hom.app
            ((T.mapHomologicalComplex (.up ℤ)).obj P) =
          (B d).mapDerivedCategoryFactors.hom.app P := by
      exact Functor.mapDerivedCategoryCompIso_hom_app_factors T (sectionsL d) P
    have hnorm : c.hom.app (DerivedCategory.Q.obj P) ≫
        completedScalarCounit l E L ι (Spec (.of k)) P =
          T.mapDerivedCategoryFactors.hom.app P := by
      rw [← hc' P, Iso.hom_inv_id_app_assoc]
    have hn := resolution_naturality (T.mapDerivedCategory) LT (sectionsL d).mapDerivedCategory
      (A d).mapDerivedCategory (τ ≪≫ Functor.mapDerivedCategoryCompIso T (sectionsL d)) c
      (DerivedCategory.Q.map q)
      (completedScalarCounit l E L ι (Spec (.of k)) P)
      ((sectionsL d).mapDerivedCategoryFactors.hom.app
        ((completedOrdinaryScalarComplex l E L ι
          (Spec (.of k))).obj P))
    have hrep :
        (τ.hom.app (DerivedCategory.Q.obj P) ≫
            (Functor.mapDerivedCategoryCompIso T (sectionsL d)).hom.app
              (DerivedCategory.Q.obj P)) ≫
          (sectionsL d).mapDerivedCategory.map (c.hom.app (DerivedCategory.Q.obj P)) ≫
          (sectionsL d).mapDerivedCategory.map
            (completedScalarCounit l E L ι
              (Spec (.of k)) P) ≫
          (sectionsL d).mapDerivedCategoryFactors.hom.app
            ((T.mapHomologicalComplex (.up ℤ)).obj P) =
        (A d).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map (d.complexes.hom.app P) := by
      simp only [Category.assoc]
      rw [← Functor.map_comp_assoc, hnorm, hcomp P, hτ P]
    dsimp only [Iso.trans_hom, NatTrans.comp_app] at hn
    have hrep' := congrArg
      (fun z ↦ inv ((A d).mapDerivedCategory.map (DerivedCategory.Q.map q)) ≫ z) hrep
    simp only [Category.assoc] at hn hrep'
    have hn' := hn.trans hrep'
    simpa only [θ, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, NatTrans.comp_app, Category.assoc,
      Iso.hom_inv_id_app_assoc] using hn'
  · intro C H J q f hq
    have hn := τ.hom.naturality ((inv (DerivedCategory.Q.map q)) ≫ DerivedCategory.Q.map f)
    simpa only [Functor.map_comp, Functor.map_inv, Category.assoc] using hn.symm


/-- Exact point functors descend, with the counit-normalized derived tensor comparison.
Source: Stacks 06YY, 015F, 06XN and 04VG
(blueprint: lem-weil-point-derived-sections-tensor-descent).

Proof:
1. The algebraic closure in def-weil-finite-field-fiber is algebraically closed.
lem-weil-point-proetale-sections-exact makes evaluation exact. Transport the section-ring
action through d.coefficientE and d.coefficientL. The two tensor functors are exact by
lem-weil-point-finite-free-sections-tensor. Apply the exact-functor factorization
lem-weil-pbc-exact-functor-derived-factorization: all four termwise functors preserve
quasi-isomorphisms, and their derived functors have the displayed factorizations.
2. The left-derived counit of lem-pur-derived-change-of-rings is invertible on K-flat
complexes, by lem-pur-left-derived-from-kflat-class. Resolve C by a K-flat complex P
with flat terms using lem-pc-kflat-resolution. Counit naturality and exactness of
ordinary extension show epsilon_C is invertible, since epsilon_P and both images of
P to C are invertible.
3. Descend this counit and its inverse using lem-weil-pbc-localization-universal-property.
This gives comparison, with its inverse composed with the ordinary factorization equal
to the counit on every complex. Full faithfulness of precomposition fixes it uniquely.
4. Descend d.complexes by the same localization property to localized. Its representative
equation and uniqueness are the natural-transformation clauses of that property.
Compose with the exact-functor composition isomorphism and comparison to obtain theta.
5. For any resolution q, put rho_q = LT(Qq)^{-1} followed by epsilon_P. Counit naturality
gives epsilon_C = rho_q followed by Q(Tq). Naturality of d.complexes and the exact-functor
factorizations then give resolution. This equation identifies the same theta_C for every
resolution, proving independence without a cochain comparison between resolutions.
6. Chain naturality for q and f, followed by inversion of their localized q images,
gives roof. The localized transformation and comparison are natural transformations
on the whole derived category, so their composite is natural for every derived morphism.
No boundedness, constructibility or completeness condition was used. -/
theorem point_derived_sections_tensor_descent
    (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E L : IntermediateField ℚ_[l] Ω)
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L] (h : E ≤ L)
    [HasDerivedCategory.{wE} (ModuleCat.{max u (t + 1)}
      (Padic.coefficientExtensionIntegers l E))]
    [HasDerivedCategory.{wL} (ModuleCat.{max u (t + 1)}
      (Padic.coefficientExtensionIntegers l L))]
    (d : PointFiniteFreeSectionsTensorData D.k l E L (IntermediateField.inclusion h)) :
    Nonempty (PointDerivedSectionsTensorData d) := by
  -- Use the shorter universal-property route recorded in the updated DAG node.
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  exact point_derived_sections_tensor_data d

end WeilConjectures
