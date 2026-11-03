/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentHom
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentObjects
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFiniteModelProofAPISupplement
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexPresentation
public import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleExtContinuity
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
public import WeilConjectures.CategoryTheory.MapModScalarExtension

/-!
# The constructible finite-Tor algebraic-closure coefficient 2-colimit

This is the statement of the current blueprint unit `sk-prop-qlbar-two-colimit`.
It is stated for a finite or algebraically closed base field of characteristic
different from `ℓ`, with condensed coefficients pulled back to the pro-étale
site.  The objects are the finite-constant-model bounded constructible
finite-Tor complexes used for `D^b_{ctf}`.

Source: `literature/blueprint/latest/blueprint/part-six-operations/
sec-six-functors/sec-n-change/sk-prop-qlbar-two-colimit/_section.md`,
unit statement (order 383), and its
proof paragraph (blueprint: sk-prop-qlbar-two-colimit).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 0

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section FiniteTorCocone

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (k : Type u) [Field k] (hfield : Finite k ∨ IsAlgClosed k)
  (hchar : ringChar k ≠ ℓ)
  (X : Scheme.{u}) [hOver : X.Over (Spec (.of k))]
  [hft : LocallyOfFiniteType (X ↘ Spec (.of k))]
  [hqc : QuasiCompact (X ↘ Spec (.of k))]
  [hsep : IsSeparated (X ↘ Spec (.of k))]

include hfield hchar hOver hft hqc hsep in

private lemma scalarComp_eq (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    derivedExtendScalarsCompIso X ℓ h = finiteCoefficientDerivedTensorCompIso X ℓ h := rfl

private lemma model_iso
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (U.f i)).mapIso e).symm ≪≫ eP⟩⟩

private lemma stratified_model_iso
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ X N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a ↦ model_iso
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩

private noncomputable def point_scalar_extension_iso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ] (X : Scheme.{u}) :
    Mod.extendScalars φ ⋙ (upperStarFromPoint X).mapMod Λ' ≅
      (upperStarFromPoint X).mapMod Λ ⋙ Mod.extendScalars (coefficientMap φ X) := by
  let F := upperStarFromPoint X
  let : F.Braided :=
    { toMonoidal := inferInstance
      braided A B := Functor.LaxBraided.braided (F := upperStarFromPoint X) A B }
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  let := adj.rightAdjointLaxMonoidal
  let : adj.IsMonoidal := by
    constructor
    · rfl
    · intro X Y; rfl
  exact Functor.mapModExtendScalarsIso F _ adj φ

private theorem constant_model_scalar_extension
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ' X ((Mod.extendScalars (coefficientMap φ X)).obj M) := by
  have hlocal (T : Scheme.{u})
      (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
      (hN : HasFiniteConstantLocalModel Λ T N) :
      HasFiniteConstantLocalModel Λ' T
        ((Mod.extendScalars (coefficientMap φ T)).obj N) := by
    obtain ⟨C, hC⟩ := hN
    refine ⟨C, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := hC i
    refine ⟨(Mod.extendScalars φ).obj P, ?_, ⟨?_⟩⟩
    · exact map_finitePresentation _ _ (Mod.extendScalars φ)
        (Mod.regularExtensionIso φ) P hP
    · exact ((CondensedRing.pullIso φ (C.f i)).app N).symm ≪≫
        (Mod.extendScalars (coefficientMap φ (C.X i))).mapIso eP ≪≫
        ((point_scalar_extension_iso φ (C.X i)).app P).symm
  have hstrat (T : Scheme.{u})
      (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
      (hN : IsFiniteConstantStratified Λ T N) :
      IsFiniteConstantStratified Λ' T
        ((Mod.extendScalars (coefficientMap φ T)).obj N) := by
    obtain ⟨S, hS⟩ := hN
    refine ⟨S, fun a ↦ ?_⟩
    apply model_iso ((CondensedRing.pullIso φ (S.immersion a)).app N)
    exact hlocal _ _ (hS a)
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split at hM
  · rw [if_pos ‹_›]
    exact hstrat X M hM
  · rw [if_neg ‹_›]
    intro U hU
    exact stratified_model_iso ((CondensedRing.pullIso φ U.ι).app M)
      (hstrat _ _ (hM U hU))

private theorem scalarExtension_constantModel_bounded
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ] (X : Scheme.{u})
    [CategoryTheory.Limits.PreservesFiniteLimits (Mod.extendScalars (coefficientMap φ X))]
    (K : ConstantModelBoundedConstructible Λ X) :
    constantModelBoundedConstructible Λ' X
      ((Mod.extendScalars (coefficientMap φ X)).leftDerivedFunctor.obj K.obj) := by
  let G := Mod.extendScalars (coefficientMap φ X)
  let e := G.leftDerivedFunctorIsoMapDerivedCategory
  let P : ObjectProperty _ := IsConstantModelConstructible Λ' X
  have : P.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ' X).1
  refine ⟨?_, fun n ↦ ?_⟩
  · exact DerivedCategory.TStructure.t.bounded.prop_of_iso (e.app K.obj).symm
      (G.bounded_mapDerivedCategory_obj K.property.1)
  · exact P.prop_of_iso
      ((G.mapDerivedCategoryHomologyFunctorIso n).app K.obj ≪≫
        ((DerivedCategory.homologyFunctor _ n).mapIso (e.app K.obj)).symm)
      (constant_model_scalar_extension φ X
        ((DerivedCategory.homologyFunctor _ n).obj K.obj) (K.property.2 n))

private theorem finiteHomEvaluation_transition
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime]
    {E F H : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (a : F ≤ H)
    {K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))}
    (f : (derivedExtendScalarsSubfield X ℓ h).obj K ⟶
      (derivedExtendScalarsSubfield X ℓ h).obj L) :
    finiteDescentDerivedHomToAlgCl X ℓ (h.trans a)
      (finiteDescentDerivedHomTransition X ℓ h a f) =
        finiteDescentDerivedHomToAlgCl X ℓ h f := by
  let f₀ := f ≫ (shiftFunctorZero _ ℤ).inv.app _
  have ht := finiteDescentDerivedHomTransition_zero X ℓ h a K L f
  have he := finiteDescentDerivedHomToAlgCl_zero X ℓ (h.trans a) K L
    (coefficientDescentHomTransition X ℓ h a K L 0 f₀ ≫
      (shiftFunctorZero _ ℤ).hom.app _)
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at he
  rw [← ht, ← he, descentHomToAlgCl_transition]
  exact finiteDescentDerivedHomToAlgCl_zero X ℓ h K L f

private theorem finiteHomEvaluation_eventualEquality
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime]
    {E F G : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (a : E ≤ G)
    {K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))}
    (f : (derivedExtendScalarsSubfield X ℓ h).obj K ⟶
      (derivedExtendScalarsSubfield X ℓ h).obj L)
    (g : (derivedExtendScalarsSubfield X ℓ a).obj K ⟶
      (derivedExtendScalarsSubfield X ℓ a).obj L)
    (he : finiteDescentDerivedHomToAlgCl X ℓ h f =
      finiteDescentDerivedHomToAlgCl X ℓ a g) :
    ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (b : F ≤ H) (c : G ≤ H),
      finiteDescentDerivedHomTransition X ℓ h b f =
        finiteDescentDerivedHomTransition X ℓ a c g := by
  let H := CategoryTheory.IsFiltered.max F G
  have b : F ≤ H := leOfHom (CategoryTheory.IsFiltered.leftToMax F G)
  have c : G ≤ H := leOfHom (CategoryTheory.IsFiltered.rightToMax F G)
  refine ⟨H, b, c, ?_⟩
  have : (derivedExtendScalarsToPadicAlgCl X ℓ H).Faithful :=
    faithful_leftDerivedExtendScalarsToPadicAlgCl X ℓ H
  have hh : Function.Injective (finiteDescentDerivedHomToAlgCl X ℓ (h.trans b)
      (C := K) (D := L)) := by
    intro s t heq
    apply (derivedExtendScalarsToPadicAlgCl X ℓ H).map_injective
    exact (cancel_mono ((derivedExtendScalarsCompIso X ℓ (h.trans b)).hom.app L)).mp
      ((cancel_epi ((derivedExtendScalarsCompIso X ℓ (h.trans b)).inv.app K)).mp heq)
  apply hh
  rw [finiteHomEvaluation_transition, finiteHomEvaluation_transition]
  exact he

private theorem constantModel_finiteHomSurj
    (X : Scheme.{u}) [IsNoetherian X] (ℓ : ℕ) [Fact ℓ.Prime]
    (E F : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X)
    (L : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj F) X)
    (ψ : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj K.obj ⟶
      (derivedExtendScalarsToPadicAlgCl X ℓ F).obj L.obj) :
    ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (b : E ≤ H) (c : F ≤ H)
      (f : (derivedExtendScalarsSubfield X ℓ b).obj K.obj ⟶
        (derivedExtendScalarsSubfield X ℓ c).obj L.obj),
      ψ = (derivedExtendScalarsCompIso X ℓ b).inv.app K.obj ≫
        (derivedExtendScalarsToPadicAlgCl X ℓ H).map f ≫
          (derivedExtendScalarsCompIso X ℓ c).hom.app L.obj := by
  let G := CategoryTheory.IsFiltered.max E F
  let I := AsSmall.{u + 1} (CategoryTheory.Under G)
  let H : I ⥤ PadicAlgCl.FiniteIntermediateField ℓ :=
    (AsSmall.equiv (C := CategoryTheory.Under G)).inverse ⋙ CategoryTheory.Under.forget G
  let : H.Final := Functor.final_equivalence_comp
    (AsSmall.equiv (C := CategoryTheory.Under G)).inverse (CategoryTheory.Under.forget G)
  have he (i : I) : E ≤ H.obj i :=
    le_trans (leOfHom (CategoryTheory.IsFiltered.leftToMax E F)) (leOfHom (ULift.down i).hom)
  have hf (i : I) : F ≤ H.obj i :=
    le_trans (leOfHom (CategoryTheory.IsFiltered.rightToMax E F)) (leOfHom (ULift.down i).hom)
  obtain ⟨N, c, ⟨hc⟩, ⟨b, hN⟩, eΩ, ei, hcomp⟩ :=
    exists_condensed_coefficient_complex_presentation X ℓ E F L.obj L.property.1.1 H he hf
  let : CategoryTheory.Limits.HasColimit N := ⟨⟨c, hc⟩⟩
  let R := Profinite.padicSubfieldCondensedRing.{u} ℓ E
  have hK := bounded_constructible_ext_generated ℓ E R (Or.inl rfl) X K.obj K.property
  have hcont (n : ℤ) : IsIso (extContinuityComparison K.obj N
      (CategoryTheory.Limits.colimit.cocone N) n) :=
    constructible_ext_continuity ℓ E R (Or.inl rfl) X K.obj hK N b hN
      (CategoryTheory.Limits.colimit.cocone N) (CategoryTheory.Limits.colimit.isColimit N) n
  have hfactor : ∀ f : K.obj ⟶ DerivedCategory.Q.obj c.pt,
      ∃ (i : I) (g : K.obj ⟶ DerivedCategory.Q.obj (N.obj i)),
        f = g ≫ DerivedCategory.Q.map (c.ι.app i) :=
    CategoryTheory.factors_of_colimit_cocone N DerivedCategory.Q c hc K.obj
      (CategoryTheory.factors_iso _ ((shiftFunctorZero _ ℤ).app K.obj)
        (CategoryTheory.shiftFactors_of_hom_colimit N DerivedCategory.Q K.obj hcont 0))
  let adj := finiteCoefficientDerivedAlgClHomEquiv X ℓ E K.obj
    ((finiteCoefficientDerivedToAlgCl X ℓ F).obj L.obj)
  obtain ⟨i, g, hg⟩ := hfactor (adj ψ ≫ eΩ.inv)
  let f := (finiteCoefficientDerivedHomEquiv X ℓ (he i) K.obj _).symm
    (g ≫ (ei i).hom)
  refine ⟨H.obj i, he i, hf i, f, ?_⟩
  apply adj.injective
  have hh : adj ψ = (g ≫ DerivedCategory.Q.map (c.ι.app i)) ≫ eΩ.hom :=
    eΩ.comp_inv_eq.mp hg
  rw [scalarComp_eq, scalarComp_eq]
  exact hh.trans ((Category.assoc _ _ _).trans (hcomp i K.obj g).symm)

/-- Scalar extension preserves the finite-constant-model bounded constructible
finite-Tor subcategories, both between finite fields and into the algebraic closure.

Source: `part-six-operations/sec-six-functors/sec-n-change/`
`sk-prop-qlbar-two-colimit/sk-prop-qlbar-two-colimit.proof.md`, scalar extension;
DAG proof step 2 (blueprint: sk-prop-qlbar-two-colimit).

Proof: The field scalar extensions are flat, so their derived functors are computed
termwise and commute with cohomology. On the pro-étale cover of each constructible
stratum, a finite constant model over a field is finite free. Tensoring preserves
that model, its rank, the finite stratification and the cohomological bounds.
Step 1's rational finite-Tor identification then supplies finite Tor amplitude
for the resulting bounded constructible field-coefficient complexes.
-/
theorem constantModelFiniteTor_scalarExtension_preserves :
    (∀ {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
      (K : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X),
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj F) X ⊓
        DerivedCategory.finiteTorAmplitude _)
          ((derivedExtendScalarsSubfield X ℓ h).obj K.obj)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X),
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ⊓
        DerivedCategory.finiteTorAmplitude _)
          ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K.obj)) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have htE (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
    (integral_ctf_equals_bc ℓ X
      (Mon.mk (Profinite.continuousMapRingObj E))
      (Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩)))).2.2.2
  have htΩ := (integral_ctf_equals_bc ℓ X
    (Mon.mk (Profinite.padicAlgClRingObj ℓ)) (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).2.2.2
  constructor
  · intro E F h K
    rw [htE F]
    exact scalarExtension_constantModel_bounded (Profinite.padicSubfieldRingObjMap ℓ h) X
      ⟨K.obj, K.property.1⟩
  · intro E K
    rw [htΩ]
    exact scalarExtension_constantModel_bounded (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      X ⟨K.obj, K.property.1⟩

/-- Scalar extension on the actual finite-Tor constant-model subcategories.
Source: the scalar-extension clause and DAG step 2 of the current unit
(blueprint: sk-prop-qlbar-two-colimit). -/
def constantModelFiniteTorExtendScalars
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X ⥤
      ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj F) X :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ⊓
      DerivedCategory.finiteTorAmplitude _).ι ⋙ derivedExtendScalarsSubfield X ℓ h)
    ((constantModelFiniteTor_scalarExtension_preserves ℓ k hfield hchar X).1 h)

/-- Extension to the algebraic closure on finite-Tor constant-model complexes.
Source: the object map in the current unit and DAG step 2
(blueprint: sk-prop-qlbar-two-colimit). -/
def constantModelFiniteTorToPadicAlgCl (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X ⥤
      ConstantModelConstructibleFiniteTor (Profinite.padicAlgClRingObj ℓ) X :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ⊓
      DerivedCategory.finiteTorAmplitude _).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E)
    ((constantModelFiniteTor_scalarExtension_preserves ℓ k hfield hchar X).2 E)

/-- Restriction of the canonical ambient scalar transitivity isomorphism, using
full faithfulness of the inclusion of the finite-Tor constant-model subcategory.
Source: the category-of-pairs construction, DAG step 5
(blueprint: sk-prop-qlbar-two-colimit). -/
def constantModelFiniteTorToPadicAlgClCompIso
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    constantModelFiniteTorExtendScalars ℓ k hfield hchar X h ⋙
        constantModelFiniteTorToPadicAlgCl ℓ k hfield hchar X F ≅
      constantModelFiniteTorToPadicAlgCl ℓ k hfield hchar X E :=
  Functor.fullyFaithfulCancelRight
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ⊓
      DerivedCategory.finiteTorAmplitude _).ι
    ((Iso.refl ((constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ⊓
        DerivedCategory.finiteTorAmplitude _).ι ⋙
        (derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F)) :
      (constantModelFiniteTorExtendScalars ℓ k hfield hchar X h ⋙
          constantModelFiniteTorToPadicAlgCl ℓ k hfield hchar X F) ⋙
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ⊓
          DerivedCategory.finiteTorAmplitude _).ι ≅
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ⊓
        DerivedCategory.finiteTorAmplitude _).ι ⋙
        (derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F)) ≪≫
      Functor.isoWhiskerLeft
        (constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ⊓
          DerivedCategory.finiteTorAmplitude _).ι
        (derivedExtendScalarsCompIso X ℓ h))

/-- The scalar-extension cocone with finite-Tor constant-model categories at every
finite field and at its vertex, constructed directly from their ambient inclusions.
Source: the unit's category of pairs and DAG steps 5--6
(blueprint: sk-prop-qlbar-two-colimit). -/
def constantModelFiniteTorCocone :
    CategoryCocone
      (fun E : PadicAlgCl.FiniteIntermediateField ℓ ↦
        ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X)
      (ConstantModelConstructibleFiniteTor (Profinite.padicAlgClRingObj ℓ) X) where
  T h := constantModelFiniteTorExtendScalars ℓ k hfield hchar X h
  Φ E := constantModelFiniteTorToPadicAlgCl ℓ k hfield hchar X E
  iso h := constantModelFiniteTorToPadicAlgClCompIso ℓ k hfield hchar X h

private lemma finiteTorToAlgCl_map_hom (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {K L : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X}
    (f : K ⟶ L) :
    ((constantModelFiniteTorToPadicAlgCl ℓ k hfield hchar X E).map f).hom =
      (derivedExtendScalarsToPadicAlgCl X ℓ E).map f.hom := rfl

private lemma finiteTorCompIso_hom
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X) :
    ((constantModelFiniteTorToPadicAlgClCompIso ℓ k hfield hchar X h).hom.app K).hom =
      (derivedExtendScalarsCompIso X ℓ h).hom.app K.obj := by
  change (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ⊓
    DerivedCategory.finiteTorAmplitude _).ι.map _ = _
  unfold constantModelFiniteTorToPadicAlgClCompIso
  rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  exact Category.id_comp _

private lemma finiteTorCompIso_inv
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X) :
    ((constantModelFiniteTorToPadicAlgClCompIso ℓ k hfield hchar X h).inv.app K).hom =
      (derivedExtendScalarsCompIso X ℓ h).inv.app K.obj := by
  change (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ⊓
    DerivedCategory.finiteTorAmplitude _).ι.map _ = _
  unfold constantModelFiniteTorToPadicAlgClCompIso
  rw [Functor.fullyFaithfulCancelRight_inv_app, Functor.map_preimage]
  simp only [Iso.trans_inv, NatTrans.comp_app, Iso.refl_inv, NatTrans.id_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app]
  exact Category.comp_id _

end FiniteTorCocone

/-- The ordinary filtered 2-colimit of the finite-Tor constant-model categories.
Source: `part-six-operations/sec-six-functors/sec-n-change/`
`sk-prop-qlbar-two-colimit/_section.md`, order 383, and its proof
(blueprint: sk-prop-qlbar-two-colimit).

Proof follows DAG steps 1--6:
1. A separated finite-type scheme over a field is qcqs. For finite field coefficients
   and the algebraic closure, rational bounded constructibility equals finite-Tor
   bounded constructibility inside the same ordinary derived category.
2. Flat scalar extension preserves the finite constant models, the constructible
   stratification and the cohomological bounds; step 1 gives finite Tor amplitude.
   This is the named preservation theorem used to construct the cocone above.
3. Descend an object by the finite-coefficient descent theorem: descend its lisse
   sheaves and transition matrices and then the connecting maps of a finite
   Postnikov tower. Step 1 puts the finite-stage representative in Dctf.
4. Apply the morphism clause at degree zero. Fullness identifies the Hom sets with
   ambient derived Hom sets, and constructible Ext continuity gives surjectivity
   and eventual equality for their finite-stage representatives.
5. For different initial fields move to their finite compositum. The ambient
   scalar transitivity isomorphisms restrict by the fully faithful inclusions.
   Transport identities and composition through the Hom bijections; injectivity
   gives independence of representatives, associativity and the unit laws.
6. Object descent and the cross-stage Hom bijections give essential surjectivity
   and full faithfulness of the comparison from pairs. Equivalently they give
   Obj, Hom-surj and Hom-inj of the actual Dctf cocone, so it is a filtered
   2-colimit of ordinary categories.
-/
theorem qlbarTwoColimitGeneral
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hfield : Finite k ∨ IsAlgClosed k)
    (hchar : ringChar k ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ K : ConstantModelConstructibleFiniteTor
        (Profinite.padicAlgClRingObj ℓ) X,
      ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
        (K_E : ConstantModelConstructibleFiniteTor
          (Profinite.continuousMapRingObj E) X),
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K L : ConstantModelConstructibleFiniteTor
        (Profinite.continuousMapRingObj E) X),
      (∀ ψ : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj K.obj ⟶
          (derivedExtendScalarsToPadicAlgCl X ℓ E).obj L.obj,
        ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
          (f : (derivedExtendScalarsSubfield X ℓ h).obj K.obj ⟶
            (derivedExtendScalarsSubfield X ℓ h).obj L.obj),
          finiteDescentDerivedHomToAlgCl X ℓ h f = ψ) ∧
      (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (a : E ≤ G)
        (f : (derivedExtendScalarsSubfield X ℓ h).obj K.obj ⟶
          (derivedExtendScalarsSubfield X ℓ h).obj L.obj)
        (g : (derivedExtendScalarsSubfield X ℓ a).obj K.obj ⟶
          (derivedExtendScalarsSubfield X ℓ a).obj L.obj),
        finiteDescentDerivedHomToAlgCl X ℓ h f =
            finiteDescentDerivedHomToAlgCl X ℓ a g →
        ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (b : F ≤ H) (c : G ≤ H),
          finiteDescentDerivedHomTransition X ℓ h b f =
            finiteDescentDerivedHomTransition X ℓ a c g)) ∧
    (constantModelFiniteTorCocone ℓ k hfield hchar X).IsFilteredTwoColimit := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsNoetherian X := {}
  have htE (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
    (integral_ctf_equals_bc ℓ X
      (Mon.mk (Profinite.continuousMapRingObj E))
      (Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩)))).2.2.2
  have hobj : ∀ K : ConstantModelConstructibleFiniteTor
      (Profinite.padicAlgClRingObj ℓ) X,
      ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
        (K_E : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X),
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj) := by
    intro K
    obtain ⟨E, K_E, he⟩ := (coefficient_finite_descent_objects_of_isNoetherian ℓ X).1
      ⟨K.obj, K.property.1⟩
    refine ⟨E, ⟨K_E.obj, ?_⟩, he⟩
    rw [htE E]
    exact K_E.property
  have hhom : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K L : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X),
      (∀ ψ : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj K.obj ⟶
          (derivedExtendScalarsToPadicAlgCl X ℓ E).obj L.obj,
        ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
          (f : (derivedExtendScalarsSubfield X ℓ h).obj K.obj ⟶
            (derivedExtendScalarsSubfield X ℓ h).obj L.obj),
          finiteDescentDerivedHomToAlgCl X ℓ h f = ψ) ∧
      (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (a : E ≤ G)
        (f : (derivedExtendScalarsSubfield X ℓ h).obj K.obj ⟶
          (derivedExtendScalarsSubfield X ℓ h).obj L.obj)
        (g : (derivedExtendScalarsSubfield X ℓ a).obj K.obj ⟶
          (derivedExtendScalarsSubfield X ℓ a).obj L.obj),
        finiteDescentDerivedHomToAlgCl X ℓ h f =
            finiteDescentDerivedHomToAlgCl X ℓ a g →
        ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (b : F ≤ H) (c : G ≤ H),
          finiteDescentDerivedHomTransition X ℓ h b f =
            finiteDescentDerivedHomTransition X ℓ a c g) := by
    intro E K L
    constructor
    · intro ψ
      obtain ⟨F, h, a, f, hf⟩ := constantModel_finiteHomSurj X ℓ E E
        ⟨K.obj, K.property.1⟩ ⟨L.obj, L.property.1⟩ ψ
      refine ⟨F, h, f, ?_⟩
      simpa only [finiteDescentDerivedHomToAlgCl] using hf.symm
    · intro F G h a f g he
      exact finiteHomEvaluation_eventualEquality X ℓ h a f g he
  refine ⟨hobj, hhom, ?_⟩
  constructor
  · intro K
    obtain ⟨E, K_E, ⟨e⟩⟩ := hobj K
    refine ⟨E, K_E, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _ e
  · intro E F K L ψ
    obtain ⟨H, b, c, f, hf⟩ := constantModel_finiteHomSurj X ℓ E F
      ⟨K.obj, K.property.1⟩ ⟨L.obj, L.property.1⟩ ψ.hom
    refine ⟨H, b, c, ObjectProperty.homMk f, ?_⟩
    apply (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ⊓
      DerivedCategory.finiteTorAmplitude _).ι.map_injective
    simpa only [constantModelFiniteTorCocone, ObjectProperty.ι_map,
      ObjectProperty.FullSubcategory.comp_hom, finiteTorCompIso_inv, finiteTorCompIso_hom,
      finiteTorToAlgCl_map_hom, ObjectProperty.homMk]
      using hf
  · intro E K L f g he
    have : (derivedExtendScalarsToPadicAlgCl X ℓ E).Faithful :=
      faithful_leftDerivedExtendScalarsToPadicAlgCl X ℓ E
    have hfg : f = g := by
      apply (constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ⊓
        DerivedCategory.finiteTorAmplitude _).ι.map_injective
      apply (derivedExtendScalarsToPadicAlgCl X ℓ E).map_injective
      exact congrArg (·.hom) he
    exact ⟨E, le_rfl, congrArg
      ((constantModelFiniteTorCocone ℓ k hfield hchar X).T le_rfl).map hfg⟩

end AlgebraicGeometry.ProEtale
