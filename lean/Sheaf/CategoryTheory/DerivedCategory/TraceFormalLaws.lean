/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q12, Q5
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
public import Sheaf.Paper.PointFdQbarCategory
public import Sheaf.Algebra.Homology.TwoStepFilteredTotal
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.Algebra.Homology.FilteredProjectiveModel
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.TraceLaws
import WeilConjectures.CategoryTheory.DerivedCategory.TraceScalarExtension
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Algebra.Homology.FieldComplexCohomologySplitting
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Formal laws for the categorical trace

Source: Weil blueprint, main-20261015, `sk-p-trace/prop-trf-trace-formal-laws`,
clauses (1)--(4); Stacks Project, Tags 03TB, 03TJ and 087J
(blueprint: prop-trf-trace-formal-laws).

The first three laws use exactly `A = O_E / ϖ_E^n`, with `n ≥ 1`, from the fixed
finite-field datum and coefficient conventions. The target of scalar extension uses
the same signed dual-frame construction over an arbitrary commutative ring. Perfectness means
a bounded finite-projective
model, never merely bounded finite cohomology. The filtered law is stated on the
filtered derived object itself: its total and graded endomorphisms induce the triangle
in clause (2). In particular every filtration-preserving chain endomorphism is covered.
It asserts no additivity for arbitrary endomorphisms of Verdier triangles. The explicit
`Z/4` counterexample and its middle trace `-2 ≠ 0` are the warning in that clause.

Scalar extension is quantified over a universal left derived functor together with its
counit and universal property. This specifies exactly derived extension of scalars and
allows a nonflat target. The field law applies both to finite coefficient fields and to
the actual ordinary-module category over the algebraic closure. The last statement
separately treats the common-stage category: it characterizes its scalar trace uniquely
by all common-stage presentations, without identifying it with the entire D(Qbar).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex

namespace DerivedCategory

/-- Additivity of the recorded ordinary scalar-extension functor, needed to form its
homotopy functor in clause (3). Source: the termwise tensor construction in the blueprint
(blueprint: prop-trf-trace-formal-laws). -/
noncomputable instance traceExtendScalarsAdditive {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) : (ModuleCat.extendScalars.{u, u, u} ρ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj ρ).left_adjoint_additive

/-- Conjugacy invariance, clause (1), for the signed perfect-complex trace.
Source: blueprint trace formal laws, clause (1)
(blueprint: prop-trf-trace-formal-laws).
Proof: install the canonical braiding and the canonical right duals of both perfect
objects. The proved monoidal trace-conjugacy theorem cancels the transported duality
isomorphisms using the intertwining equation. Apply `perfectTraceScalar` to the
resulting equality of endomorphisms of the tensor unit. -/
theorem perfectCategoricalTrace_conjugacy
    (D : WeilConjectures.FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : IntermediateField (Padic c.l) c.Qbar) [FiniteDimensional (Padic c.l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (P₁ P₂ : DerivedCategory.{u}
      (ModuleCat.{u} (Padic.coefficientExtensionRing c.l E n)))
    (h₁ : IsPerfectRingComplex.{u, u} P₁) (h₂ : IsPerfectRingComplex.{u, u} P₂)
    (v₁ : P₁ ⟶ P₁) (v₂ : P₂ ⟶ P₂) (w : P₁ ≅ P₂)
    (hw : w.hom ≫ v₂ = v₁ ≫ w.hom) :
    WeilConjectures.finiteCoefficientCategoricalTrace D c E n hn P₁ h₁ v₁ =
      WeilConjectures.finiteCoefficientCategoricalTrace D c E n hn P₂ h₂ v₂ := by
  let := perfectTraceCanonicalBraiding
    (ModuleCat.{u} (Padic.coefficientExtensionRing c.l E n))
  let := perfectTraceHasRightDual P₁ h₁
  let := perfectTraceHasRightDual P₂ h₂
  unfold WeilConjectures.finiteCoefficientCategoricalTrace perfectCategoricalTrace
  exact congrArg perfectTraceScalar (MonoidalCategory.trace_eq_of_iso w v₁ v₂ hw.symm)

private theorem traceScalar_algebraMap {R : Type u} [CommRing R] (r : R) :
    perfectTraceScalar (algebraMap R
      (End (MonoidalCategoryStruct.tensorUnit (DerivedCategory (ModuleCat.{u} R)))) r) = r := by
  unfold perfectTraceScalar
  have hpre : (singleFunctor (ModuleCat.{u} R) 0).preimage
      ((singleFunctorObjUnitIso (ModuleCat.{u} R)).hom ≫
        algebraMap R
          (End (MonoidalCategoryStruct.tensorUnit (DerivedCategory (ModuleCat.{u} R)))) r ≫
        (singleFunctorObjUnitIso (ModuleCat.{u} R)).inv) =
      algebraMap R (End (MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} R))) r := by
    apply (singleFunctor (ModuleCat.{u} R) 0).map_injective
    rw [Functor.map_preimage]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      End.one_def, End.one_def]
    rw [Linear.smul_comp, Linear.comp_smul]
    simp only [Category.id_comp, Iso.hom_inv_id]
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  rw [hpre, Algebra.algebraMap_eq_smul_one, End.one_def]
  change (r • (LinearMap.id : R →ₗ[R] R)) 1 = r
  simp

private theorem traceScalar_add {R : Type u} [CommRing R]
    (f g : End
      (MonoidalCategoryStruct.tensorUnit (DerivedCategory (ModuleCat.{u} R)))) :
    perfectTraceScalar (f + g) = perfectTraceScalar f + perfectTraceScalar g := by
  let F := singleFunctor (ModuleCat.{u} R) 0
  have hadd {X Y : ModuleCat.{u} R} (x y : F.obj X ⟶ F.obj Y) :
      F.preimage (x + y) = F.preimage x + F.preimage y := by
    apply F.map_injective
    simp only [Functor.map_preimage, Functor.map_add]
  unfold perfectTraceScalar
  rw [Preadditive.add_comp, Preadditive.comp_add, hadd]
  rfl

private theorem coefficient_projective_free
    (D : WeilConjectures.FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : IntermediateField (Padic c.l) c.Qbar) [FiniteDimensional (Padic c.l) E]
    (n : ℕ) (M : ModuleCat.{u} (Padic.coefficientExtensionRing c.l E n))
    [Module.Finite (Padic.coefficientExtensionRing c.l E n) M]
    [Module.Projective (Padic.coefficientExtensionRing c.l E n) M] :
    Module.Free (Padic.coefficientExtensionRing c.l E n) M := by
  rcases subsingleton_or_nontrivial (Padic.coefficientExtensionRing c.l E n) with h | h
  · have := h
    exact Module.Free.of_subsingleton' _ _
  · have := h
    have hO := (Padic.extension_integers_dvr c.l E
      (Padic.coefficientExtensionAbsoluteValue c.l E)
      (spectralNorm_extends (K := Padic c.l) (L := E))).choose_spec.choose_spec
    have : IsLocalRing (Padic.coefficientExtensionIntegers c.l E) := hO.2.2.2.1
    have : IsLocalRing (Padic.coefficientExtensionRing c.l E n) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    exact Module.free_of_flat_of_isLocalRing

private theorem trace_free_model {R : Type u} [CommRing R]
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [M.IsStrictlyGE a] [M.IsStrictlyLE b]
    (hfree : ∀ i, Module.Free R (M.X i))
    (hfin : ∀ i, Module.Finite R (M.X i))
    (P : DerivedCategory (ModuleCat.{u} R)) (hP : IsPerfectRingComplex P)
    (v : P ⟶ P) (w : M ⟶ M) (e : P ≅ Q.obj M)
    (hw : v ≫ e.hom = e.hom ≫ Q.map w) :
    perfectCategoricalTrace P hP v =
      ∑ i ∈ Finset.Icc a b, i.negOnePow • LinearMap.trace R (M.X i) (w.f i).hom := by
  let := perfectTraceCanonicalBraiding (ModuleCat.{u} R)
  let := perfectTraceHasRightDual P hP
  have hs (i : ℤ) (hi : i ∉ Finset.Icc a b) : IsZero (M.X i) := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · exact M.isZero_of_isStrictlyGE a i hi
    · exact M.isZero_of_isStrictlyLE b i hi
  unfold perfectCategoricalTrace
  rw [trace_eq_algebraMap_sum_negOnePow_linearMapTrace M w _ hs hfree hfin P v e hw]
  exact traceScalar_algebraMap _

private theorem perfect_chain_representative {R : Type u} [CommRing R]
    (P : DerivedCategory (ModuleCat.{u} R)) (hP : IsPerfectRingComplex P) (v : P ⟶ P) :
    ∃ (M : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ),
      M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
      (∀ i, Module.Projective R (M.X i) ∧ Module.Finite R (M.X i)) ∧
      ∃ (e : P ≅ Q.obj M) (w : M ⟶ M), v ≫ e.hom = e.hom ≫ Q.map w := by
  obtain ⟨M, a, b, ha, hb, hM, ⟨e⟩⟩ := hP
  have := hb
  have (i : ℤ) : Projective (M.X i) := by
    have := (hM i).1
    exact ModuleCat.projective_of_categoryTheory_projective _
  have : M.IsKProjective := isKProjective_of_projective M b
  obtain ⟨w, hw⟩ := IsKProjective.exists_Q_map_eq M M (e.inv ≫ v ≫ e.hom)
  refine ⟨M, a, b, ha, hb, hM, e, w, ?_⟩
  simp [hw]

private theorem intertwine_iso_inv {C : Type*} [Category C] {X Y : C}
    (e : X ≅ Y) (x : X ⟶ X) (y : Y ⟶ Y) (h : x ≫ e.hom = e.hom ≫ y) :
    y ≫ e.inv = e.inv ≫ x := by
  apply (cancel_epi e.hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using
    congrArg (fun f ↦ f ≫ e.inv) h.symm

private theorem field_trace {F : Type u} [Field F]
    (P : DerivedCategory (ModuleCat.{u} F)) (hP : pointFiniteDimensional F P)
    (v : P ⟶ P) :
    ∃ h : IsPerfectRingComplex P,
      perfectCategoricalTrace P h v = ∑ᶠ i : ℤ, i.negOnePow •
        LinearMap.trace F ((homologyFunctor (ModuleCat.{u} F) i).obj P)
          (((homologyFunctor (ModuleCat.{u} F) i).map v).hom) := by
  classical
  have hp := ((field_complex_cohomology_splitting F).2.2.2.1 P hP).2
  obtain ⟨M, a, b, ha, hb, hM, e, w, hw⟩ := perfect_chain_representative P hp v
  have := ha
  have := hb
  have hfree (i : ℤ) : Module.Free F (M.X i) := inferInstance
  have hfin (i : ℤ) : Module.Finite F (M.X i) := (hM i).2
  have hs (i : ℤ) (hi : i ∉ Finset.Icc a b) : IsZero (M.X i) := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · exact M.isZero_of_isStrictlyGE a i hi
    · exact M.isZero_of_isStrictlyLE b i hi
  refine ⟨hp, ?_⟩
  rw [trace_free_model M a b hfree hfin P hp v w e hw]
  have hhopf :=
    CochainComplex.sum_negOnePow_smul_trace_f_eq_sum_negOnePow_smul_trace_homologyMap
      M w (Finset.Icc a b) hs hfin
  change (∑ i ∈ Finset.Icc a b, i.negOnePow •
      LinearMap.trace F (M.X i) (w.f i).hom) =
    ∑ i ∈ Finset.Icc a b, i.negOnePow •
      LinearMap.trace F (M.homology i) (HomologicalComplex.homologyMap w i).hom at hhopf
  rw [hhopf]
  let eH (i : ℤ) : (homologyFunctor (ModuleCat.{u} F) i).obj P ≅ M.homology i :=
    (homologyFunctor _ i).mapIso e ≪≫ (homologyFunctorFactors _ i).app M
  have hc (i : ℤ) : (homologyFunctor (ModuleCat.{u} F) i).map v ≫ (eH i).hom =
      (eH i).hom ≫ HomologicalComplex.homologyMap w i := by
    have hn := (homologyFunctorFactors (ModuleCat.{u} F) i).hom.naturality w
    change (homologyFunctor (ModuleCat.{u} F) i).map (Q.map w) ≫
      ((homologyFunctorFactors _ i).app M).hom =
      ((homologyFunctorFactors _ i).app M).hom ≫ HomologicalComplex.homologyMap w i at hn
    change (homologyFunctor (ModuleCat.{u} F) i).map v ≫
      (homologyFunctor (ModuleCat.{u} F) i).map e.hom ≫ _ = _
    rw [← Functor.map_comp_assoc, hw, Functor.map_comp, Category.assoc, hn]
    simp only [eH, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  have htr (i : ℤ) : LinearMap.trace F (M.homology i)
        (HomologicalComplex.homologyMap w i).hom =
      LinearMap.trace F ((homologyFunctor (ModuleCat.{u} F) i).obj P)
        (((homologyFunctor (ModuleCat.{u} F) i).map v).hom) := by
    have hg : HomologicalComplex.homologyMap w i = (eH i).inv ≫
        (homologyFunctor (ModuleCat.{u} F) i).map v ≫ (eH i).hom := by
      apply (cancel_epi (eH i).hom).1
      simpa using (hc i).symm
    rw [hg]
    exact LinearMap.trace_conj' _ (eH i).toLinearEquiv
  simp_rw [htr]
  symm
  apply finsum_eq_sum_of_support_subset _
  intro i hi
  by_contra hi'
  have hz : IsZero ((homologyFunctor (ModuleCat.{u} F) i).obj P) :=
    ((M.exactAt_iff_isZero_homology i).mp
        ((M.sc i).exact_of_isZero_X₂ (hs i hi'))).of_iso (eH i)
  have : Subsingleton ((homologyFunctor (ModuleCat.{u} F) i).obj P) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  exact hi (by simp only [LinearMap.trace_eq_zero_of_subsingleton, smul_zero])

set_option backward.isDefEq.respectTransparency false in
private theorem filtered_trace_of_free {A : Type u} [CommRing A]
    (hfree : ∀ (M : ModuleCat.{u} A) [Module.Finite A M] [Module.Projective A M],
      Module.Free A M)
    (P : TwoStepModuleDerived A) (v : P ⟶ P)
    (h : IsPerfectRingComplex ((twoStepTotal A).obj P))
    (h' : IsPerfectRingComplex ((twoStepGraded A true).obj P))
    (h'' : IsPerfectRingComplex ((twoStepGraded A false).obj P)) :
    perfectCategoricalTrace _ h ((twoStepTotal A).map v) =
      perfectCategoricalTrace _ h' ((twoStepGraded A true).map v) +
      perfectCategoricalTrace _ h'' ((twoStepGraded A false).map v) := by
  classical
  obtain ⟨M, ⟨a, b, ha, hb, hgr⟩, hMF, hS, _, j, w, hw, hgraded⟩ :=
    exists_filteredProjectiveModel P (fun z ↦ by
      cases z
      · exact h''
      · exact h') v
  have := ha
  have := hb
  have hfreeGr (z : Bool) (i : ℤ) :
      Module.Free A (((twoStepGradedComplex A z).obj M).X i) := by
    have := ((hMF i).2 z).1
    have := ((hMF i).2 z).2
    exact hfree _
  let S := ShortComplex.mk M.obj.hom (cokernel.π M.obj.hom)
    (cokernel.condition M.obj.hom)
  let φ : S ⟶ S :=
    { τ₁ := w.hom.left
      τ₂ := w.hom.right
      τ₃ := (coker _).map w.hom
      comm₁₂ := w.hom.w
      comm₂₃ := (coker.π (C := CochainComplex (ModuleCat A) ℤ)).naturality w.hom }
  have hs (i : ℤ) (hi : i ∉ Finset.Icc a b) : IsZero (M.obj.right.X i) := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · exact M.obj.right.isZero_of_isStrictlyGE a i hi
    · exact M.obj.right.isZero_of_isStrictlyLE b i hi
  have hcomp : twoStepModuleQ A ⋙ twoStepTotal A = twoStepTotalComplex A := by
    change twoStepModuleHomotopyQuotient A ⋙
      (twoStepModuleQh A ⋙ twoStepTotal A) = _
    rw [show twoStepModuleQh A ⋙ twoStepTotal A = twoStepTotalHomotopy A from
      Localization.Construction.fac _ _]
    rfl
  have hmap := Functor.congr_hom hcomp w
  dsimp only [Functor.comp_map] at hmap
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hmap
  change (twoStepTotal A).map ((twoStepModuleQ A).map w) =
    Q.map w.hom.right at hmap
  have ht : Q.map w.hom.right ≫ (twoStepTotal A).map j.hom =
      (twoStepTotal A).map j.hom ≫ (twoStepTotal A).map v := by
    rw [← hmap]
    simpa only [Functor.map_comp] using congrArg ((twoStepTotal A).map) hw
  let := perfectTraceCanonicalBraiding (ModuleCat.{u} A)
  let := perfectTraceHasRightDual ((twoStepTotal A).obj P) h
  let := perfectTraceHasRightDual ((twoStepGraded A true).obj P) h'
  let := perfectTraceHasRightDual ((twoStepGraded A false).obj P) h''
  have ht' : (twoStepTotal A).map v ≫ ((twoStepTotal A).mapIso j.symm).hom =
      ((twoStepTotal A).mapIso j.symm).hom ≫ Q.map w.hom.right := by
    exact intertwine_iso_inv ((twoStepTotal A).mapIso j) _ _ ht
  have hg' (z : Bool) : (twoStepGraded A z).map v ≫
        ((twoStepGraded A z).mapIso j.symm).hom =
      ((twoStepGraded A z).mapIso j.symm).hom ≫
        Q.map ((twoStepGradedComplex A z).map w) := by
    exact intertwine_iso_inv ((twoStepGraded A z).mapIso j) _ _ (hgraded z)
  have htrace := trace_eq_trace_add_trace_of_shortExact S hS φ (Finset.Icc a b) hs
    (hfreeGr true) (fun i ↦ ((hMF i).2 true).1)
    (hfreeGr false) (fun i ↦ ((hMF i).2 false).1)
    _ _ _ ((twoStepGraded A true).map v) ((twoStepTotal A).map v)
    ((twoStepGraded A false).map v)
    ((twoStepGraded A true).mapIso j.symm) ((twoStepTotal A).mapIso j.symm)
    ((twoStepGraded A false).mapIso j.symm) (hg' true) ht' (hg' false)
  unfold perfectCategoricalTrace
  exact (congrArg perfectTraceScalar htrace).trans (traceScalar_add _ _)


/-- Additivity for exactly the localized filtered endomorphisms of clause (2).
Source: blueprint trace formal laws, clause (2); Stacks, Tags 03TB and 03TJ
(blueprint: prop-trf-trace-formal-laws).
Proof: use `lem-trf-filtered-projective-model` to obtain the bounded filtered model.
The coefficient ring is a quotient of the local DVR of integers, so its finite
projective modules are free (the zero-ring case is handled separately). Apply the
proved source-library `trace_eq_trace_add_trace_of_shortExact` to the compatible
chain endomorphism of the model short exact sequence. The total localization
factorization and the two graded comparison isomorphisms identify its three maps
with the given ones. Finally `perfectTraceScalar` preserves addition. -/
theorem perfectCategoricalTrace_filtered_additivity
    (D : WeilConjectures.FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : IntermediateField (Padic c.l) c.Qbar) [FiniteDimensional (Padic c.l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (P : TwoStepModuleDerived (Padic.coefficientExtensionRing c.l E n)) (v : P ⟶ P)
    (h : IsPerfectRingComplex.{u, u}
      ((twoStepTotal.{u, u} (Padic.coefficientExtensionRing c.l E n)).obj P))
    (h' : IsPerfectRingComplex.{u, u}
      ((twoStepGraded.{u, u} (Padic.coefficientExtensionRing c.l E n) true).obj P))
    (h'' : IsPerfectRingComplex.{u, u}
      ((twoStepGraded.{u, u} (Padic.coefficientExtensionRing c.l E n) false).obj P)) :
    WeilConjectures.finiteCoefficientCategoricalTrace D c E n hn _ h
        ((twoStepTotal.{u, u} (Padic.coefficientExtensionRing c.l E n)).map v) =
      WeilConjectures.finiteCoefficientCategoricalTrace D c E n hn _ h'
        ((twoStepGraded.{u, u} (Padic.coefficientExtensionRing c.l E n) true).map v) +
      WeilConjectures.finiteCoefficientCategoricalTrace D c E n hn _ h''
        ((twoStepGraded.{u, u} (Padic.coefficientExtensionRing c.l E n) false).map v) := by
  exact filtered_trace_of_free (fun M _ _ ↦ coefficient_projective_free D c E n M) P v h h' h''

/-- The explicit `Z/4` warning in clause (2): a Verdier triangle endomorphism
with zero end maps and nonzero middle trace. Its middle chain model is `R → R`,
differential `2`, in degrees `0,1`, and its endomorphism has components `0,2`.
Source: blueprint trace formal laws, clause (2); Stacks, Tag 087J
(blueprint: prop-trf-trace-formal-laws).
Proof: take the degreewise split exact sequence `R[-1] → [R → R] → R[0]`.
The middle differential and degree-one endomorphism are multiplication by two;
the chain equation is `2*2=0`. The left triangle square commutes by the homotopy
whose degree-one component is the identity; the right square commutes strictly,
and the last square is zero on both sides. The cone-to-quotient map is a
quasi-isomorphism, with contractible kernel the cone of the identity, so the
triangle is distinguished. The two terms are finite free. The chain supertrace
of the middle endomorphism is `0-2=-2`, nonzero in `Z/4`; both end maps are zero.
The restriction of the chain endomorphism to the subcomplex is two, rather than
the prescribed zero endomorphism, so this triple does not have filtered origin. -/
theorem perfectCategoricalTrace_triangle_counterexample :
    ∃ (M : CochainComplex (ModuleCat.{0} (ZMod 4)) ℤ) (w : M ⟶ M)
      (e₀ : M.X 0 ≅ ModuleCat.of (ZMod 4) (ZMod 4))
      (e₁ : M.X 1 ≅ ModuleCat.of (ZMod 4) (ZMod 4)),
      (∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (M.X i)) ∧
      e₀.inv ≫ M.d 0 1 ≫ e₁.hom = ModuleCat.ofHom (2 • LinearMap.id) ∧
      w.f 0 = 0 ∧ e₁.inv ≫ w.f 1 ≫ e₁.hom = ModuleCat.ofHom (2 • LinearMap.id) ∧
      ∃ (ι : (CochainComplex.singleFunctor (ModuleCat.{0} (ZMod 4)) 1).obj
          (ModuleCat.of (ZMod 4) (ZMod 4)) ⟶ M)
        (π : M ⟶ (CochainComplex.singleFunctor (ModuleCat.{0} (ZMod 4)) 0).obj
          (ModuleCat.of (ZMod 4) (ZMod 4))),
        (HomologicalComplex.singleObjXSelf (.up ℤ) 1
          (ModuleCat.of (ZMod 4) (ZMod 4))).inv ≫ ι.f 1 ≫ e₁.hom = 𝟙 _ ∧
        e₀.inv ≫ π.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (ModuleCat.of (ZMod 4) (ZMod 4))).hom = 𝟙 _ ∧
        ∃ (T : Triangle (DerivedCategory.{0} (ModuleCat.{0} (ZMod 4)))) (f : T ⟶ T),
          T ∈ distTriang _ ∧
          ∃ (a : T.obj₁ ≅ Q.obj ((CochainComplex.singleFunctor
              (ModuleCat.{0} (ZMod 4)) 1).obj (ModuleCat.of (ZMod 4) (ZMod 4))))
            (b : T.obj₂ ≅ Q.obj M)
            (c : T.obj₃ ≅ Q.obj ((CochainComplex.singleFunctor
              (ModuleCat.{0} (ZMod 4)) 0).obj (ModuleCat.of (ZMod 4) (ZMod 4)))),
            T.mor₁ ≫ b.hom = a.hom ≫ Q.map ι ∧
            T.mor₂ ≫ c.hom = b.hom ≫ Q.map π ∧
            f.hom₁ = 0 ∧ f.hom₃ = 0 ∧ f.hom₂ ≫ b.hom = b.hom ≫ Q.map w ∧
            ∃ h : IsPerfectRingComplex.{0, 0} T.obj₂,
              perfectCategoricalTrace.{0} (R := ZMod 4) T.obj₂ h f.hom₂ = -2 ∧
              perfectCategoricalTrace.{0} (R := ZMod 4) T.obj₂ h f.hom₂ ≠ 0 := by
  classical
  have : Fact (1 < 4) := ⟨by decide⟩
  let R := ZMod 4
  let V := ModuleCat.of R R
  let d : V ⟶ V := ModuleCat.ofHom (2 • LinearMap.id)
  let M : CochainComplex (ModuleCat.{0} R) ℤ :=
    HomologicalComplex.double d (show (ComplexShape.up ℤ).Rel 0 1 from rfl)
  let e₀ : M.X 0 ≅ V := HomologicalComplex.doubleXIso₀ d rfl
  let e₁ : M.X 1 ≅ V := HomologicalComplex.doubleXIso₁ d rfl (by decide)
  have hz (i : ℤ) (h₀ : i ≠ 0) (h₁ : i ≠ 1) : IsZero (M.X i) :=
    HomologicalComplex.isZero_double_X d rfl i h₀ h₁
  have hd : M.d 0 1 = e₀.hom ≫ d ≫ e₁.inv :=
    HomologicalComplex.double_d d rfl (by decide)
  have hd₁ (i : ℤ) : M.d 1 i = 0 :=
    HomologicalComplex.double_d_eq_zero₀ d rfl 1 i (by decide)
  have hd₀ (i : ℤ) : M.d i 0 = 0 :=
    HomologicalComplex.double_d_eq_zero₁ d rfl i 0 (by decide)
  have hdd : d ≫ d = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (2 : ℕ) • ((2 : ℕ) • x) = 0
    rw [← Nat.cast_smul_eq_nsmul R, ← Nat.cast_smul_eq_nsmul R, smul_smul]
    change (4 : ZMod 4) * x = 0
    rw [show (4 : ZMod 4) = 0 from by decide, zero_mul]
  let w : M ⟶ M := HomologicalComplex.mkHomFromDouble rfl (by decide)
    (0 : V ⟶ M.X 0) (d ≫ e₁.inv)
    (by rw [zero_comp, ← Category.assoc, hdd, zero_comp])
    (fun i _ ↦ by simp [hd₁])
  have hw₀ : w.f 0 = 0 := by simp [w]
  have hw₁ : e₁.inv ≫ w.f 1 ≫ e₁.hom = d := by simp [w, e₁]
  let L := (CochainComplex.singleFunctor (ModuleCat.{0} R) 1).obj V
  let N := (CochainComplex.singleFunctor (ModuleCat.{0} R) 0).obj V
  let ι : L ⟶ M := HomologicalComplex.mkHomFromSingle e₁.inv
    (fun i _ ↦ by simp [hd₁])
  let π : M ⟶ N := HomologicalComplex.mkHomToSingle e₀.hom
    (fun i _ ↦ by simp [hd₀])
  have hιπ : ι ≫ π = 0 := by
    apply HomologicalComplex.from_single_hom_ext
    apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 V 1 (by decide)).eq_of_tgt
  let S := ShortComplex.mk ι π hιπ
  have hS : S.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    let Sᵢ := S.map (HomologicalComplex.eval (ModuleCat.{0} R) (.up ℤ) i)
    by_cases hi₀ : i = 0
    · subst i
      have : IsIso Sᵢ.g := by
        change IsIso (π.f 0)
        dsimp [π]
        rw [HomologicalComplex.mkHomToSingle_f]
        infer_instance
      have hL : IsZero (L.X 0) :=
        HomologicalComplex.isZero_single_obj_X (.up ℤ) 1 V 0 (by decide)
      exact { exact := (Sᵢ.exact_iff_mono (hL.eq_of_src _ _)).2 inferInstance
              mono_f := hL.mono _ }
    · by_cases hi₁ : i = 1
      · subst i
        have : IsIso Sᵢ.f := by
          change IsIso (ι.f 1)
          dsimp [ι]
          rw [HomologicalComplex.mkHomFromSingle_f]
          infer_instance
        have hN : IsZero (N.X 1) :=
          HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 V 1 (by decide)
        exact { exact := (Sᵢ.exact_iff_epi (hN.eq_of_tgt _ _)).2 inferInstance
                epi_g := hN.epi _ }
      · have hL : IsZero (L.X i) :=
          HomologicalComplex.isZero_single_obj_X (.up ℤ) 1 V i hi₁
        have hN : IsZero (N.X i) :=
          HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 V i hi₀
        exact { exact := Sᵢ.exact_of_isZero_X₂ (hz i hi₀ hi₁)
                mono_f := hL.mono _
                epi_g := hN.epi _ }
  have hπ : w ≫ π = 0 := by
    apply HomologicalComplex.to_single_hom_ext
    simp [HomologicalComplex.comp_f, hw₀]
  let H : Homotopy (ι ≫ w) 0 :=
    { hom := fun i j ↦ if hi : i = 1 then
        if hj : j = 0 then eqToHom (by dsimp [L]; rw [hi]; rfl) ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 1 V).hom ≫ e₀.inv ≫
          eqToHom (by rw [hj]) else 0 else 0
      zero := by
        intro i j hij
        split_ifs with hi hj
        · subst i; subst j
          exact (hij rfl).elim
        · rfl
        · rfl
      comm := by
        intro i
        by_cases hi : i = 1
        · subst i
          rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 1 2 from rfl),
            prevD_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl)]
          simp [ι, w, hd]
        · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 1 V i hi).eq_of_src }
  have hι : Q.map ι ≫ Q.map w = 0 := by
    rw [← Functor.map_comp]
    exact (Q_map_eq_of_homotopy (ModuleCat R) H).trans (Functor.map_zero Q _ _)
  have hπ' : Q.map w ≫ Q.map π = 0 := by rw [← Functor.map_comp, hπ, Functor.map_zero]
  let T := triangleOfSES hS
  let f : T ⟶ T :=
    { hom₁ := 0
      hom₂ := Q.map w
      hom₃ := 0
      comm₁ := by simpa only [T, triangleOfSES_mor₁, zero_comp] using hι
      comm₂ := by simpa only [T, triangleOfSES_mor₂, comp_zero] using hπ'.symm
      comm₃ := by simp }
  have hMa : M.IsStrictlyGE 0 := (M.isStrictlyGE_iff 0).2
    (fun i hi ↦ hz i (by omega) (by omega))
  have hMb : M.IsStrictlyLE 1 := (M.isStrictlyLE_iff 1).2
    (fun i hi ↦ hz i (by omega) (by omega))
  have := hMa
  have := hMb
  have hfin (i : ℤ) : Module.Finite R (M.X i) := by
    by_cases hi₀ : i = 0
    · subst i
      exact Module.Finite.equiv e₀.toLinearEquiv.symm
    · by_cases hi₁ : i = 1
      · subst i
        exact Module.Finite.equiv e₁.toLinearEquiv.symm
      · have : Subsingleton (M.X i) := ModuleCat.isZero_iff_subsingleton.mp (hz i hi₀ hi₁)
        infer_instance
  have hfree (i : ℤ) : Module.Free R (M.X i) := by
    by_cases hi₀ : i = 0
    · subst i
      exact Module.Free.of_equiv e₀.toLinearEquiv.symm
    · by_cases hi₁ : i = 1
      · subst i
        exact Module.Free.of_equiv e₁.toLinearEquiv.symm
      · have : Subsingleton (M.X i) := ModuleCat.isZero_iff_subsingleton.mp (hz i hi₀ hi₁)
        infer_instance
  have hp : IsPerfectRingComplex (Q.obj M) :=
    ⟨M, 0, 1, hMa, hMb, fun i ↦ by
      have := hfree i
      exact ⟨inferInstance, hfin i⟩, ⟨Iso.refl _⟩⟩
  have htr₁ : LinearMap.trace R (M.X 1) (w.f 1).hom = 2 := by
    have h := LinearMap.trace_conj' (w.f 1).hom e₁.toLinearEquiv
    change LinearMap.trace R R (e₁.inv ≫ w.f 1 ≫ e₁.hom).hom = _ at h
    rw [← h, hw₁]
    change LinearMap.trace R R ((2 : ℕ) • LinearMap.id) = 2
    rw [map_nsmul, LinearMap.trace_id, Module.finrank_self]
    norm_num
  have ht : perfectCategoricalTrace (Q.obj M) hp (Q.map w) = -2 := by
    rw [trace_free_model M 0 1 hfree hfin _ hp (Q.map w) w (Iso.refl _) (by simp)]
    have hI : Finset.Icc (0 : ℤ) 1 = {0, 1} := by decide
    simp [hI, hw₀, htr₁]
  refine ⟨M, w, e₀, e₁, hz, ?_, hw₀, hw₁, ι, π, ?_, ?_, T, f,
    triangleOfSES_distinguished hS, Iso.refl _, Iso.refl _, Iso.refl _, ?_, ?_,
    rfl, rfl, ?_, hp, ht, ?_⟩
  · simpa only [hd, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
      using (show d = ModuleCat.ofHom (2 • LinearMap.id) from rfl)
  · simp [ι]
  · simp [π, V, R]
  · simp only [T, triangleOfSES_mor₁, Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [T, triangleOfSES_mor₂, Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp [f]
  · change perfectCategoricalTrace (Q.obj M) hp (Q.map w) ≠ 0
    rw [ht]
    decide


private theorem trace_scalar_extension_model {R B : Type u} [CommRing R] [CommRing B]
    (ρ : R →+* B)
    (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (η : Q ⋙ LF ⟶ (ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ) ⋙ Q)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [M.IsStrictlyGE a] [M.IsStrictlyLE b] [IsIso (η.app M)]
    (hfree : ∀ i, Module.Free R (M.X i))
    (hfin : ∀ i, Module.Finite R (M.X i))
    (P : DerivedCategory (ModuleCat.{u} R)) (hP : IsPerfectRingComplex P)
    (v : P ⟶ P) (w : M ⟶ M) (e : P ≅ Q.obj M)
    (hw : v ≫ e.hom = e.hom ≫ Q.map w) :
    ∃ hB : IsPerfectRingComplex (LF.obj P),
      ρ (perfectCategoricalTrace P hP v) = perfectCategoricalTrace _ hB (LF.map v) := by
  classical
  let F := ModuleCat.extendScalars ρ
  let MB : CochainComplex (ModuleCat.{u} B) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj M
  have hfreeB (i : ℤ) : Module.Free B (MB.X i) := by
    have := hfree i
    exact ModuleCat.free_extendScalars_obj ρ (M.X i)
  have hfinB (i : ℤ) : Module.Finite B (MB.X i) := by
    have := hfin i
    exact ModuleCat.finite_extendScalars_obj ρ (M.X i)
  let eB : LF.obj P ≅ Q.obj MB := LF.mapIso e ≪≫ asIso (η.app M)
  have hBa : MB.IsStrictlyGE a := inferInstance
  have hBb : MB.IsStrictlyLE b := inferInstance
  have hB : IsPerfectRingComplex (LF.obj P) :=
    ⟨MB, a, b, hBa, hBb, fun i ↦ by
      have := hfreeB i
      exact ⟨inferInstance, hfinB i⟩, ⟨eB⟩⟩
  have hwB : LF.map v ≫ eB.hom = eB.hom ≫
      Q.map ((F.mapHomologicalComplex (.up ℤ)).map w) := by
    change LF.map v ≫ LF.map e.hom ≫ η.app M = _
    have hn := η.naturality w
    change LF.map (Q.map w) ≫ η.app M =
      η.app M ≫ Q.map ((F.mapHomologicalComplex (.up ℤ)).map w) at hn
    rw [← Functor.map_comp_assoc, hw, Functor.map_comp, Category.assoc, hn]
    simp only [eB, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Category.assoc]
  have hs (i : ℤ) (hi : i ∉ Finset.Icc a b) : IsZero (M.X i) := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · exact M.isZero_of_isStrictlyGE a i hi
    · exact M.isZero_of_isStrictlyLE b i hi
  let := perfectTraceCanonicalBraiding (ModuleCat.{u} R)
  let := perfectTraceCanonicalBraiding (ModuleCat.{u} B)
  let := perfectTraceHasRightDual P hP
  let := perfectTraceHasRightDual (LF.obj P) hB
  obtain ⟨t, ht, htB⟩ := exists_trace_eq_algebraMap_and_trace_extendScalars_eq_algebraMap
    ρ M w (Finset.Icc a b) hs hfree hfin P v e hw (LF.obj P) (LF.map v) eB hwB
  refine ⟨hB, ?_⟩
  unfold perfectCategoricalTrace
  rw [ht, htB, traceScalar_algebraMap, traceScalar_algebraMap]

/-- Derived scalar extension preserves perfectness and the categorical trace, clause (3).
Source: blueprint trace formal laws, clause (3)
(blueprint: prop-trf-trace-formal-laws).
Proof: choose a bounded finite-projective model and a chain representative. Finite
projectives over the local coefficient quotient are free and hence flat. Bounded
flatness gives K-flatness, so the counit of the specified universal derived functor
is invertible on this model. Its naturality identifies the extended endomorphism
with the termwise extension. Tensor extension preserves finite freeness and the
degree bounds, proving perfectness. The source-library scalar-extension trace
calculation computes the two categorical traces as the algebra-map images of a
single scalar. Applying `perfectTraceScalar` recovers this scalar on each side.
No flatness assumption on the target ring is used. -/
theorem perfectCategoricalTrace_scalar_extension
    (D : WeilConjectures.FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : IntermediateField (Padic c.l) c.Qbar) [FiniteDimensional (Padic c.l) E]
    (n : ℕ) (hn : 1 ≤ n) {B : Type u} [CommRing B]
    (ρ : Padic.coefficientExtensionRing c.l E n →+* B)
    (LF : DerivedCategory.{u} (ModuleCat.{u} (Padic.coefficientExtensionRing c.l E n)) ⥤
      DerivedCategory.{u} (ModuleCat.{u} B))
    (ε : Qh ⋙ LF ⟶ (ModuleCat.extendScalars ρ).mapHomotopyCategory (.up ℤ) ⋙ Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} (Padic.coefficientExtensionRing c.l E n))
        (.up ℤ)))
    (P : DerivedCategory.{u} (ModuleCat.{u} (Padic.coefficientExtensionRing c.l E n)))
    (hP : IsPerfectRingComplex.{u, u} P) (v : P ⟶ P) :
    ∃ hB : IsPerfectRingComplex.{u, u} (LF.obj P),
      ρ (WeilConjectures.finiteCoefficientCategoricalTrace D c E n hn P hP v) =
        perfectCategoricalTrace.{u} (R := B) _ hB (LF.map v) := by
  obtain ⟨M, a, b, ha, hb, hM, e, w, hw⟩ := perfect_chain_representative P hP v
  have := ha
  have := hb
  have hfree (i : ℤ) : Module.Free (Padic.coefficientExtensionRing c.l E n) (M.X i) := by
    have := (hM i).1
    have := (hM i).2
    exact coefficient_projective_free D c E n _
  have hflat (i : ℤ) : Module.Flat (Padic.coefficientExtensionRing c.l E n) (M.X i) := by
    have := hfree i
    infer_instance
  have hk := CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat M
    ⟨b, fun i hi ↦ M.isZero_of_isStrictlyLE b i hi⟩ hflat
  have := ModuleCat.scalarExtensionCounit_isIso_of_kFlat ρ M hk LF ε hLF
  let F := ModuleCat.extendScalars ρ
  let H := HomotopyCategory.quotient
    (ModuleCat.{u} (Padic.coefficientExtensionRing c.l E n)) (.up ℤ)
  let η : Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ Q :=
    Functor.whiskerRight (quotientCompQhIso _).inv LF ≫
      Functor.whiskerLeft H ε ≫
      Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom Qh ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) (quotientCompQhIso _).hom
  have : IsIso (η.app M) := by dsimp [η]; infer_instance
  exact trace_scalar_extension_model ρ LF η M a b hfree (fun i ↦ (hM i).2)
    P hP v w e hw


set_option linter.unusedVariables false in
/-- The cohomological supertrace, clause (4), including perfectness of its field object.
Source: blueprint trace formal laws, clause (4)
(blueprint: prop-trf-trace-formal-laws).
Proof: the perfectness conclusion of `field_complex_cohomology_splitting` supplies
perfection from bounded finite-dimensional cohomology. Choose a bounded finite-free
chain model and an endomorphism representing the derived map. The existing signed
chain-trace calculation and Hopf trace formula identify its categorical trace with
the finite signed sum of homology traces. Naturality of `homologyFunctorFactors`
identifies the model homology endomorphisms with those of the given object, and
ordinary trace is invariant under conjugacy. Outside the model interval homology
is zero, so the finite sum equals the displayed finitely supported sum. -/
theorem perfectCategoricalTrace_cohomology
    (D : WeilConjectures.FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : IntermediateField (Padic c.l) c.Qbar) [FiniteDimensional (Padic c.l) E] :
    (∀ (P : DerivedCategory.{u} (ModuleCat.{u} E))
      (hP : pointFiniteDimensional E P) (v : P ⟶ P),
      ∃ h : IsPerfectRingComplex.{u, u} P,
        perfectCategoricalTrace.{u} (R := E) P h v = ∑ᶠ i : ℤ, i.negOnePow •
          LinearMap.trace E ((homologyFunctor.{u} (ModuleCat.{u} E) i).obj P)
            (((homologyFunctor.{u} (ModuleCat.{u} E) i).map v).hom)) ∧
    (∀ (P : DerivedCategory.{u} (ModuleCat.{u} c.Qbar))
      (hP : pointFiniteDimensional c.Qbar P) (v : P ⟶ P),
      ∃ h : IsPerfectRingComplex.{u, u} P,
        perfectCategoricalTrace.{u} (R := c.Qbar) P h v = ∑ᶠ i : ℤ, i.negOnePow •
          LinearMap.trace c.Qbar ((homologyFunctor.{u} (ModuleCat.{u} c.Qbar) i).obj P)
            (((homologyFunctor.{u} (ModuleCat.{u} c.Qbar) i).map v).hom)) := by
  exact ⟨fun P hP v ↦ field_trace P hP v, fun P hP v ↦ field_trace P hP v⟩

private theorem trace_conjugacy {R : Type u} [CommRing R]
    {P₁ P₂ : DerivedCategory (ModuleCat.{u} R)}
    (h₁ : IsPerfectRingComplex P₁) (h₂ : IsPerfectRingComplex P₂)
    (v₁ : P₁ ⟶ P₁) (v₂ : P₂ ⟶ P₂) (e : P₁ ≅ P₂)
    (he : v₁ ≫ e.hom = e.hom ≫ v₂) :
    perfectCategoricalTrace P₁ h₁ v₁ = perfectCategoricalTrace P₂ h₂ v₂ := by
  let := perfectTraceCanonicalBraiding (ModuleCat.{u} R)
  let := perfectTraceHasRightDual P₁ h₁
  let := perfectTraceHasRightDual P₂ h₂
  unfold perfectCategoricalTrace
  exact congrArg perfectTraceScalar (MonoidalCategory.trace_eq_of_iso e v₁ v₂ he)

private theorem field_trace_extension {F K : Type u} [Field F] [Field K]
    (ρ : F →+* K) (P : DerivedCategory (ModuleCat.{u} F))
    (hP : pointFiniteDimensional F P) (v : P ⟶ P) :
    ∃ (h : IsPerfectRingComplex P)
      (hK : IsPerfectRingComplex ((fieldDerivedScalarExtension ρ).obj P)),
      ρ (perfectCategoricalTrace P h v) =
        perfectCategoricalTrace _ hK ((fieldDerivedScalarExtension ρ).map v) := by
  have hp := ((field_complex_cohomology_splitting F).2.2.2.1 P hP).2
  obtain ⟨M, a, b, ha, hb, hM, e, w, hw⟩ := perfect_chain_representative P hp v
  have := ha
  have := hb
  have hfree (i : ℤ) : Module.Free F (M.X i) := inferInstance
  obtain ⟨hK, ht⟩ := trace_scalar_extension_model ρ (fieldDerivedScalarExtension ρ)
    (ModuleCat.extendScalars ρ).mapDerivedCategoryFactors.hom M a b hfree
    (fun i ↦ (hM i).2) P hp v w e hw
  exact ⟨hp, hK, ht⟩

private theorem field_presentation_trace {F K : Type u} [Field F] [Field K]
    (ρ : F →+* K) (P : DerivedCategory (ModuleCat.{u} F))
    (hP : pointFiniteDimensional F P) (Y : DerivedCategory (ModuleCat.{u} K))
    (hY : IsPerfectRingComplex Y) (w : P ⟶ P) (v : Y ⟶ Y)
    (e : (fieldDerivedScalarExtension ρ).obj P ≅ Y)
    (he : (fieldDerivedScalarExtension ρ).map w ≫ e.hom = e.hom ≫ v) :
    ∃ h : IsPerfectRingComplex P,
      ρ (perfectCategoricalTrace P h w) = perfectCategoricalTrace Y hY v ∧
      ρ (∑ᶠ i : ℤ, i.negOnePow •
        LinearMap.trace F ((homologyFunctor (ModuleCat.{u} F) i).obj P)
          (((homologyFunctor (ModuleCat.{u} F) i).map w).hom)) =
        perfectCategoricalTrace Y hY v := by
  obtain ⟨hp, hK, hscalar⟩ := field_trace_extension ρ P hP w
  obtain ⟨hp', hfield⟩ := field_trace P hP w
  have ht := hscalar.trans (trace_conjugacy hK hY _ _ e he)
  exact ⟨hp, ht, by rw [← hfield]; exact ht⟩

private theorem common_stage_trace
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (X : PointFdQbar l Ω) (v : X ⟶ X) :
    ∃! t : Ω, ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (P : (pointFiniteDimensional E.val).FullSubcategory)
      (e : (pointFdQbarStage l Ω E).obj P ≅ X) (w : P.obj ⟶ P.obj),
      (pointFdQbarStage l Ω E).map (ObjectProperty.homMk w) ≫ e.hom = e.hom ≫ v →
      ∃ h : IsPerfectRingComplex.{u, u} P.obj,
        E.val.subtype (perfectCategoricalTrace.{u} (R := E.val) P.obj h w) = t ∧
        E.val.subtype (∑ᶠ i : ℤ, i.negOnePow •
          LinearMap.trace E.val ((homologyFunctor.{u} (ModuleCat.{u} E.val) i).obj P.obj)
            (((homologyFunctor.{u} (ModuleCat.{u} E.val) i).map w).hom)) = t := by
  classical
  let Y := pointFdQbarObject l Ω X
  have hY : pointFiniteDimensional Ω Y :=
    fieldDerivedScalarExtension_preserves (K := X.1.val) (L := Ω)
      X.1.val.subtype X.2.obj X.2.property
  have hpY := ((field_complex_cohomology_splitting Ω).2.2.2.1 Y hY).2
  let t := perfectCategoricalTrace Y hpY v.hom
  have hvalue (E : Padic.FiniteCoefficientFields l Ω)
      (P : (pointFiniteDimensional E.val).FullSubcategory)
      (e : (pointFdQbarStage l Ω E).obj P ≅ X) (w : P.obj ⟶ P.obj)
      (hw : (pointFdQbarStage l Ω E).map (ObjectProperty.homMk w) ≫ e.hom =
        e.hom ≫ v) :
      ∃ h : IsPerfectRingComplex.{u, u} P.obj,
        E.val.subtype (perfectCategoricalTrace (R := E.val) P.obj h w) = t ∧
        E.val.subtype (∑ᶠ i : ℤ, i.negOnePow •
          LinearMap.trace E.val ((homologyFunctor (ModuleCat.{u} E.val) i).obj P.obj)
            (((homologyFunctor (ModuleCat.{u} E.val) i).map w).hom)) = t := by
    let eΩ := (pointFdQbarRealization l Ω).mapIso e
    dsimp only [pointFdQbarRealization, inducedFunctor, Functor.mapIso,
      pointFdQbarObject, pointFdQbarStage] at eΩ
    exact field_presentation_trace (F := E.val) (K := Ω) E.val.subtype
      P.obj P.property Y hpY w v.hom eΩ
      (congrArg (fun f : (pointFdQbarStage l Ω E).obj P ⟶ X ↦ f.hom) hw)
  refine ⟨t, hvalue, ?_⟩
  intro t' ht'
  let C := pointFdQbarCocone l Ω
  obtain ⟨N, h₁, h₂, w, hw⟩ :=
    (pointFdQbarCocone_isFilteredTwoColimit l Ω).homSurj
      X.1 X.1 X.2 X.2 v
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  subst hh
  let P := (C.T h₁).obj X.2
  let e : (pointFdQbarStage l Ω N).obj P ≅ X := (C.iso h₁).app X.2
  have he : (pointFdQbarStage l Ω N).map w ≫ e.hom = e.hom ≫ v := by
    rw [hw]
    change _ = e.hom ≫ e.inv ≫ _ ≫ e.hom
    simp
    rfl
  obtain ⟨hp, hp₁, _⟩ := hvalue N P e w.hom he
  obtain ⟨hp', hp₂, _⟩ := ht' N P e w.hom he
  exact hp₂.symm.trans hp₁



/-- The common-stage Qlbar trace is the unique scalar computed at every finite
coefficient-field presentation, and is the corresponding cohomological supertrace.
Source: blueprint trace formal laws, clause (4), common-stage paragraph
(blueprint: prop-trf-trace-formal-laws).
Proof: define the scalar by the perfect categorical trace of the actual realization
in the fixed algebraic closure; exact scalar extension preserves its bounded finite
cohomology. For every finite-stage presentation, scalar-extension compatibility and
conjugacy along the realized comparison isomorphism give this same scalar. The field
Hopf trace formula gives the second equality. For uniqueness, Hom surjectivity of
the common-stage cocone supplies one finite-stage representative of the endomorphism.
The two maps from its original field to that stage agree, hence the canonical
comparison isomorphism intertwines this representative with the given map. Evaluate
both proposed scalars on it. No equivalence with all of the derived category of the
closure is assumed. -/
theorem perfectCategoricalTrace_common_stage
    (D : WeilConjectures.FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (X : PointFdQbar c.l c.Qbar) (v : X ⟶ X) :
    ∃! t : c.Qbar, ∀ (E : Padic.FiniteCoefficientFields c.l c.Qbar)
      (P : (pointFiniteDimensional E.val).FullSubcategory)
      (e : (pointFdQbarStage c.l c.Qbar E).obj P ≅ X) (w : P.obj ⟶ P.obj),
      (pointFdQbarStage c.l c.Qbar E).map (ObjectProperty.homMk w) ≫ e.hom = e.hom ≫ v →
      ∃ h : IsPerfectRingComplex.{u, u} P.obj,
        E.val.subtype (perfectCategoricalTrace.{u} (R := E.val) P.obj h w) = t ∧
        E.val.subtype (∑ᶠ i : ℤ, i.negOnePow •
          LinearMap.trace E.val ((homologyFunctor.{u} (ModuleCat.{u} E.val) i).obj P.obj)
            (((homologyFunctor.{u} (ModuleCat.{u} E.val) i).map w).hom)) = t := by
  exact common_stage_trace c.l c.Qbar X v

end DerivedCategory
