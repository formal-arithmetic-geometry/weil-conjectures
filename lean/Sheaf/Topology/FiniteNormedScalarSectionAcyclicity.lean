/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Sheaf.Topology.FiniteNormedScalarCechVanishing
import Sheaf.Topology.ProfiniteCechDerivedVanishing
import Sheaf.Topology.ProfiniteInternalModuleEvaluationComparison
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Sectionwise acyclicity of finite normed scalar coefficients

Source: Bhatt--Scholze, Lemma 4.3.9(2)--(4); Stacks Project, Tags 03F9 and 03FD.
(blueprint: lem-sfb-finite-normed-scalar-section-acyclicity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite

/-- Bundle the recorded continuous-function ring with its pointwise commutative multiplication.
Source: Bhatt--Scholze 4.3.9; Stacks 03FD
(blueprint: lem-sfb-finite-normed-scalar-section-acyclicity). -/
def finiteScalarSectionRing (E : Type u) [NormedField E] :
    CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) where
  X := continuousMapRingObjOfUniverse E
  mon := continuousMapRingObjOfUniverseMonObj E
  comm := isCommMonObj_continuousMapRingObjOfUniverse E

/-- Evaluation of an internal scalar module after the recorded sectionwise equivalence.
Its sections and maps are literally those of the original underlying abelian sheaf.
Source: Stacks 00YV and 03FD
(blueprint: lem-sfb-finite-normed-scalar-section-acyclicity). -/
abbrev finiteScalarSectionEvaluation (E : Type u) [NormedField E] (V : Profinite.{u}) :=
  Mod.forget (finiteScalarSectionRing E).X ⋙
    sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} ⋙
    (evaluation Profinite.{u}ᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)

private theorem scalar_cech_vanishing_with_empty (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (V : Profinite.{u}) (T : Type v) [Finite T] (W : T → Profinite.{u})
    (f : ∀ t, W t ⟶ V) (hf : ∀ v : V, ∃ t, ∃ w : W t, f t w = v)
    (S : SiteCechComplex W f) (q : ℕ) (hq : 0 < q) :
    IsZero ((S.cohomologyFunctor q).obj (continuousMapRingObjOfUniverse E).obj) := by
  cases isEmpty_or_nonempty T with
  | inl h =>
    have : IsEmpty T := h
    change IsZero ((S.complex (continuousMapRingObjOfUniverse E).obj).homology q)
    apply HomologicalComplex.ExactAt.isZero_homology
    apply HomologicalComplex.ExactAt.of_isZero
    change IsZero (S.cochains (continuousMapRingObjOfUniverse E).obj q)
    have : Subsingleton (S.cochains (continuousMapRingObjOfUniverse E).obj q) := by
      change Subsingleton (∀ t : Fin (q + 1) → T, _)
      refine ⟨fun a b ↦ funext fun t ↦ ?_⟩
      exact isEmptyElim (t 0)
    exact AddCommGrpCat.isZero_of_subsingleton _
  | inr h =>
    have : Nonempty T := h
    exact finiteNormedScalar_cech_vanishing l E V T W f hf S q hq

/-- Finite extensions with the extending norm are complete, Cech-acyclic, and acyclic
for evaluation on every profinite object. Every internal module injective resolution
of the regular module has an exact augmented section complex, with its given augmentation
inducing the degree-zero identification and zero positive cohomology.

Source: Bhatt--Scholze, Lemma 4.3.9(2)--(4); Stacks Tags 03F9 and 03FD
(blueprint: lem-sfb-finite-normed-scalar-section-acyclicity).

Proof: (1) Completeness follows from finite dimensionality over Q_l. For a finite cover,
form the finite disjoint union of its sources. It is profinite and surjects onto V.
The equal-image tuples decompose into clopen pieces indexed by tuples of summands.
Restriction and gluing identify its continuous-function alternating complex with the
recorded family Cech complex, commuting with coordinate deletion. Apply
lem-sfb-normed-scalar-profinite-cech-exact to obtain a primitive in every positive degree.
The empty family covers only the empty object, where all groups vanish.
(2) Apply lem-weil-pbc-site-cech-vanishing-criterion (03F9), taking all profinite objects
and all finite jointly surjective covers. Finite fibre products remain profinite and
each cover refines itself. The universe convention provides the small-site size bound.
(3) By lem-sfb-profinite-free-hom-resolution-evaluation, the internal-to-sectionwise
module equivalence is exact and preserves injectives. Apply
lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison (03FD) to the transported
arbitrary resolution and the regular module. Its positive cohomology is the vanishing
abelian cohomology from (2), and its degree-zero identification is the given augmentation.
(4) In a nonnegative complex, degree zero is the kernel of the first differential.
Thus the augmentation is injective with image that kernel. Positive homology vanishing
is image equals kernel in every later degree. On the empty object the sheaf condition
for the empty cover makes the augmented complex zero. No locally constant substitution,
algebraic closure, or assumption on the underlying abelian injectivity is used. -/
theorem finiteNormedScalar_section_acyclicity (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    CompleteSpace E ∧
    (∀ (V : Profinite.{u}) (T : Type u) [Finite T] (W : T → Profinite.{u})
      (f : ∀ t, W t ⟶ V), (∀ v : V, ∃ t, ∃ w : W t, f t w = v) →
      ∀ (S : SiteCechComplex W f) (q : ℕ), 0 < q →
        IsZero ((S.cohomologyFunctor q).obj (continuousMapRingObjOfUniverse E).obj)) ∧
    (∀ (V : Profinite.{u}) (q : ℕ), 0 < q →
      IsZero (((sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} ⋙
        (evaluation Profinite.{u}ᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).rightDerived q).obj
          (continuousMapRingObjOfUniverse E))) ∧
    (∀ (I : InjectiveResolution (Mod.regular (finiteScalarSectionRing E).X))
      (V : Profinite.{u}),
      Function.Injective ((finiteScalarSectionEvaluation E V).map (I.ι.f 0)) ∧
      Function.Exact ((finiteScalarSectionEvaluation E V).map (I.ι.f 0))
        ((finiteScalarSectionEvaluation E V).map (I.cocomplex.d 0 1)) ∧
      (∀ n : ℕ, Function.Exact
        ((finiteScalarSectionEvaluation E V).map (I.cocomplex.d n (n + 1)))
        ((finiteScalarSectionEvaluation E V).map (I.cocomplex.d (n + 1) (n + 2)))) ∧
      IsIso (HomologicalComplex.homologyMap
        (((finiteScalarSectionEvaluation E V).mapHomologicalComplex (.up ℕ)).map I.ι) 0) ∧
      ∀ q : ℕ, 0 < q → IsZero
        ((((finiteScalarSectionEvaluation E V).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex).homology q)) := by
  have hcech := scalar_cech_vanishing_with_empty.{u, u} l E
  have hab := isZero_rightDerived_eval_of_profinite_cech
    (continuousMapRingObjOfUniverse E) (scalar_cech_vanishing_with_empty.{u, 0} l E)
  refine ⟨FiniteDimensional.complete (Padic l) E, hcech, hab, ?_⟩
  intro I V
  let F := finiteScalarSectionEvaluation E V
  have hzero (q : ℕ) (hq : 0 < q) :
      IsZero (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology q) := by
    obtain ⟨e⟩ := nonempty_internalModule_eval_homology_iso
      (finiteScalarSectionRing E) (Mod.regular (finiteScalarSectionRing E).X) I V q hq
    exact (hab V q hq).of_iso e
  have hkernel := KernelFork.mapIsLimit _ I.isLimitKernelFork F
  have hfirst :
      (ShortComplex.mk (F.map (I.ι.f 0)) (F.map (I.cocomplex.d 0 1))
        (by rw [← F.map_comp, I.ι_f_zero_comp_complex_d, F.map_zero])).Exact ∧
      Mono (F.map (I.ι.f 0)) := by
    rw [ShortComplex.exact_and_mono_f_iff_f_is_kernel]
    exact ⟨hkernel⟩
  refine ⟨(AddCommGrpCat.mono_iff_injective _).mp hfirst.2,
    (ShortComplex.ab_exact_iff_function_exact _).mp hfirst.1, ?_, ?_, hzero⟩
  · intro n
    have hex : ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).ExactAt (n + 1) :=
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (hzero _ (Nat.succ_pos n))
    exact (ShortComplex.ab_exact_iff_function_exact _).mp
      ((HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
        (by simp only [CochainComplex.next]; rfl)).mp hex)
  · rw [← quasiIsoAt_iff_isIso_homologyMap,
      CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · rw [ShortComplex.exact_and_mono_f_iff_f_is_kernel]
      exact ⟨hkernel⟩
    all_goals simp

end Profinite
