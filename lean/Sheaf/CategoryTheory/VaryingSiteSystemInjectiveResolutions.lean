/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Sheaf.CategoryTheory.VaryingSiteSystem
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Sheaf.CategoryTheory.VaryingSiteSystemAbelian
import Sheaf.CategoryTheory.VaryingSiteSystemEvaluationAdjoints
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Injective resolutions of varying-site systems

Source: Stacks Project, sites-cohomology.tex, Tag 0EXZ,
lemma-colim-sites-injective; derived.tex, Tag 013K,
lemma-injective-resolutions-exist (3), generalized to a small index category
(blueprint: lem-per-varying-site-system-injective-resolutions).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory

variable {I : Type u} [SmallCategory I]

private noncomputable def systemProduct (D : VaryingSiteDiagram.{u} I)
    (e : VaryingSiteCoherence D) {T : Type u} (F : T → VaryingSiteSystem D e) :
    VaryingSiteSystem D e where
  obj i := ∏ᶜ fun t ↦ (F t).obj i
  transition a := Pi.lift fun t ↦ (D.pull a).map (Pi.π _ t) ≫ (F t).transition a
  identity i := by
    apply Pi.hom_ext
    intro t
    rw [Pi.lift_π, (F t).identity]
    exact (e.unit i).hom.naturality (Pi.π _ t)
  cocycle b a := by
    apply Pi.hom_ext
    intro t
    dsimp
    rw [Pi.lift_π, Category.assoc, Category.assoc, Pi.lift_π]
    rw [← Category.assoc ((D.pull b).map _) ((D.pull b).map _),
      ← Functor.map_comp, Pi.lift_π, Functor.map_comp, (F t).cocycle]
    simp only [Category.assoc]
    rw [← Category.assoc, ← Category.assoc, (e.comp b a).hom.naturality]
    simp only [Category.assoc, Functor.comp_map]

private noncomputable def systemProductProjection (D : VaryingSiteDiagram.{u} I)
    (e : VaryingSiteCoherence D) {T : Type u} (F : T → VaryingSiteSystem D e) (t : T) :
    systemProduct D e F ⟶ F t :=
  ⟨fun i ↦ Pi.π _ t, by
    intro j i a
    exact (Pi.lift_π (fun t ↦
      (D.pull a).map (Pi.π (fun t ↦ (F t).obj i) t) ≫ (F t).transition a) t).symm⟩

private noncomputable def systemProductFan (D : VaryingSiteDiagram.{u} I)
    (e : VaryingSiteCoherence D) {T : Type u} (F : T → VaryingSiteSystem D e) : Fan F :=
  Fan.mk (systemProduct D e F) (systemProductProjection D e F)

private noncomputable def systemProductLift (D : VaryingSiteDiagram.{u} I)
    (e : VaryingSiteCoherence D) {T : Type u} (F : T → VaryingSiteSystem D e)
    (s : Fan F) : s.pt ⟶ systemProduct D e F :=
  ⟨fun i ↦ Pi.lift fun t ↦ (s.proj t).val i, by
    intro j i a
    apply Pi.hom_ext
    intro t
    change ((D.pull a).map (Pi.lift fun t ↦ (s.proj t).val i) ≫
        Pi.lift (fun t ↦ (D.pull a).map (Pi.π _ t) ≫ (F t).transition a)) ≫
        Pi.π _ t = _
    rw [Category.assoc, Pi.lift_π, ← Category.assoc, ← Functor.map_comp, Pi.lift_π]
    rw [(s.proj t).property a, Category.assoc, Pi.lift_π]⟩

private noncomputable def systemProductIsLimit (D : VaryingSiteDiagram.{u} I)
    (e : VaryingSiteCoherence D) {T : Type u} (F : T → VaryingSiteSystem D e) :
    IsLimit (systemProductFan D e F) := by
  refine Fan.IsLimit.mk _ (systemProductLift D e F) ?_ ?_
  · intro s t
    apply Subtype.ext
    funext i
    exact Pi.lift_π _ t
  · intro s m hm
    apply Subtype.ext
    funext i
    apply Pi.hom_ext
    intro t
    have ht := congrArg (fun f ↦ f.val i) (hm t)
    exact ht.trans (Pi.lift_π (fun t ↦ (s.proj t).val i) t).symm

private theorem systemProducts (D : VaryingSiteDiagram.{u} I)
    (e : VaryingSiteCoherence D) : HasProducts.{u} (VaryingSiteSystem D e) :=
  hasProducts_of_limit_fans (systemProductFan D e) (systemProductIsLimit D e)

/-- Systems form an abelian category with enough injectives; evaluation is exact,
preserves injectives, and computes kernels and cokernels componentwise. Every complex
zero below an integer admits a degreewise monomorphic injective resolution with the
same lower bound, also an injective resolution at each site.

Source: Stacks Project, Tag 0EXZ, lemma-colim-sites-injective; Tag 013K(3),
lemma-injective-resolutions-exist
(blueprint: lem-per-varying-site-system-injective-resolutions).

Proof:
1. Compute addition, kernels, cokernels and finite biproducts componentwise, using
   exactness of inverse image (lem-weil-pbc-site-pullback-abelian-exact). Kernel
   inclusions and cokernel projections cancel to prove all system laws and universal
   properties. The coimage-image comparison and its inverse are componentwise, giving
   an abelian category (def-sp-abelian) and exact evaluations. Abelian sheaf categories
   are supplied by lem-weil-pbc-site-sheaves-enough-injectives.
2. The free evaluation adjoint in lem-per-varying-site-evaluation-adjoints is a sum
   of inverse images. Finite subsums preserve monomorphisms; exact filtered colimits
   (lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact) give the full sum.
   Apply lem-exc-rg-right-adjoint-preserves-injectives to evaluation, which is its
   right adjoint, to obtain preservation of injectives.
3. Choose embeddings F_i into injective sheaves A_i using
   lem-weil-pbc-site-sheaves-enough-injectives. The cofree evaluation adjoints R_i
   preserve injectives by exactness of evaluation and
   lem-exc-rg-right-adjoint-preserves-injectives. Their product exists componentwise
   (lem-weil-pbc-sheafification-exact) and is injective by
   lem-weil-pbc-product-injectives. The adjoint embeddings assemble into F to the
   product of R_i A_i. Projection to the identity factor recovers the chosen embedding
   at every vertex; this proves the assembled map monic and gives enough injectives.
4. Apply lem-weil-pbc-complex-injective-resolution-mono with the prescribed lower
   bound. Evaluation preserves its injective terms by step 2, and preserves the
   quasi-isomorphism by exactness and lem-sp-exact-functor-preserves-homology.
   Every index used is small. For empty I the system category is the zero category.
   No filteredness, finite-cover or colimit-site hypothesis occurs.
-/
theorem varyingSiteSystem_injective_resolutions
    {I : Type u} [SmallCategory I] (D : VaryingSiteDiagram.{u} I)
    (e : VaryingSiteCoherence D) :
    ∃ (_ : Abelian (VaryingSiteSystem D e)),
      ∃ (_ : ∀ i : I, (VaryingSiteSystem.evaluation D e i).Additive),
        EnoughInjectives (VaryingSiteSystem D e) ∧
        (∀ i : I,
          PreservesFiniteLimits (VaryingSiteSystem.evaluation D e i) ∧
          PreservesFiniteColimits (VaryingSiteSystem.evaluation D e i) ∧
          ∀ F : VaryingSiteSystem D e, Injective F → Injective (F.obj i)) ∧
        (∀ (F G : VaryingSiteSystem D e) (h : F ⟶ G) (c : KernelFork h),
          Nonempty (IsLimit c) ↔ ∀ i : I,
            Nonempty (IsLimit ((VaryingSiteSystem.evaluation D e i).mapCone c))) ∧
        (∀ (F G : VaryingSiteSystem D e) (h : F ⟶ G) (c : CokernelCofork h),
          Nonempty (IsColimit c) ↔ ∀ i : I,
            Nonempty (IsColimit ((VaryingSiteSystem.evaluation D e i).mapCocone c))) ∧
        ∀ (b : ℤ) (K : CochainComplex (VaryingSiteSystem D e) ℤ),
          (∀ n : ℤ, n < b → IsZero (K.X n)) →
          ∃ (J : CochainComplex (VaryingSiteSystem D e) ℤ) (s : K ⟶ J),
            (∀ n : ℤ, n < b → IsZero (J.X n)) ∧
            (∀ n : ℤ, Injective (J.X n)) ∧
            (∀ n : ℤ, Mono (s.f n)) ∧ QuasiIso s ∧
            (∀ (i : I) (n : ℤ), Injective ((J.X n).obj i)) ∧
            ∀ i : I, QuasiIso
              (((VaryingSiteSystem.evaluation D e i).mapHomologicalComplex
                (ComplexShape.up ℤ)).map s) := by
  classical
  obtain ⟨hAb, hAdd, hExact, hKer, hCoker⟩ :=
    varyingSiteSystem_abelian_componentwise D e
  let := hAb
  let := hAdd
  let := systemProducts D e
  have hInj (i : I) (F : VaryingSiteSystem D e) (hF : Injective F) :
      Injective (F.obj i) := by
    obtain ⟨L, ⟨adj⟩, hL⟩ := (varyingSiteSystem_evaluation_adjoints D e i).1
    let := hL
    exact adj.map_injective F hF
  have hEnough : EnoughInjectives (VaryingSiteSystem D e) := by
    have hRight (i : I) := (varyingSiteSystem_evaluation_adjoints D e i).2
    choose R hR using hRight
    let adj (i : I) := (hR i).some
    have hEvalMono (i : I) :
        (VaryingSiteSystem.evaluation D e i).PreservesMonomorphisms := by
      let := (hExact i).1
      infer_instance
    refine ⟨fun F ↦ ?_⟩
    let A (i : I) := Injective.under (F.obj i)
    have hA (i : I) : Injective (A i) := inferInstance
    have hRA (i : I) : Injective ((R i).obj (A i)) :=
      (adj i).map_injective (A i) (hA i)
    let G := ∏ᶜ fun i ↦ (R i).obj (A i)
    let f : F ⟶ G := Pi.lift fun i ↦ (adj i).homEquiv _ _ (Injective.ι (F.obj i))
    have hf : Mono f := by
      refine ⟨fun {X} a b hab ↦ ?_⟩
      apply Subtype.ext
      funext i
      apply (cancel_mono (Injective.ι (F.obj i))).1
      have hi := congrArg
        (fun g ↦ ((adj i).homEquiv X (A i)).symm
          (g ≫ Pi.π (fun j ↦ (R j).obj (A j)) i)) hab
      simp only [f, Category.assoc, Pi.lift_π,
        Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply] at hi
      dsimp only [VaryingSiteSystem.evaluation, A] at hi
      exact hi
    exact ⟨{ J := G, f := f }⟩
  let := hEnough
  refine ⟨hAb, hAdd, hEnough, fun i ↦ ⟨(hExact i).1, (hExact i).2, hInj i⟩,
    hKer, hCoker, ?_⟩
  intro b K hK
  obtain ⟨J, s, hBound, hTerms, hMono, hQuasi⟩ :=
    CochainComplex.exists_mono_quasiIso_injective_boundedBelow _ b K hK
  refine ⟨J, s, hBound, hTerms, hMono, hQuasi, fun i n ↦ hInj i (J.X n) (hTerms n), ?_⟩
  intro i
  let := (hExact i).1
  let := (hExact i).2
  let := hQuasi
  infer_instance

end CategoryTheory
