/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.ArrowCechComplex
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Čech complexes of short exact sequences of sheaves

Let `(C, J)` be a site, `A` an abelian category and `f : U ⟶ V` a morphism of `C` generating a
covering sieve of `V`. For a short exact sequence `0 ⟶ G₁ ⟶ G₂ ⟶ G₃ ⟶ 0` of `A`-valued sheaves,
we show, without using elements of `A`:

- if the first Čech cohomology of `G₁` along `f` vanishes and `G₂(U) ⟶ G₃(U)` is an
  epimorphism, then so is `G₂(V) ⟶ G₃(V)`
  (`CategoryTheory.Arrow.epi_app_right_of_exactAt_cechComplex_one`);
- if `G₂(U_n) ⟶ G₃(U_n)` is an epimorphism on all objects `U_n = U ×_V ⋯ ×_V U` of the Čech
  nerve, and the Čech complexes of `G₁` and `G₂` are exact in positive degrees, then so is the
  Čech complex of `G₃` (`CategoryTheory.Arrow.exactAt_cechComplex_X₃`).

These are the two steps of the dimension shifting argument in the Čech acyclicity criterion
(Stacks 03F9). We also show that a morphism of sheaves is an epimorphism as soon as it is so on
sections over the objects of a cover dense subcategory
(`CategoryTheory.Sheaf.epi_of_epi_app_obj`).
-/

@[expose] public section

universe w' w v v' u u'

open CategoryTheory Limits Opposite Simplicial

namespace CategoryTheory

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type w} [Category.{w'} A] [Preadditive A]

/-- A morphism of sheaves with values in a preadditive category is an epimorphism if it is so on
sections over the objects of a cover dense subcategory. -/
lemma epi_of_epi_app_obj {C' : Type u'} [Category.{v'} C'] (G : C' ⥤ C) [G.IsCoverDense J]
    {F₁ F₂ : Sheaf J A} (φ : F₁ ⟶ F₂) (h : ∀ Y : C', Epi (φ.hom.app (op (G.obj Y)))) :
    Epi φ := by
  refine Preadditive.epi_of_cancel_zero _ fun {R} g hg ↦ ?_
  have h₀ (Y : C') : g.hom.app (op (G.obj Y)) = 0 := by
    rw [← cancel_epi (φ.hom.app (op (G.obj Y))), comp_zero, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, hg]
    rfl
  ext V : 2
  refine R.property.hom_ext ⟨_, G.is_cover_of_isCoverDense J V.unop⟩ _ _ fun I ↦ ?_
  obtain ⟨⟨Y, a, b, hab⟩⟩ := I.hf
  rw [← hab, op_comp, Functor.map_comp, ← Category.assoc, ← g.hom.naturality, Category.assoc,
    h₀ Y, zero_comp, comp_zero]
  simp

end Sheaf

namespace Arrow

variable {C : Type u} [Category.{v} C] (f : Arrow C)
  [∀ n : ℕ, HasWidePullback.{0} f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]

/-- The augmentation `U ×_V ⋯ ×_V U ⟶ V` of an object of the Čech nerve of `f : U ⟶ V`. -/
noncomputable abbrev cechNerveBase (n : ℕ) : f.cechNerve.obj (op ⦋n⦌) ⟶ f.right :=
  WidePullback.base fun _ : Fin (n + 1) => f.hom

@[reassoc (attr := simp)]
lemma cechNerve_map_cechNerveBase {n m : ℕ} (θ : op ⦋n⦌ ⟶ op ⦋m⦌) :
    f.cechNerve.map θ ≫ f.cechNerveBase m = f.cechNerveBase n := by
  dsimp [Arrow.cechNerve]
  rw [WidePullback.lift_base]

@[reassoc (attr := simp)]
lemma cechNerve_map_π {n m : ℕ} (θ : op ⦋n⦌ ⟶ op ⦋m⦌) (j : Fin (m + 1)) :
    f.cechNerve.map θ ≫ WidePullback.π (fun _ : Fin (m + 1) => f.hom) j =
      WidePullback.π (fun _ : Fin (n + 1) => f.hom) (θ.unop.toOrderHom j) := by
  dsimp [Arrow.cechNerve]
  rw [WidePullback.lift_π]

/-- The section `U ⟶ U ×_V U ×_V ⋯` (one factor) of the projection. -/
noncomputable def cechNerveZeroSection : f.left ⟶ f.cechNerve.obj (op ⦋0⦌) :=
  WidePullback.lift f.hom (fun _ => 𝟙 _) (fun _ => Category.id_comp _)

@[reassoc (attr := simp)]
lemma cechNerveZeroSection_base : f.cechNerveZeroSection ≫ f.cechNerveBase 0 = f.hom :=
  WidePullback.lift_base _ _ _ _

instance isIso_cechNerve_π_zero : IsIso (WidePullback.π (fun _ : Fin 1 => f.hom) 0) := by
  refine ⟨f.cechNerveZeroSection, ?_, WidePullback.lift_π _ _ _ _ 0⟩
  apply WidePullback.hom_ext
  · intro j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [Category.assoc, cechNerveZeroSection, WidePullback.lift_π, Category.comp_id,
      Category.id_comp]
  · rw [Category.assoc, cechNerveZeroSection, WidePullback.lift_base, WidePullback.π_arrow,
      Category.id_comp]

variable {A : Type w} [Category.{w'} A]

section Preadditive

variable [Preadditive A]

lemma cechComplex_d_zero_one (P : Cᵒᵖ ⥤ A) :
    (f.cechComplex P).d 0 1 =
      P.map (f.cechNerve.δ 0).op - P.map (f.cechNerve.δ 1).op := by
  rw [cechComplex_d, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

@[reassoc (attr := simp)]
lemma map_cechNerveBase_comp_d (P : Cᵒᵖ ⥤ A) :
    P.map (f.cechNerveBase 0).op ≫ (f.cechComplex P).d 0 1 = 0 := by
  rw [cechComplex_d_zero_one, Preadditive.comp_sub, ← P.map_comp, ← P.map_comp, ← op_comp,
    ← op_comp]
  dsimp only [SimplicialObject.δ]
  rw [cechNerve_map_cechNerveBase, cechNerve_map_cechNerveBase, sub_self]

variable {J : GrothendieckTopology C}
  (hf : Sieve.generate (Presieve.singleton f.hom) ∈ J f.right)
include hf

lemma ofArrows_cechNerveBase_mem :
    Sieve.ofArrows (fun _ : Unit => f.cechNerve.obj (op ⦋0⦌)) (fun _ => f.cechNerveBase 0) ∈
      J f.right := by
  refine J.superset_covering ?_ hf
  rintro Z _ ⟨Y, a, _, ⟨⟩, rfl⟩
  rw [← cechNerveZeroSection_base, ← Category.assoc]
  exact Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ ()) _

variable {f}

/-- Sections of a sheaf over the target of a covering morphism inject into the sections over
the first object of its Čech nerve. -/
lemma hom_ext_cechNerveBase {P : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P) {T : A}
    {x y : T ⟶ P.obj (op f.right)}
    (h : x ≫ P.map (f.cechNerveBase 0).op = y ≫ P.map (f.cechNerveBase 0).op) : x = y :=
  hP.hom_ext_ofArrows _ (f.ofArrows_cechNerveBase_mem hf) fun _ ↦ h

/-- A Čech `0`-cocycle of a sheaf along a covering morphism comes from a section over the
target. -/
lemma exists_comp_map_cechNerveBase {P : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P) {T : A}
    (x : T ⟶ P.obj (op (f.cechNerve.obj (op ⦋0⦌)))) (hx : x ≫ (f.cechComplex P).d 0 1 = 0) :
    ∃ y : T ⟶ P.obj (op f.right), y ≫ P.map (f.cechNerveBase 0).op = x := by
  have hx' : x ≫ P.map (f.cechNerve.δ 0).op = x ≫ P.map (f.cechNerve.δ 1).op := by
    rw [cechComplex_d_zero_one, Preadditive.comp_sub, sub_eq_zero] at hx
    exact hx
  obtain ⟨y, hy, -⟩ := hP.existsUnique_amalgamation_ofArrows _
    (f.ofArrows_cechNerveBase_mem hf) (fun _ ↦ x) fun W _ _ a b hab ↦ by
      -- the pair `(a, b)` defines a point of `U ×_V U`
      let l : W ⟶ f.cechNerve.obj (op ⦋1⦌) :=
        WidePullback.lift (a ≫ f.cechNerveBase 0)
          (Fin.cons (a ≫ WidePullback.π _ 0) (fun _ => b ≫ WidePullback.π _ 0))
          (by
            intro j
            refine Fin.cases ?_ (fun _ ↦ ?_) j
            · simp
            · simp [hab])
      have hl₀ : l ≫ f.cechNerve.δ 0 = b := by
        apply WidePullback.hom_ext
        · intro j
          obtain rfl : j = 0 := Subsingleton.elim _ _
          dsimp only [SimplicialObject.δ]
          rw [Category.assoc, cechNerve_map_π]
          exact WidePullback.lift_π _ _ _ _ _
        · dsimp only [SimplicialObject.δ]
          rw [Category.assoc, cechNerve_map_cechNerveBase]
          exact (WidePullback.lift_base _ _ _ _).trans hab
      have hl₁ : l ≫ f.cechNerve.δ 1 = a := by
        apply WidePullback.hom_ext
        · intro j
          obtain rfl : j = 0 := Subsingleton.elim _ _
          dsimp only [SimplicialObject.δ]
          rw [Category.assoc, cechNerve_map_π]
          exact WidePullback.lift_π _ _ _ _ _
        · dsimp only [SimplicialObject.δ]
          rw [Category.assoc, cechNerve_map_cechNerveBase]
          exact WidePullback.lift_base _ _ _ _
      rw [← hl₀, ← hl₁, op_comp, op_comp, P.map_comp, P.map_comp, ← Category.assoc,
        ← Category.assoc, hx']
  exact ⟨y, hy ()⟩

end Preadditive

section Abelian

variable [Abelian A] {J : GrothendieckTopology C}

omit [∀ n : ℕ, HasWidePullback.{0} f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom] in
/-- Sections over an object of a short exact sequence of sheaves form a left exact sequence. -/
lemma exact_and_mono_map_sections {S : ShortComplex (Sheaf J A)} (hS : S.ShortExact) (V : C) :
    (S.map (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op V))).Exact ∧
      Mono (S.f.hom.app (op V)) :=
  (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op V))).1 inferInstance S hS

lemma cechComplex_d_naturality {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) (n : ℕ) :
    φ.app (op (f.cechNerve.obj (op ⦋n⦌))) ≫ (f.cechComplex Q).d n (n + 1) =
      (f.cechComplex P).d n (n + 1) ≫ φ.app (op (f.cechNerve.obj (op ⦋n + 1⦌))) :=
  ((f.cechComplexFunctor.map φ).comm n (n + 1)).symm

variable {f}

/-- **Lifting sections along a covering.** Let `0 ⟶ G₁ ⟶ G₂ ⟶ G₃ ⟶ 0` be a short exact sequence
of sheaves and `f : U ⟶ V` a covering morphism. If `G₂(U) ⟶ G₃(U)` is an epimorphism and the
first Čech cohomology of `G₁` along `f` vanishes, then `G₂(V) ⟶ G₃(V)` is an epimorphism. -/
theorem epi_app_right_of_exactAt_cechComplex_one {S : ShortComplex (Sheaf J A)}
    (hS : S.ShortExact) (hf : Sieve.generate (Presieve.singleton f.hom) ∈ J f.right)
    (h₁ : (f.cechComplex S.X₁.obj).ExactAt 1) (h₀ : Epi (S.g.hom.app (op f.left))) :
    Epi (S.g.hom.app (op f.right)) := by
  -- the epimorphism on the first object of the Čech nerve, isomorphic to `U`
  have h₀' : Epi (S.g.hom.app (op (f.cechNerve.obj (op ⦋0⦌)))) := by
    have e := S.g.hom.naturality (WidePullback.π (fun _ : Fin 1 => f.hom) 0).op
    have : S.g.hom.app (op (f.cechNerve.obj (op ⦋0⦌))) =
        inv (S.X₂.obj.map (WidePullback.π (fun _ : Fin 1 => f.hom) 0).op) ≫
          S.g.hom.app (op f.left) ≫
            S.X₃.obj.map (WidePullback.π (fun _ : Fin 1 => f.hom) 0).op := by
      rw [← e, IsIso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)] at h₁
  obtain ⟨hE₁, _⟩ := exact_and_mono_map_sections hS (f.cechNerve.obj (op ⦋1⦌))
  obtain ⟨-, _⟩ := exact_and_mono_map_sections hS (f.cechNerve.obj (op ⦋2⦌))
  obtain ⟨-, _⟩ := exact_and_mono_map_sections hS (f.cechNerve.obj (op ⦋0⦌))
  rw [epi_iff_surjective_up_to_refinements]
  intro T s
  obtain ⟨T₁, π₁, _, t, ht⟩ := (epi_iff_surjective_up_to_refinements _).1 h₀'
    (s ≫ S.X₃.obj.map (f.cechNerveBase 0).op)
  -- the Čech differential of the lift `t` comes from a cocycle `u` of `G₁`
  have hu : (t ≫ (f.cechComplex S.X₂.obj).d 0 1) ≫ S.g.hom.app (op (f.cechNerve.obj (op ⦋1⦌)))
      = 0 := by
    rw [Category.assoc, ← cechComplex_d_naturality, ← Category.assoc, ← ht, Category.assoc,
      Category.assoc, map_cechNerveBase_comp_d, comp_zero, comp_zero]
  let u := hE₁.lift _ hu
  have hu' : u ≫ S.f.hom.app (op (f.cechNerve.obj (op ⦋1⦌))) =
      t ≫ (f.cechComplex S.X₂.obj).d 0 1 := hE₁.lift_f _ hu
  have hcoc : u ≫ (f.cechComplex S.X₁.obj).d 1 2 = 0 := by
    rw [← cancel_mono (S.f.hom.app (op (f.cechNerve.obj (op ⦋2⦌)))), zero_comp,
      Category.assoc, cechComplex_d_naturality, ← Category.assoc, hu', Category.assoc,
      HomologicalComplex.d_comp_d, comp_zero]
  obtain ⟨T₂, π₂, _, v, hv⟩ := h₁.exact_up_to_refinements u hcoc
  change π₂ ≫ u = v ≫ (f.cechComplex S.X₁.obj).d 0 1 at hv
  -- the corrected lift is a Čech `0`-cocycle of `G₂`, hence a section over `V`
  let t' := π₂ ≫ t - v ≫ S.f.hom.app (op (f.cechNerve.obj (op ⦋0⦌)))
  have ht' : t' ≫ (f.cechComplex S.X₂.obj).d 0 1 = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, ← cechComplex_d_naturality,
      ← hu', ← Category.assoc, ← Category.assoc, hv, sub_self]
  obtain ⟨z, hz⟩ := exists_comp_map_cechNerveBase hf S.X₂.property t' ht'
  refine ⟨T₂, π₂ ≫ π₁, inferInstance, z, ?_⟩
  refine hom_ext_cechNerveBase hf S.X₃.property ?_
  rw [Category.assoc, Category.assoc, Category.assoc, ← S.g.hom.naturality, ← Category.assoc z,
    hz, Preadditive.sub_comp, Category.assoc, ← ht, Category.assoc,
    ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, S.zero]
  simp

/-- **Čech complexes of a short exact sequence.** Let `0 ⟶ G₁ ⟶ G₂ ⟶ G₃ ⟶ 0` be a short exact
sequence of sheaves such that `G₂ ⟶ G₃` is an epimorphism on sections over all the objects of
the Čech nerve of `f`. If the Čech complexes of `G₁` and `G₂` along `f` are exact in positive
degrees, then so is the Čech complex of `G₃`. -/
theorem exactAt_cechComplex_X₃ {S : ShortComplex (Sheaf J A)} (hS : S.ShortExact)
    (hepi : ∀ n : ℕ, Epi (S.g.hom.app (op (f.cechNerve.obj (op ⦋n⦌)))))
    (h₁ : ∀ n : ℕ, (f.cechComplex S.X₁.obj).ExactAt (n + 1))
    (h₂ : ∀ n : ℕ, (f.cechComplex S.X₂.obj).ExactAt (n + 1)) (n : ℕ) :
    (f.cechComplex S.X₃.obj).ExactAt (n + 1) := by
  let T := S.map (sheafToPresheaf J A ⋙ f.cechComplexFunctor)
  have hT : T.ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun k ↦ ?_
    obtain ⟨hE, hm⟩ := exact_and_mono_map_sections hS (f.cechNerve.obj (op ⦋k⦌))
    have := hepi k
    exact { exact := hE, mono_f := hm, epi_g := this }
  have h := hT.homology_exact₃ (n + 1) (n + 2) (by simp)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine h.isZero_X₂ ?_ ?_
  · exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₂ n)).eq_of_src _ _
  · exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₁ (n + 1))).eq_of_tgt _ _

end Abelian

end Arrow

end CategoryTheory
