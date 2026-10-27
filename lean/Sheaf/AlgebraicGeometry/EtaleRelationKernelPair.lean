/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Over
import Sheaf.AlgebraicGeometry.FppfUniversalUnitLocallyInjective
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Kernel pair of the fppf quotient of an equivalence relation

Source: Stacks Project, Groupoids, Tag 045Y and the preceding quotient-sheaf definition,
with the monomorphism hypothesis (blueprint: lem-trf-etale-relation-kernel-pair).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem quotient_eq_relation {S : Scheme.{u}} {R U : Over S}
    (s t : R ⟶ U)
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    (T : Over S) (a b : T ⟶ U)
    (h : (coequalizer.π (yoneda.map s) (yoneda.map t)).app (Opposite.op T) a =
      (coequalizer.π (yoneda.map s) (yoneda.map t)).app (Opposite.op T) b) :
    ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b := by
  let E := (CategoryTheory.evaluation (Over S)ᵒᵖ (Type u)).obj (Opposite.op T)
  let q : (T ⟶ U) ⟶ Quotient (⟨_, hrel T⟩ : Setoid (T ⟶ U)) := ↾Quotient.mk _
  have hq : (yoneda.map s).app (Opposite.op T) ≫ q = (yoneda.map t).app (Opposite.op T) ≫ q := by
    ext r
    exact Quotient.sound ⟨r, rfl, rfl⟩
  let hc := isColimitCoforkMapOfIsColimit E (coequalizer.condition _ _) (coequalizerIsCoequalizer
    (yoneda.map s) (yoneda.map t))
  let l := hc.desc (Cofork.ofπ q hq)
  have hl : (coequalizer.π (yoneda.map s) (yoneda.map t)).app (Opposite.op T) ≫ l = q :=
    hc.fac _ WalkingParallelPair.one
  apply Quotient.exact (s := (⟨_, hrel T⟩ : Setoid (T ⟶ U)))
  have hh := congrArg (fun z ↦ l z) h
  change q a = q b
  change ((coequalizer.π (yoneda.map s) (yoneda.map t)).app (Opposite.op T) ≫ l) a =
    ((coequalizer.π (yoneda.map s) (yoneda.map t)).app (Opposite.op T) ≫ l) b at hh
  rwa [hl] at hh

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem relation_jointly_injective {S : Scheme.{u}} {R U T : Over S}
    (s t : R ⟶ U) [Mono (prod.lift s t)] (a b : T ⟶ R)
    (hs : a ≫ s = b ≫ s) (ht : a ≫ t = b ≫ t) : a = b := by
  apply (cancel_mono (prod.lift s t)).mp
  apply prod.hom_ext <;> simpa only [Category.assoc, prod.lift_fst, prod.lift_snd]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem relation_of_local {S : Scheme.{u}} {R U T : Over S}
    (s t : R ⟶ U) [Mono (prod.lift s t)] (a b : T ⟶ U)
    (Z : Sieve T) (hZ : Z ∈ (fppfTopology.over S) T)
    (h : ∀ (V : Over S) (f : V ⟶ T), Z f →
      ∃ r : V ⟶ R, r ≫ s = f ≫ a ∧ r ≫ t = f ≫ b) :
    ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b := by
  classical
  let x : Presieve.FamilyOfElements (yoneda.obj R) Z.arrows :=
    fun V f hf ↦ (h V f hf).choose
  have hx (V : Over S) (f : V ⟶ T) (hf : Z f) :
      x f hf ≫ s = f ≫ a ∧ x f hf ≫ t = f ≫ b := (h V f hf).choose_spec
  have hc : x.Compatible := by
    intro V W Y g k f l hf hl he
    apply relation_jointly_injective s t
    · change (g ≫ x f hf) ≫ s = (k ≫ x l hl) ≫ s
      rw [Category.assoc, Category.assoc, (hx _ _ hf).1, (hx _ _ hl).1,
        ← Category.assoc, ← Category.assoc, he]
    · change (g ≫ x f hf) ≫ t = (k ≫ x l hl) ≫ t
      rw [Category.assoc, Category.assoc, (hx _ _ hf).2, (hx _ _ hl).2,
        ← Category.assoc, ← Category.assoc, he]
  have hR := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := fppfTopology.over S) (yoneda.obj R)
  have hU := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := fppfTopology.over S) (yoneda.obj U)
  obtain ⟨r, hr, _⟩ := hR Z hZ x hc
  refine ⟨r, ?_, ?_⟩
  · apply (hU Z hZ).isSeparatedFor.ext
    intro V f hf
    change f ≫ r ≫ s = f ≫ a
    have hh : f ≫ r = x f hf := hr f hf
    rw [← Category.assoc, hh, (hx _ _ hf).1]
  · apply (hU Z hZ).isSeparatedFor.ext
    intro V f hf
    change f ≫ r ≫ t = f ≫ b
    have hh : f ≫ r = x f hf := hr f hf
    rw [← Category.assoc, hh, (hx _ _ hf).2]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A monomorphic equivalence relation is the kernel pair of its fppf sheaf quotient.
The presheaf coequalizer is the pointwise quotient. The pair `F, η`, with `hη`, specifies
its sheafification by the universal property of `presheafToSheaf`, without requiring
sheafification for every small-valued presheaf on the big site. The pullback assertion
says precisely that the canonical relation-to-kernel-pair map is an isomorphism: the
representables are fppf sheaves, and their pullback is computed in presheaves.
Source: Stacks Project, Groupoids, Tag 045Y and the preceding quotient-sheaf definition
(blueprint: lem-trf-etale-relation-kernel-pair).

Proof:
1. The standard large-valued sheafification of a small-valued presheaf has small
   sections on this site. Encode a section by all its representatives on a small
   model of the affine schemes locally of finite type over the test scheme. Local
   surjectivity, affine refinement of fppf covers, and separatedness make this
   encoding injective. The smallness of that affine category is Mathlib's
   `essentiallySmall_costructuredArrow_Spec`.
2. Shrink the standard sheafification and factor its unit through `η` by `hη`.
   Local injectivity of the standard unit then implies local injectivity of `η`.
   This supplies the universe bridge needed for the given small-valued universal
   property without assuming small-valued sheafification on an arbitrary big site.
3. Evaluate the presheaf coequalizer at a test scheme and map it into the quotient
   set by `hrel`. Exactness of the setoid quotient turns equality of coequalizer
   classes into a single relation witness. Step 2 therefore supplies such witnesses
   locally whenever two sections have equal images in `F` (Stacks Tag 045Y).
4. Monicity of `(s,t)` makes the witnesses unique. The representable fppf sheaf
   glues them, and separatedness verifies both projections. Thus the square is a
   pullback on each test scheme, hence a pullback of presheaves. -/
theorem etale_relation_kernel_pair {S : Scheme.{u}} {R U : Over S} (s t : R ⟶ U)
    [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g)) :
    IsPullback (yoneda.map s) (yoneda.map t)
      (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η)
      (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) := by
  classical
  let π := coequalizer.π (yoneda.map s) (yoneda.map t)
  have hlocal := fppf_universal_unit_locally_injective _ F η hη
  have hw : yoneda.map s ≫ π ≫ η = yoneda.map t ≫ π ≫ η :=
    coequalizer.condition_assoc _ _ η
  apply IsPullback.of_forall_isPullback_app
  intro T
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun f ↦ f.app T) hw
  · intro a b hab
    exact relation_jointly_injective s t a b hab.1 hab.2
  · intro a b hab
    have hz := Presheaf.equalizerSieve_mem (fppfTopology.over S) η
      (π.app T a) (π.app T b) hab
    apply relation_of_local s t a b _ hz
    intro V f hf
    apply quotient_eq_relation s t hrel V (f ≫ a) (f ≫ b)
    change (coequalizer (yoneda.map s) (yoneda.map t)).map f.op (π.app T a) =
      (coequalizer (yoneda.map s) (yoneda.map t)).map f.op (π.app T b) at hf
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply] at hf
    exact hf

end AlgebraicGeometry.Scheme
