/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.CategoryTheory.SmallSiteModuleSubsheafCodes
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Small families of actual image subsheaves

Source: blueprint main-20261015, integral-heart triangulated proof, paragraph (2),
final sentence; Stacks Project, Tag 03DA, sectionwise kernels
(blueprint: lem-sfb-small-site-image-subsheaf-representatives).
-/

@[expose] public section

universe u

open CategoryTheory

namespace SheafOfModules

/-- Submodule carriers uniquely determine the code's recovered submodule. -/
private theorem code_submodule_eq
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {P : ringedSiteModules.{u} R}
    (s : ModuleSubsheafCode P) (N : P.val.Submodule)
    (h : ∀ X, (N.obj X : Set (P.val.obj X)) = s.val X) : s.submodule = N := by
  apply PresheafOfModules.Submodule.ext
  intro X
  exact SetLike.coe_injective (s.property.choose_spec.1 X |>.trans (h X).symm)

/-- Finite-limit preservation reduces sectionwise injectivity to Mathlib's presheaf lemma. -/
private theorem mono_sections
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M P : ringedSiteModules.{u} R} (m : M ⟶ P) [Mono m]
    (X : Cᵒᵖ) : Function.Injective (m.val.app X) := by
  have : Mono m.val := (forget R).map_mono m
  exact PresheafOfModules.injective_of_mono m.val X

/-- Construct the range presheaf explicitly and transport the sheaf axiom along its isomorphism. -/
private theorem range_factor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M P : ringedSiteModules.{u} R} (m : M ⟶ P) [Mono m] :
    ∃ s : ModuleSubsheafCode P,
      (∀ X : Cᵒᵖ, s.val X = Set.range (m.val.app X)) ∧
      ∃ e : M ≅ s.toSheaf, e.hom ≫ s.ι = m ∧
        ∀ (X : Cᵒᵖ) (x : M.val.obj X),
          ((e.hom.val.app X x).val : P.val.obj X) = m.val.app X x := by
  classical
  let N : P.val.Submodule :=
    { obj X := LinearMap.range (m.val.app X).hom
      map := by
        intro X Y f y hy
        rcases hy with ⟨x, rfl⟩
        exact ⟨M.val.map f x, PresheafOfModules.naturality_apply m.val f x⟩ }
  let e : M.val ≅ N.toPresheafOfModules :=
    PresheafOfModules.isoMk (fun X ↦
      (LinearEquiv.ofInjective (m.val.app X).hom (mono_sections m X)).toModuleIso) (by
        intro X Y f
        ext x
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply m.val f x)
  have hf : e.hom ≫ N.ι = m.val := by
    ext X x
    rfl
  have hN : Presheaf.IsSheaf J N.toPresheafOfModules.presheaf :=
    (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf R.obj).mapIso e)).1
      M.isSheaf
  let s : ModuleSubsheafCode P :=
    ⟨fun X ↦ Set.range (m.val.app X), N, (fun _ ↦ rfl), hN⟩
  have hs : s.submodule = N := code_submodule_eq s N (fun _ ↦ rfl)
  have he : ∃ e' : M.val ≅ s.submodule.toPresheafOfModules,
      e'.hom ≫ s.submodule.ι = m.val := by
    rw [hs]
    exact ⟨e, hf⟩
  obtain ⟨e', he'⟩ := he
  let eS : M ≅ s.toSheaf := (fullyFaithfulForget R).preimageIso e'
  have heS : eS.hom ≫ s.ι = m := by
    apply hom_ext
    exact he'
  refine ⟨s, (fun _ ↦ rfl), eS, heS, ?_⟩
  intro X x
  exact ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.val.app X) heS) x

/-- Actual subset codes classify subobjects over each specified module-sheaf target.

Source: blueprint main-20261015, integral-heart triangulated proof, paragraph (2),
final sentence; Stacks Project, Tag 03DA, sectionwise kernels
(blueprint: lem-sfb-small-site-image-subsheaf-representatives).

Proof plan (the seven steps of the node):
1. A code supplies the inherited section modules and restriction maps using
   `def-weil-sheaf-of-modules-category`. The sheaf axiom is its membership condition.
   Carriers determine submodules uniquely; cancellation of subset inclusions is pointwise.
2. For a monomorphism, the sectionwise kernel inclusion is zero by cancellation
   (Tag 03DA and `def-weil-sheaf-of-modules-category`). Hence its section maps are injective.
3. The sectionwise ranges are submodules, and naturality preserves them under restriction.
4. For a matching family in these ranges, lift uniquely to the source using injectivity.
   The lifts agree on overlaps and glue in the source, by
   `def-weil-pbc-sites-and-cohomology`. Their image glues the original family uniquely.
   This argument includes empty coverings.
5. Sending a section to its image in the range is a natural linear bijection. Its inverse
   is linear and natural by injectivity. Thus it is an isomorphism over the fixed target.
6. An isomorphism over the target preserves ranges; equal ranges give an isomorphism by
   composing the two isomorphisms of step 5. The range of an inclusion is its own subset.
7. By `def-weil-size-convention`, powersets and products over the small object set are
   small; so are their subsets and the dependent sum over the small target index set.
   This includes empty object and target index sets and zero targets. Only monomorphisms
   are asserted to have sectionwise image presheaves that are sheaves. -/
theorem smallSite_image_subsheaf_representatives
    {C : Type u} [Category.{u} C] (T : Precoverage C)
    (_hT : T.IsSiteForCoverings) (R : Sheaf T.toGrothendieck RingCat.{u})
    (I : Type u) (P : I → ringedSiteModules.{u} R) :
    (∀ j : I, Small.{u} (SectionSubsetFamily (P j)) ∧ Small.{u} (ModuleSubsheafCode (P j))) ∧
    Small.{u} (Σ j : I, ModuleSubsheafCode (P j)) ∧
    (∀ (j : I) (s : ModuleSubsheafCode (P j)),
      (∀ X : Cᵒᵖ, (s.submodule.obj X : Set ((P j).val.obj X)) = s.val X) ∧
      (∃! N : (P j).val.Submodule,
        (∀ X : Cᵒᵖ, (N.obj X : Set ((P j).val.obj X)) = s.val X) ∧
          Presheaf.IsSheaf T.toGrothendieck N.toPresheafOfModules.presheaf) ∧
      Mono s.ι ∧
      (∀ X : Cᵒᵖ, Set.range (s.ι.val.app X) = s.val X)) ∧
    (∀ (j : I) (M : ringedSiteModules.{u} R) (m : M ⟶ P j), Mono m →
      (∀ X : Cᵒᵖ, Function.Injective (m.val.app X)) ∧
      ∃ s : ModuleSubsheafCode (P j),
        (∀ X : Cᵒᵖ, s.val X = Set.range (m.val.app X)) ∧
        ∃ e : M ≅ s.toSheaf, e.hom ≫ s.ι = m ∧
          ∀ (X : Cᵒᵖ) (x : M.val.obj X),
            ((e.hom.val.app X x).val : (P j).val.obj X) = m.val.app X x) ∧
    (∀ (j : I) (M M' : ringedSiteModules.{u} R) (m : M ⟶ P j) (m' : M' ⟶ P j),
      Mono m → Mono m' →
      ((∃ e : M ≅ M', e.hom ≫ m' = m) ↔
        ∀ X : Cᵒᵖ, Set.range (m.val.app X) = Set.range (m'.val.app X))) := by
  classical
  refine ⟨(fun _ ↦ ⟨inferInstance, inferInstance⟩), inferInstance, ?_, ?_, ?_⟩
  · intro j s
    refine ⟨s.property.choose_spec.1, ?_, ?_, ?_⟩
    · refine ⟨s.submodule, s.property.choose_spec, ?_⟩
      intro N hN
      exact (code_submodule_eq s N hN.1).symm
    · exact (forget R).mono_of_mono_map (by
        change Mono s.submodule.ι
        infer_instance)
    · intro X
      rw [← s.property.choose_spec.1 X]
      exact Subtype.range_coe
  · intro j M m hm
    have : Mono m := hm
    exact ⟨mono_sections m, range_factor m⟩
  · intro j M M' m m' hm hm'
    have : Mono m := hm
    have : Mono m' := hm'
    constructor
    · rintro ⟨e, he⟩ X
      have heX (x : M.val.obj X) :
          m'.val.app X (e.hom.val.app X x) = m.val.app X x :=
        ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app X) he) x
      apply Set.Subset.antisymm
      · rintro y ⟨x, rfl⟩
        exact ⟨e.hom.val.app X x, heX x⟩
      · rintro y ⟨x, rfl⟩
        refine ⟨e.inv.val.app X x, ?_⟩
        rw [← heX]
        have h := ConcreteCategory.congr_hom
          (congrArg (fun f ↦ f.val.app X) e.inv_hom_id) x
        change e.hom.val.app X (e.inv.val.app X x) = x at h
        rw [h]
    · intro hr
      obtain ⟨s, hs, e, he, _⟩ := range_factor m
      obtain ⟨s', hs', e', he', _⟩ := range_factor m'
      have hss : s = s' := by
        apply Subtype.ext
        funext X
        exact (hs X).trans ((hr X).trans (hs' X).symm)
      subst s'
      refine ⟨e ≪≫ e'.symm, ?_⟩
      simp only [Iso.trans_hom, Iso.symm_hom]
      rw [← he', Category.assoc, Iso.inv_hom_id_assoc, he]

end SheafOfModules
