/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Grothendieck
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Vanishing

/-!
# Tensoring presheaves of modules preserves locally bijective morphisms

Let `C` be a category equipped with a Grothendieck topology `J` and let `R : Cᵒᵖ ⥤ CommRingCat`
be a presheaf of commutative rings. The category `PresheafOfModules (R ⋙ forget₂ _ _)` is
symmetric monoidal, the tensor product being computed sectionwise.

We show that whiskering by a fixed presheaf of modules `M` preserves local surjectivity and
local bijectivity of morphisms, and deduce that the class `J.W` of morphisms of presheaves of
abelian groups which become isomorphisms after sheafification pulls back to a monoidal class
of morphisms of presheaves of modules. This is the hypothesis needed to transport the monoidal
structure along the sheafification functor `PresheafOfModules.sheafification`, which is a
localization functor for that class (see
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean`).

## Main results

- `PresheafOfModules.isLocallySurjective_whiskerLeft`: if `f` is locally surjective, so is
  `M ◁ f`. A section of `M ⊗ N₂` is a finite sum of pure tensors `mᵢ ⊗ nᵢ`; on the
  intersection of the image sieves of the `nᵢ` it is in the image of `M ◁ f`.
- `PresheafOfModules.isLocallyInjective_whiskerLeft`: if `f` is locally bijective, then `M ◁ f`
  is locally injective. This uses the equational criterion for vanishing of an element of a
  tensor product (`TensorProduct.exists_vanishesTrivially_sum_elim_of_sum_tmul_eq_zero`): the
  relations trivializing the vanishing of the image can be lifted locally along `f`.
- `PresheafOfModules.W_inverseImage_toPresheaf_isMonoidal`: the class
  `J.W.inverseImage (toPresheaf (R ⋙ forget₂ _ _))` is monoidal.

Note that, unlike the case of sheaves with values in a fixed monoidal category
(`Mathlib/CategoryTheory/Sites/Monoidal.lean`), no monoidal closedness is used: there is no
internal hom of presheaves of modules, and the proofs below are elementary.

-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

universe v₁ u₁ u

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

section

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}}

/-- Membership in the image sieve of the underlying morphism of presheaves of abelian groups of
a morphism of presheaves of modules, expressed in terms of the modules of sections. -/
lemma imageSieve_toPresheaf_map_arrows {M N : PresheafOfModules.{u} R₀} (φ : M ⟶ N) {U : Cᵒᵖ}
    (s : N.obj U) {V : C} (g : V ⟶ U.unop) :
    (Presheaf.imageSieve ((toPresheaf R₀).map φ) s).arrows g ↔
      ∃ t : M.obj (op V), φ.app (op V) t = N.map g.op s := Iff.rfl

/-- Two sections have the same image under the underlying morphism of presheaves of abelian
groups of a morphism of presheaves of modules iff they have the same image under the morphism
itself. -/
lemma toPresheaf_map_app_eq_iff {M N : PresheafOfModules.{u} R₀} (φ : M ⟶ N) {X : Cᵒᵖ}
    (x y : M.obj X) :
    ((toPresheaf R₀).map φ).app X x = ((toPresheaf R₀).map φ).app X y ↔ φ.app X x = φ.app X y :=
  Iff.rfl

/-- Membership in the equalizer sieve of two sections of the underlying presheaf of abelian
groups of a presheaf of modules, expressed in terms of the modules of sections. -/
lemma equalizerSieve_toPresheaf_obj_arrows {M : PresheafOfModules.{u} R₀} {X : Cᵒᵖ}
    (x y : M.obj X) {V : C} (g : V ⟶ X.unop) :
    (Presheaf.equalizerSieve (F := (toPresheaf R₀).obj M) x y).arrows g ↔
      M.map g.op x = M.map g.op y := Iff.rfl

end

variable {R : Cᵒᵖ ⥤ CommRingCat.{u}} (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
  {N₁ N₂ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (f : N₁ ⟶ N₂)

/-- Whiskering a locally surjective morphism of presheaves of modules by a fixed presheaf of
modules gives a locally surjective morphism. -/
instance isLocallySurjective_whiskerLeft
    [Presheaf.IsLocallySurjective J ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f)] :
    Presheaf.IsLocallySurjective J
      ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map (M ◁ f)) where
  imageSieve_mem {U} s := by
    obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := R.obj (op U)) s
    -- refine by the intersection of the image sieves of the second components of `S`
    refine J.mem_of_forall_finite
      (fun p : {p // p ∈ S} ↦
        Presheaf.imageSieve ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f)
          (p.1.2 : N₂.obj (op U)))
      (fun p ↦ Presheaf.imageSieve_mem J _ _) (fun V g hg ↦ ?_)
    choose w hw using fun p : {p // p ∈ S} ↦
      (imageSieve_toPresheaf_map_arrows f (p.1.2 : N₂.obj (op U)) g).1 (hg p)
    refine (imageSieve_toPresheaf_map_arrows (M ◁ f) s g).2
      ⟨∑ p : {p // p ∈ S}, (M.map g.op p.1.1 : M.obj (op V)) ⊗ₜ[R.obj (op V)] w p, ?_⟩
    rw [hS, ← Finset.sum_coe_sort S (fun i ↦ (i.1 : M.obj (op U)) ⊗ₜ[R.obj (op U)] i.2)]
    refine (map_sum _ _ _).trans (Eq.trans ?_ (map_sum _ _ _).symm)
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    exact congrArg (fun y ↦ (M.map g.op p.1.1 : M.obj (op V)) ⊗ₜ[R.obj (op V)] y) (hw p)

section

variable [Presheaf.IsLocallyInjective J ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f)]
  [Presheaf.IsLocallySurjective J ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f)]

/-- If `f` is locally bijective, a section of `M ⊗ N₁` which is killed by `M ◁ f` vanishes
locally. -/
lemma equalizerSieve_mem_of_whiskerLeft_app_eq_zero {X : Cᵒᵖ} (t : (M ⊗ N₁).obj X)
    (ht : (M ◁ f).app X t = 0) :
    Presheaf.equalizerSieve
      (F := (toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj (M ⊗ N₁)) t 0 ∈ J X.unop := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := R.obj X) t
  have hsum : ∑ i : {p // p ∈ S}, (i.1.1 : M.obj X) ⊗ₜ[R.obj X] f.app X i.1.2 = 0 := by
    rw [Finset.sum_coe_sort S (fun i ↦ (i.1 : M.obj X) ⊗ₜ[R.obj X] f.app X i.2), ← ht, hS,
      map_sum ((M ◁ f).app X).hom]
    exact Finset.sum_congr rfl fun i _ ↦ rfl
  -- the vanishing of `∑ mᵢ ⊗ f(nᵢ)` is trivialized by a matrix `a` and elements `y j` of `N₂`,
  -- after adjoining auxiliary elements `m'` of `M`
  obtain ⟨l, m', k, a, y, h₁, h₂⟩ :=
    TensorProduct.exists_vanishesTrivially_sum_elim_of_sum_tmul_eq_zero (R.obj X)
      (m := fun i : {p // p ∈ S} ↦ (i.1.1 : M.obj X)) (n := fun i ↦ f.app X i.1.2) hsum
  -- first refine so that all the `y j` lift along `f`
  refine J.transitive (J.finsetInf_mem Finset.univ
    (fun j : Fin k ↦ Presheaf.imageSieve
      ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f) (y j))
    (fun j _ ↦ Presheaf.imageSieve_mem J _ _)) _ ?_
  intro V g hgS
  rw [GrothendieckTopology.finsetInf_apply] at hgS
  choose w hw using fun j : Fin k ↦
    (imageSieve_toPresheaf_map_arrows f (y j) g).1 (hgS j (Finset.mem_univ j))
  -- the relations `nᵢ = ∑ⱼ aᵢⱼ wⱼ` and `∑ⱼ a_{i'}ⱼ wⱼ = 0` hold after applying `f`
  have key : ∀ p : {p // p ∈ S} ⊕ Fin l,
      f.app (op V) (Sum.elim (fun i : {p // p ∈ S} ↦ N₁.map g.op i.1.2) 0 p) =
        f.app (op V) (∑ j, R.map g.op (a p j) • w j) := by
    intro p
    have hL : f.app (op V) (Sum.elim (fun i : {p // p ∈ S} ↦ N₁.map g.op i.1.2) 0 p) =
        N₂.map g.op (Sum.elim (fun i : {p // p ∈ S} ↦ f.app X i.1.2) 0 p) := by
      cases p with
      | inl i => exact naturality_apply f g.op i.1.2
      | inr i =>
        simp only [Sum.elim_inr, Pi.zero_apply, map_zero ((f.app (op V)).hom)]
        exact (map_zero ((N₂.map g.op).hom)).symm
    have hR : f.app (op V) (∑ j, R.map g.op (a p j) • w j)
        = N₂.map g.op (∑ j, a p j • y j) := by
      rw [map_sum ((f.app (op V)).hom), map_sum ((N₂.map g.op).hom)]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_smul, hw j, N₂.map_smul]
      rfl
    rw [hL, hR, h₁ p]
  -- so by local injectivity of `f` they hold after a further refinement
  refine J.mem_of_forall_finite
    (fun p : {p // p ∈ S} ⊕ Fin l ↦ Presheaf.equalizerSieve
      (F := (toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj N₁)
      (Sum.elim (fun i : {p // p ∈ S} ↦ N₁.map g.op i.1.2) 0 p)
      (∑ j, R.map g.op (a p j) • w j))
    (fun p ↦ Presheaf.equalizerSieve_mem J _ _ _
      ((toPresheaf_map_app_eq_iff f _ _).2 (key p))) ?_
  intro W h hD
  have hRc : ∀ r : R.obj X, (R ⋙ forget₂ CommRingCat RingCat).map h.op (R.map g.op r)
      = R.map (h ≫ g).op r := by
    intro r
    rw [op_comp, R.map_comp]
    rfl
  have hD' : ∀ p, N₁.map h.op (Sum.elim (fun i : {p // p ∈ S} ↦ N₁.map g.op i.1.2) 0 p)
      = N₁.map h.op (∑ j, R.map g.op (a p j) • w j) := fun p ↦
    (equalizerSieve_toPresheaf_obj_arrows _ _ h).1 (hD p)
  -- on this refinement, the restricted matrix trivializes the vanishing of the restriction of `t`
  have hA : ∀ p, Sum.elim (fun i : {p // p ∈ S} ↦ N₁.map (h ≫ g).op i.1.2) 0 p
      = ∑ j, R.map (h ≫ g).op (a p j) • N₁.map h.op (w j) := by
    intro p
    have e1 : Sum.elim (fun i : {p // p ∈ S} ↦ N₁.map (h ≫ g).op i.1.2) 0 p
        = N₁.map h.op (Sum.elim (fun i : {p // p ∈ S} ↦ N₁.map g.op i.1.2) 0 p) := by
      cases p with
      | inl i =>
        simp only [Sum.elim_inl]
        rw [op_comp, N₁.map_comp_apply]
      | inr i =>
        simp only [Sum.elim_inr, Pi.zero_apply]
        exact (map_zero ((N₁.map h.op).hom)).symm
    rw [e1, hD' p, map_sum ((N₁.map h.op).hom)]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [N₁.map_smul, hRc]
  have hB : ∀ j, ∑ p, R.map (h ≫ g).op (a p j) •
      Sum.elim (fun i : {p // p ∈ S} ↦ M.map (h ≫ g).op i.1.1)
        (fun i ↦ M.map (h ≫ g).op (m' i)) p = 0 := by
    intro j
    have e2 := congrArg (fun z : M.obj X ↦ M.map (h ≫ g).op z) (h₂ j)
    simp only [map_sum ((M.map (h ≫ g).op).hom), M.map_smul] at e2
    refine Eq.trans (Finset.sum_congr rfl fun p _ ↦ ?_) (e2.trans (map_zero _))
    cases p <;> rfl
  have hzero := TensorProduct.sum_tmul_eq_zero_of_vanishesTrivially (R.obj (op W))
    (m := Sum.elim (fun i : {p // p ∈ S} ↦ M.map (h ≫ g).op i.1.1)
      (fun i ↦ M.map (h ≫ g).op (m' i)))
    (n := Sum.elim (fun i : {p // p ∈ S} ↦ N₁.map (h ≫ g).op i.1.2) 0)
    ⟨k, fun p j ↦ R.map (h ≫ g).op (a p j), fun j ↦ N₁.map h.op (w j), hA, hB⟩
  rw [Fintype.sum_sum_type] at hzero
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, TensorProduct.tmul_zero,
    Finset.sum_const_zero, add_zero] at hzero
  refine (equalizerSieve_toPresheaf_obj_arrows t 0 (h ≫ g)).2 ?_
  rw [map_zero (((M ⊗ N₁).map (h ≫ g).op).hom), hS,
    map_sum (((M ⊗ N₁).map (h ≫ g).op).hom),
    ← Finset.sum_coe_sort S (fun i ↦ ((M ⊗ N₁).map (h ≫ g).op) (i.1 ⊗ₜ[R.obj X] i.2))]
  exact hzero

/-- Whiskering a locally bijective morphism of presheaves of modules by a fixed presheaf of
modules gives a locally injective morphism. -/
instance isLocallyInjective_whiskerLeft :
    Presheaf.IsLocallyInjective J
      ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map (M ◁ f)) where
  equalizerSieve_mem {X} x y hxy := by
    have ht : (M ◁ f).app X ((x - y : (M ⊗ N₁).obj X)) = 0 := by
      rw [map_sub ((M ◁ f).app X).hom, (toPresheaf_map_app_eq_iff (M ◁ f) x y).1 hxy, sub_self]
    refine J.superset_covering ?_
      (equalizerSieve_mem_of_whiskerLeft_app_eq_zero J M f (x - y : (M ⊗ N₁).obj X) ht)
    intro V g hg
    rw [equalizerSieve_toPresheaf_obj_arrows] at hg ⊢
    rw [map_sub (((M ⊗ N₁).map g.op).hom), map_zero (((M ⊗ N₁).map g.op).hom),
      sub_eq_zero] at hg
    exact hg

end

section

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

open MorphismProperty

/-- The class of morphisms of presheaves of modules which become isomorphisms after
sheafification is compatible with the monoidal structure. -/
instance W_inverseImage_toPresheaf_isMonoidal :
    (J.W.inverseImage (toPresheaf (R ⋙ forget₂ CommRingCat RingCat))).IsMonoidal where
  whiskerLeft M _ _ g hg := by
    rw [inverseImage_iff] at hg ⊢
    have := hg.isLocallyInjective
    have := hg.isLocallySurjective
    exact J.W_of_isLocallyBijective _
  whiskerRight {N₁ N₂} f hf M := by
    refine ((J.W.inverseImage (toPresheaf (R ⋙ forget₂ CommRingCat RingCat))).arrow_mk_iso_iff
      (Arrow.isoMk (β_ N₁ M) (β_ N₂ M))).2 ?_
    rw [inverseImage_iff] at hf ⊢
    have := hf.isLocallyInjective
    have := hf.isLocallySurjective
    exact J.W_of_isLocallyBijective _

end

end PresheafOfModules
