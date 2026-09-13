/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Grothendieck
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallyInjective
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sieves
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Vanishing

/-!
# Tensoring presheaves of modules preserves locally bijective morphisms

Let `C` be a category equipped with a Grothendieck topology `J` and let `R : Cᵒᵖ ⥤ CommRingCat`
be a presheaf of commutative rings. The category `PresheafOfModules (R ⋙ forget₂ _ _)` is
symmetric monoidal, the tensor product being computed sectionwise.

We show that tensoring by a fixed presheaf of modules `M` preserves local surjectivity and local
bijectivity of morphisms, and deduce that the class `J.W` of morphisms of presheaves of abelian
groups which become isomorphisms after sheafification pulls back to a monoidal class of morphisms
of presheaves of modules. This is the hypothesis needed to transport the monoidal structure along
the sheafification functor `PresheafOfModules.sheafification`, which is a localization functor for
that class.

## Main results

- `PresheafOfModules.isLocallySurjective_whiskerLeft` and
  `PresheafOfModules.isLocallySurjective_whiskerRight`: tensoring a locally surjective morphism
  by a fixed presheaf of modules gives a locally surjective morphism.
- `PresheafOfModules.isLocallyInjective_whiskerLeft` and
  `PresheafOfModules.isLocallyInjective_whiskerRight`: tensoring a locally bijective morphism by
  a fixed presheaf of modules gives a locally injective morphism.
- `PresheafOfModules.inverseImage_W_toPresheaf_isMonoidal`: the class
  `J.W.inverseImage (toPresheaf (R ⋙ forget₂ _ _))` is monoidal.
- `PresheafOfModules.isIso_sheafification_map_iff`: a morphism of presheaves of modules becomes
  an isomorphism after sheafification if and only if it is locally bijective.

Note that, unlike the case of sheaves with values in a fixed monoidal category
(`Mathlib/CategoryTheory/Sites/Monoidal.lean`), no monoidal closedness is used: there is no
internal hom of presheaves of modules, and the proofs below are elementary.

-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

universe v₁ u₁ u

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {R : Cᵒᵖ ⥤ CommRingCat.{u}} (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
  {N₁ N₂ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (f : N₁ ⟶ N₂)

/-- Tensoring on the left by a fixed presheaf of modules preserves local surjectivity. -/
instance isLocallySurjective_whiskerLeft [IsLocallySurjective J f] :
    IsLocallySurjective J (M ◁ f) where
  imageSieve_mem {U} s := by
    obtain ⟨s, rfl⟩ : ∃ t : TensorProduct (R.obj (op U)) (M.obj (op U)) (N₂.obj (op U)),
        t = s := ⟨s, rfl⟩
    -- the sections which lift locally form a submodule, and `s` is a sum of pure tensors
    refine (mem_localImage J (M ◁ f) s).1 ?_
    have hs : s ∈ Submodule.span (R.obj (op U))
        {t : TensorProduct (R.obj (op U)) (M.obj (op U)) (N₂.obj (op U)) |
          ∃ m n, m ⊗ₜ[R.obj (op U)] n = t} := by
      rw [TensorProduct.span_tmul_eq_top]
      trivial
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, n, rfl⟩ := hx
      refine J.superset_covering (fun V g hg ↦ ?_)
        (Presheaf.imageSieve_mem J ((toPresheaf (R ⋙ forget₂ _ _)).map f) n)
      obtain ⟨t, ht⟩ : ∃ t : N₁.obj (op V), f.app (op V) t = N₂.map g.op n := hg
      exact ⟨M.map g.op m ⊗ₜ[R.obj (op V)] t, congrArg (M.map g.op m ⊗ₜ[R.obj (op V)] ·) ht⟩
    | zero => exact zero_mem _
    | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | smul r _ _ h => exact Submodule.smul_mem _ r h

/-- Tensoring on the right by a fixed presheaf of modules preserves local surjectivity. -/
instance isLocallySurjective_whiskerRight [IsLocallySurjective J f] :
    IsLocallySurjective J (f ▷ M) := by
  have : Presheaf.IsLocallySurjective J ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map
      ((β_ N₁ M).hom ≫ M ◁ f ≫ (β_ N₂ M).inv)) := by
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  rwa [whiskerRight_eq_braiding_conj]

section

variable [IsLocallyInjective J f] [IsLocallySurjective J f]

/-- If `f` is locally bijective, a section `∑ᵢ mᵢ ⊗ nᵢ` of `M ⊗ N₁` which is killed by `M ◁ f`
vanishes locally. -/
lemma equalizerSieve_mem_of_eq_sum_tmul {X : Cᵒᵖ} {ι : Type*} [Fintype ι] (m : ι → M.obj X)
    (n : ι → N₁.obj X) (t : (M ⊗ N₁).obj X) (hts : t = ∑ i, m i ⊗ₜ[R.obj X] n i)
    (ht : (M ◁ f).app X t = 0) :
    Presheaf.equalizerSieve (F := (toPresheaf (R ⋙ forget₂ _ _)).obj (M ⊗ N₁)) t 0
      ∈ J X.unop := by
  subst hts
  have hmn : ∑ i, m i ⊗ₜ[R.obj X] f.app X (n i) = 0 :=
    (map_sum (((M ◁ f).app X).hom) _ _).symm.trans ht
  -- the vanishing of `∑ᵢ mᵢ ⊗ f(nᵢ)` is trivialized by a matrix `a` and elements `yⱼ` of `N₂`,
  -- after adjoining auxiliary elements `m'` of `M`
  obtain ⟨l, m', k, a, y, h₁, h₂⟩ :=
    TensorProduct.exists_vanishesTrivially_sum_elim_of_sum_tmul_eq_zero (R.obj X)
      (m := m) (n := fun i ↦ f.app X (n i)) hmn
  -- first refine so that all the `yⱼ` lift along `f`
  refine J.transitive (J.iInf_mem
    (fun j ↦ Presheaf.imageSieve ((toPresheaf (R ⋙ forget₂ _ _)).map f) (y j))
    (fun j ↦ Presheaf.imageSieve_mem J _ _)) _ (fun V g hg ↦ ?_)
  rw [Sieve.iInf_apply] at hg
  have hg' : ∀ j : Fin k, ∃ u : N₁.obj (op V), f.app (op V) u = N₂.map g.op (y j) := hg
  choose w hw using hg'
  -- after applying `f`, the relations `nᵢ = ∑ⱼ aᵢⱼ wⱼ` hold over `V`
  have key : ∀ p : ι ⊕ Fin l,
      f.app (op V) (Sum.elim (fun i ↦ (N₁.map g.op (n i) : N₁.obj (op V))) 0 p) =
        f.app (op V) (∑ j, R.map g.op (a p j) • w j) := by
    intro p
    have hL : f.app (op V) (Sum.elim (fun i ↦ (N₁.map g.op (n i) : N₁.obj (op V))) 0 p) =
        N₂.map g.op (Sum.elim (fun i ↦ f.app X (n i)) 0 p) := by
      cases p with
      | inl i => exact naturality_apply f g.op (n i)
      | inr i =>
        exact (map_zero ((f.app (op V)).hom)).trans (map_zero ((N₂.map g.op).hom)).symm
    have hR : f.app (op V) (∑ j, R.map g.op (a p j) • w j)
        = N₂.map g.op (∑ j, a p j • y j) := by
      rw [map_sum ((f.app (op V)).hom), map_sum ((N₂.map g.op).hom)]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, hw j, N₂.map_smul]; rfl
    rw [hL, hR, h₁ p]
  -- so by local injectivity of `f` the relations hold in `N₁` after a further refinement
  refine J.superset_covering (fun W h hD ↦ ?_) (J.iInf_mem
    (fun p : ι ⊕ Fin l ↦ Presheaf.equalizerSieve
      (F := (toPresheaf (R ⋙ forget₂ _ _)).obj N₁)
      (Sum.elim (fun i ↦ (N₁.map g.op (n i) : N₁.obj (op V))) 0 p)
      (∑ j, R.map g.op (a p j) • w j))
    (fun p ↦ Presheaf.equalizerSieve_mem J ((toPresheaf (R ⋙ forget₂ _ _)).map f) _ _ (key p)))
  rw [Sieve.iInf_apply] at hD
  -- the restricted relations trivialize the vanishing of the restriction of `∑ᵢ mᵢ ⊗ nᵢ`
  have hA : ∀ p, Sum.elim (fun i ↦ (N₁.map (h ≫ g).op (n i) : N₁.obj (op W))) 0 p
      = ∑ j, R.map (h ≫ g).op (a p j) • (N₁.map h.op (w j) : N₁.obj (op W)) := by
    intro p
    have e : Sum.elim (fun i ↦ (N₁.map (h ≫ g).op (n i) : N₁.obj (op W))) 0 p
        = N₁.map h.op (Sum.elim (fun i ↦ (N₁.map g.op (n i) : N₁.obj (op V))) 0 p) := by
      cases p with
      | inl i => rw [Sum.elim_inl, Sum.elim_inl, op_comp, N₁.map_comp_apply]
      | inr i => exact (map_zero ((N₁.map h.op).hom)).symm
    have hDp : N₁.map h.op (Sum.elim (fun i ↦ (N₁.map g.op (n i) : N₁.obj (op V))) 0 p)
        = N₁.map h.op (∑ j, R.map g.op (a p j) • w j) := hD p
    rw [e, hDp, map_sum ((N₁.map h.op).hom)]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [N₁.map_smul, op_comp, R.map_comp]; rfl
  have hB : ∀ j, ∑ p, R.map (h ≫ g).op (a p j) •
      Sum.elim (fun i ↦ (M.map (h ≫ g).op (m i) : M.obj (op W)))
        (fun i ↦ (M.map (h ≫ g).op (m' i) : M.obj (op W))) p = 0 := by
    intro j
    have e := congrArg (M.map (h ≫ g).op) (h₂ j)
    simp only [map_sum ((M.map (h ≫ g).op).hom), M.map_smul] at e
    refine Eq.trans (Finset.sum_congr rfl fun p _ ↦ ?_) (e.trans (map_zero _))
    cases p <;> rfl
  have hzero := TensorProduct.sum_tmul_eq_zero_of_vanishesTrivially (R.obj (op W))
    (m := Sum.elim (fun i ↦ (M.map (h ≫ g).op (m i) : M.obj (op W)))
      (fun i ↦ (M.map (h ≫ g).op (m' i) : M.obj (op W))))
    (n := Sum.elim (fun i ↦ (N₁.map (h ≫ g).op (n i) : N₁.obj (op W))) 0)
    ⟨k, fun p j ↦ R.map (h ≫ g).op (a p j), fun j ↦ (N₁.map h.op (w j) : N₁.obj (op W)), hA, hB⟩
  rw [Fintype.sum_sum_type] at hzero
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, TensorProduct.tmul_zero,
    Finset.sum_const_zero, add_zero] at hzero
  have final : (M ⊗ N₁).map (h ≫ g).op (∑ i, m i ⊗ₜ[R.obj X] n i)
      = (M ⊗ N₁).map (h ≫ g).op (0 : (M ⊗ N₁).obj X) := by
    rwa [map_zero (((M ⊗ N₁).map (h ≫ g).op).hom), map_sum (((M ⊗ N₁).map (h ≫ g).op).hom)]
  exact final

/-- Tensoring a locally bijective morphism on the left by a fixed presheaf of modules gives a
locally injective morphism. Local *bijectivity* of `f` is required, not just local injectivity:
the relations witnessing the vanishing of a section have to be lifted along `f`. This is why
this is not an instance. -/
lemma isLocallyInjective_whiskerLeft : IsLocallyInjective J (M ◁ f) :=
  Presheaf.isLocallyInjective_of_forall_equalizerSieve_zero J _ fun X t ht ↦ by
    obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := R.obj X) (t : (M ⊗ N₁).obj X)
    exact equalizerSieve_mem_of_eq_sum_tmul J M f (fun i : S ↦ (i.1.1 : M.obj X))
      (fun i : S ↦ (i.1.2 : N₁.obj X)) t
      (hS.trans (Finset.sum_coe_sort S (fun i ↦ (i.1 : M.obj X) ⊗ₜ[R.obj X] i.2)).symm) ht

/-- Tensoring a locally bijective morphism on the right by a fixed presheaf of modules gives a
locally injective morphism. As for `isLocallyInjective_whiskerLeft`, local bijectivity of `f`
is required. -/
lemma isLocallyInjective_whiskerRight : IsLocallyInjective J (f ▷ M) := by
  have := isLocallyInjective_whiskerLeft J M f
  have : Presheaf.IsLocallyInjective J ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map
      ((β_ N₁ M).hom ≫ M ◁ f ≫ (β_ N₂ M).inv)) := by
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  rwa [whiskerRight_eq_braiding_conj]

end

section

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

open MorphismProperty

/-- The class of morphisms of presheaves of modules which become isomorphisms after
sheafification is compatible with the monoidal structure. The `whiskerRight` half is deduced
from the `whiskerLeft` half through the braiding

```text
          f ▷ M
  N₁ ⊗ M ────────→ N₂ ⊗ M
     │                │
     │ β_ N₁ M        │ β_ N₂ M
     ↓                ↓
  M ⊗ N₁ ────────→ M ⊗ N₂
          M ◁ f
```
-/
instance inverseImage_W_toPresheaf_isMonoidal :
    (J.W.inverseImage (toPresheaf (R ⋙ forget₂ CommRingCat RingCat))).IsMonoidal :=
  .mk_of_braided _ fun M _ _ g hg ↦ by
    rw [inverseImage_iff] at hg ⊢
    have := hg.isLocallyInjective
    have := hg.isLocallySurjective
    have := isLocallyInjective_whiskerLeft J M g
    exact J.W_of_isLocallyBijective _

end

section

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {S : Sheaf J RingCat.{u}} (α : R₀ ⟶ S.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- A morphism of presheaves of modules becomes an isomorphism after sheafification if and only
if the underlying morphism of presheaves of abelian groups becomes an isomorphism after
sheafification. -/
theorem isIso_sheafification_map_iff {P Q : PresheafOfModules.{u} R₀} (φ : P ⟶ Q) :
    IsIso ((sheafification.{u} α).map φ) ↔ J.W ((toPresheaf R₀).map φ) := by
  have h : J.W.inverseImage (toPresheaf R₀) φ ↔
      (MorphismProperty.isomorphisms _).inverseImage (sheafification.{u} α) φ := by
    rw [inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms α]
  simpa only [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff] using h.symm

/-- A morphism of presheaves of modules whose underlying morphism of presheaves of abelian
groups becomes an isomorphism after sheafification induces an isomorphism of the
sheafifications. -/
theorem isIso_sheafification_map {P Q : PresheafOfModules.{u} R₀} (φ : P ⟶ Q)
    (hφ : J.W ((toPresheaf R₀).map φ)) : IsIso ((sheafification.{u} α).map φ) :=
  (isIso_sheafification_map_iff J α φ).2 hφ

end

end PresheafOfModules
