/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sheaves of abelian groups of dependent functions

Let `X` be a topological space and let `A x` be an abelian group for every point `x : X`.
Suppose that for every open `U` we are given a subgroup `P U` of the dependent functions
`(x : U) → A x`, which is stable under restriction and satisfies the gluing condition: a
function on `⨆ i, U i` whose restrictions to all `U i` lie in `P (U i)` lies in `P (⨆ i, U i)`.
Then `U ↦ P U` is a sheaf of abelian groups on `X`.

## Main definitions

- `TopCat.SubgroupOfFunctions`: the data `P` above.
- `TopCat.SubgroupOfFunctions.sheaf`: the corresponding sheaf of abelian groups.
-/

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace Opposite

namespace TopCat

variable {X : TopCat.{u}} (A : X → Type v) [∀ x, AddCommGroup (A x)]

/-- A family of subgroups of the groups of dependent functions `(x : U) → A x` on the opens
`U` of `X`, stable under restriction and satisfying the gluing condition. -/
structure SubgroupOfFunctions where
  /-- The subgroup of functions on `U`. -/
  subgroup (U : Opens X) : AddSubgroup ((x : U) → A x)
  restrict_mem {U V : Opens X} (h : V ≤ U) {f : (x : U) → A x} :
    f ∈ subgroup U → (fun x : V ↦ f ⟨x, h x.2⟩) ∈ subgroup V
  mem_of_forall {ι : Type u} (U : ι → Opens X) (f : (x : (⨆ i, U i : Opens X)) → A x) :
    (∀ i, (fun x : U i ↦ f ⟨x, Opens.mem_iSup.2 ⟨i, x.2⟩⟩) ∈ subgroup (U i)) →
      f ∈ subgroup (⨆ i, U i)

namespace SubgroupOfFunctions

variable {A} (P : SubgroupOfFunctions A)

/-- Restriction of functions, as a group homomorphism between the subgroups of `P`. -/
def restrict {U V : Opens X} (h : V ≤ U) : P.subgroup U →+ P.subgroup V where
  toFun f := ⟨fun x ↦ f.1 ⟨x, h x.2⟩, P.restrict_mem h f.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma restrict_apply {U V : Opens X} (h : V ≤ U) (f : P.subgroup U) (x : V) :
    (P.restrict h f).1 x = f.1 ⟨x, h x.2⟩ :=
  rfl

/-- The presheaf of abelian groups `U ↦ P U`. -/
def presheaf : Presheaf AddCommGrpCat.{max u v} X where
  obj U := AddCommGrpCat.of (P.subgroup U.unop)
  map h := AddCommGrpCat.ofHom (P.restrict h.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
lemma presheaf_map_apply {U V : (Opens X)ᵒᵖ} (h : U ⟶ V) (f : P.subgroup U.unop) (x : V.unop) :
    (P.presheaf.map h f).1 x = f.1 ⟨x, h.unop.le x.2⟩ :=
  rfl

lemma isSheaf : P.presheaf.IsSheaf := by
  rw [Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  classical
  have hcompat (i j : ι) (x : X) (hi : x ∈ U i) (hj : x ∈ U j) :
      (sf i).1 ⟨x, hi⟩ = (sf j).1 ⟨x, hj⟩ := by
    have := congrArg (fun g : P.subgroup (U i ⊓ U j) ↦ g.1 ⟨x, ⟨hi, hj⟩⟩) (hsf i j)
    exact this
  let f : (x : (⨆ i, U i : Opens X)) → A x := fun x ↦
    (sf (Opens.mem_iSup.1 x.2).choose).1 ⟨x, (Opens.mem_iSup.1 x.2).choose_spec⟩
  have hf (i : ι) (x : X) (hx : x ∈ U i) :
      f ⟨x, Opens.mem_iSup.2 ⟨i, hx⟩⟩ = (sf i).1 ⟨x, hx⟩ :=
    hcompat _ _ _ _ _
  have hmem : f ∈ P.subgroup (⨆ i, U i) := P.mem_of_forall U f fun i ↦ by
    convert (sf i).2 using 1
    funext x
    exact hf i x.1 x.2
  refine ⟨⟨f, hmem⟩, fun i ↦ Subtype.ext (funext fun x ↦ hf i x.1 x.2), fun g hg ↦ ?_⟩
  refine Subtype.ext (funext fun x ↦ ?_)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
  have h1 := congrArg (fun g : P.subgroup (U i) ↦ g.1 ⟨x, hi⟩) (hg i)
  refine h1.trans (hf i x hi).symm

/-- The sheaf of abelian groups `U ↦ P U`. -/
def sheaf : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} :=
  ⟨P.presheaf, P.isSheaf⟩

@[simp]
lemma sheaf_obj_obj (U : (Opens X)ᵒᵖ) :
    P.sheaf.obj.obj U = AddCommGrpCat.of (P.subgroup U.unop) :=
  rfl

end SubgroupOfFunctions

end TopCat
