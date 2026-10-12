/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The sheaf of locally constant maps

For a topological space `X` and a type `R`, being locally constant is a local predicate on maps
`U → R` defined on open subsets `U` of `X`. We record the resulting sheaf of locally constant
maps, prove that its stalk at `x` is identified with `R` by evaluation at `x`, and that compatible
families of locally constant maps on an open cover glue.

## Main results

- `TopCat.isLocallyConstantLocal`: the local predicate "is locally constant".
- `TopCat.existsUnique_locallyConstant_germ_evaluation`: evaluation of germs at `x` is the unique
  map from the stalk to `R` sending `g_x` to `g x`, and it is bijective.
- `TopCat.locallyConstantMaps_gluing_exists`: gluing of locally constant maps.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat

variable (X : TopCat.{u}) (R : Type u)

/-- Being locally constant is a local predicate on maps from open subsets of `X` to `R`. -/
def isLocallyConstantLocal : LocalPredicate fun _ : X ↦ R where
  pred {_} f := IsLocallyConstant f
  res {_ _} i _ h := h.comp_continuous (Opens.isOpenEmbedding_of_le i.le).continuous
  locality {U} f w := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨V, hxV, i, hV⟩ := w x
    have he := Opens.isOpenEmbedding_of_le i.le
    have h := (IsLocallyConstant.iff_eventually_eq _).1 hV ⟨x.1, hxV⟩
    have hm := he.map_nhds_eq ⟨x.1, hxV⟩
    have hi : Set.inclusion i.le ⟨x.1, hxV⟩ = x := rfl
    rw [hi] at hm
    rw [← hm]
    exact Filter.eventually_map.2 h

/-- Let `x` be a point of `X`. Evaluation at `x` is the unique map from the stalk at `x` of the
sheaf of locally constant maps to `R` sending the germ `g_x` of a locally constant map `g` on an
open neighbourhood of `x` to `g x`, and this map is bijective.
(blueprint: `lem-weil-pbc-locally-constant-germ-evaluation`) -/
theorem existsUnique_locallyConstant_germ_evaluation (x : X) :
    ∃! ev : (subsheafToTypes (isLocallyConstantLocal X R)).presheaf.stalk x → R,
      (∀ (V : Opens X) (hx : x ∈ V)
        (g : (subsheafToTypes (isLocallyConstantLocal X R)).presheaf.obj (op V)),
          ev ((subsheafToTypes (isLocallyConstantLocal X R)).presheaf.germ V x hx g) =
            g.1 ⟨x, hx⟩) ∧ Function.Bijective ev := by
  refine ⟨stalkToFiber (isLocallyConstantLocal X R) x,
    ⟨fun V hx g ↦ stalkToFiber_germ _ V x hx g, ?_, ?_⟩, ?_⟩
  · apply stalkToFiber_injective
    intro U V fU hU fV hV hfx
    obtain ⟨A, hA, hxA, hA'⟩ := (IsLocallyConstant.iff_exists_open fU).1 hU ⟨x, U.2⟩
    obtain ⟨B, hB, hxB, hB'⟩ := (IsLocallyConstant.iff_exists_open fV).1 hV ⟨x, V.2⟩
    have hA₀ := (U.1.isOpenEmbedding).isOpenMap A hA
    have hB₀ := (V.1.isOpenEmbedding).isOpenMap B hB
    let W : Opens X := ⟨_, hA₀.inter hB₀⟩
    have hxW : x ∈ W := ⟨⟨_, hxA, rfl⟩, ⟨_, hxB, rfl⟩⟩
    have hWU : W ≤ U.1 := fun y hy ↦ by
      obtain ⟨z, -, rfl⟩ := hy.1
      exact z.2
    have hWV : W ≤ V.1 := fun y hy ↦ by
      obtain ⟨z, -, rfl⟩ := hy.2
      exact z.2
    refine ⟨⟨W, hxW⟩, homOfLE hWU, homOfLE hWV, fun w ↦ ?_⟩
    obtain ⟨⟨a, haA, ha⟩, ⟨b, hbB, hb⟩⟩ := w.2
    have e1 : (⟨w.1, hWU w.2⟩ : U.1) = a := Subtype.ext ha.symm
    have e2 : (⟨w.1, hWV w.2⟩ : V.1) = b := Subtype.ext hb.symm
    change fU ⟨w.1, hWU w.2⟩ = fV ⟨w.1, hWV w.2⟩
    rw [e1, e2, hA' a haA, hB' b hbB, hfx]
  · apply stalkToFiber_surjective
    intro r
    exact ⟨⟨⊤, Set.mem_univ x⟩, fun _ ↦ r, IsLocallyConstant.const r, rfl⟩
  · rintro ev ⟨hev, -⟩
    funext s
    obtain ⟨V, hx, g, rfl⟩ :=
      (subsheafToTypes (isLocallyConstantLocal X R)).presheaf.exists_germ_eq s
    rw [hev, stalkToFiber_germ]

/-- Let `(U i)` be a family of open subsets of `X` and `f i : U i → R` locally constant maps which
agree on the overlaps. Then there is a locally constant map on the union `⨆ i, U i` restricting
to `f i` on each `U i`. (blueprint: `lem-weil-pbc-locally-constant-maps-gluing-exists`) -/
theorem locallyConstantMaps_gluing_exists {ι : Type u} (U : ι → Opens X) (f : ∀ i, U i → R)
    (hf : ∀ i, IsLocallyConstant (f i))
    (hcompat : ∀ i j (y : X) (hi : y ∈ U i) (hj : y ∈ U j), f i ⟨y, hi⟩ = f j ⟨y, hj⟩) :
    ∃ g : (⨆ i, U i : Opens X) → R, IsLocallyConstant g ∧
      ∀ i (y : X) (hy : y ∈ U i), g ⟨y, Opens.mem_iSup.2 ⟨i, hy⟩⟩ = f i ⟨y, hy⟩ := by
  let F := subsheafToTypes (isLocallyConstantLocal X R)
  let sf : ∀ i, F.presheaf.obj (op (U i)) := fun i ↦ ⟨f i, hf i⟩
  obtain ⟨gl, hgl, -⟩ := F.existsUnique_gluing U sf (fun i j ↦ by
    apply Subtype.ext
    funext y
    exact hcompat i j y.1 _ _)
  refine ⟨gl.1, gl.2, fun i y hy ↦ ?_⟩
  have := congrArg (fun s : F.presheaf.obj (op (U i)) ↦ s.1 ⟨y, hy⟩) (hgl i)
  exact this

end TopCat
