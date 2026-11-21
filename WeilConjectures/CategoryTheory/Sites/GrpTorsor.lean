/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# Torsors under a sheaf of groups

Let `G` be a sheaf of (not necessarily abelian) groups on a site `(C, J)`. A `G`-torsor
(Stacks 03AH) is a sheaf of sets `T` with a left action of `G` which is simply transitive on
the sections over every object and such that `T` has sections locally. For sheaves of abelian
groups, see `CategoryTheory.Sheaf.Torsor`.

## Main definitions

- `CategoryTheory.Sheaf.GrpTorsor`: a torsor under a sheaf of groups.
- `CategoryTheory.Sheaf.GrpTorsor.isoOfSection`: a section `t` of a torsor over `x`
  identifies the underlying presheaf of sets of `G` with `T` over every family of objects
  mapping compatibly to `x`, via `g ↦ g • t`.
-/

@[expose] public section

universe w v u v' u'

open Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Stacks 03AH.** A *torsor* under a sheaf `G` of groups: a sheaf of sets `T` with a left
action `G × T → T` of `G`, compatible with restrictions, which is simply transitive on the
sections over every object, and such that `T` has sections locally, i.e. every object is
covered by objects over which `T` has a section. -/
structure GrpTorsor (G : Sheaf J GrpCat.{w}) where
  /-- The underlying sheaf of sets. -/
  sheaf : Sheaf J (Type w)
  /-- The action of `G` on `T`. -/
  smul (U : Cᵒᵖ) : G.obj.obj U → sheaf.obj.obj U → sheaf.obj.obj U
  one_smul (U : Cᵒᵖ) (t : sheaf.obj.obj U) : smul U 1 t = t
  mul_smul (U : Cᵒᵖ) (g h : G.obj.obj U) (t : sheaf.obj.obj U) :
    smul U (g * h) t = smul U g (smul U h t)
  map_smul {U V : Cᵒᵖ} (f : U ⟶ V) (g : G.obj.obj U) (t : sheaf.obj.obj U) :
    sheaf.obj.map f (smul U g t) = smul V (G.obj.map f g) (sheaf.obj.map f t)
  /-- The action is simply transitive on the sections over every object. -/
  bijective_smul (U : Cᵒᵖ) (t : sheaf.obj.obj U) : Function.Bijective (smul U · t)
  /-- The torsor has sections locally. -/
  nonemptySieve_mem (U : C) : nonemptySieve sheaf.obj U ∈ J U

namespace GrpTorsor

variable {G : Sheaf J GrpCat.{w}} (T : GrpTorsor G)

/-- A section `t` of a `G`-torsor `T` over `x` identifies the underlying presheaf of sets of
`G` with `T` along any functor `Φ : D ⥤ C` equipped with compatible maps `Φ d ⟶ x`, by
`g ↦ g • t|_{Φ d}`. -/
noncomputable def isoOfSection {D : Type u'} [Category.{v'} D] (Φ : D ⥤ C) {x : C}
    (π : Φ ⟶ (Functor.const D).obj x) (t : T.sheaf.obj.obj (op x)) :
    Φ.op ⋙ G.obj ⋙ forget GrpCat ≅ Φ.op ⋙ T.sheaf.obj :=
  NatIso.ofComponents
    (fun d ↦ (Equiv.ofBijective _
      (T.bijective_smul (op (Φ.obj d.unop)) (T.sheaf.obj.map (π.app d.unop).op t))).toIso)
    (fun {d d'} f ↦ by
      ext g
      change T.smul _ _ _ = T.sheaf.obj.map _ (T.smul _ _ _)
      have h : Φ.map f.unop ≫ π.app d.unop = π.app d'.unop := by simp
      rw [T.map_smul]
      refine congrArg₂ _ rfl ?_
      change T.sheaf.obj.map (π.app d'.unop).op t =
        T.sheaf.obj.map (Φ.map f.unop).op (T.sheaf.obj.map (π.app d.unop).op t)
      rw [← h, op_comp, Functor.map_comp]
      rfl)

end GrpTorsor

end CategoryTheory.Sheaf
