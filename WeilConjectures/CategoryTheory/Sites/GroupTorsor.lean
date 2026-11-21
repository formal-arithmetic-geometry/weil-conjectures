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

Let `G` be a sheaf of (not necessarily commutative) groups on a site `(C, J)`. A `G`-torsor is a
sheaf of sets `P` with a left action of `G` which is simply transitive on the sections over every
object and such that `P` has sections locally.

## Main definitions

- `CategoryTheory.Sheaf.GroupTorsor`: a torsor under a sheaf of groups.
- `CategoryTheory.Sheaf.GroupTorsor.isoOfSection`: a section `s` of `P` over `V` trivializes `P`
  over every object mapping to `V`, by `g ↦ g • s`.

## Implementation details

The commutative analogue, with additive notation, is `CategoryTheory.Sheaf.Torsor`.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory.Sheaf

open Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A *torsor* under a sheaf `G` of groups: a sheaf of sets `P` with a left action
`G × P → P` of `G` which is simply transitive on the sections over every object, and such
that `P` has sections locally, i.e. every object is covered by objects over which `P` has a
section. -/
structure GroupTorsor (G : Sheaf J GrpCat.{w}) where
  /-- The underlying sheaf of sets. -/
  sheaf : Sheaf J (Type w)
  /-- The action of `G` on `P`. -/
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

namespace GroupTorsor

variable {G : Sheaf J GrpCat.{w}} (P : GroupTorsor G)

/-- Let `s` be a section of a `G`-torsor `P` over `V`, and let `h` be a family of morphisms
`Φ d ⟶ V` natural in `d`. Then `g ↦ g • s|_{Φ d}` is an isomorphism between the restrictions
of the underlying sheaf of sets of `G` and of `P` along `Φ`. -/
noncomputable def isoOfSection {D : Type u'} [Category.{v'} D] (Φ : D ⥤ C) {V : C}
    (h : Φ ⟶ (Functor.const D).obj V) (s : P.sheaf.obj.obj (op V)) :
    Φ.op ⋙ G.obj ⋙ forget GrpCat.{w} ≅ Φ.op ⋙ P.sheaf.obj :=
  NatIso.ofComponents
    (fun d ↦ (Equiv.ofBijective _
      (P.bijective_smul (op (Φ.obj d.unop)) (P.sheaf.obj.map (h.app d.unop).op s))).toIso)
    (fun {d₁ d₂} f ↦ by
      ext g
      have hf : Φ.map f.unop ≫ h.app d₁.unop = h.app d₂.unop := by
        simp
      change _ = P.sheaf.obj.map _ (P.smul _ _ _)
      rw [P.map_smul, ← hf, op_comp, Functor.map_comp]
      rfl)

@[simp]
lemma isoOfSection_hom_app {D : Type u'} [Category.{v'} D] (Φ : D ⥤ C) {V : C}
    (h : Φ ⟶ (Functor.const D).obj V) (s : P.sheaf.obj.obj (op V)) (d : Dᵒᵖ)
    (g : G.obj.obj (op (Φ.obj d.unop))) :
    (P.isoOfSection Φ h s).hom.app d g =
      P.smul (op (Φ.obj d.unop)) g (P.sheaf.obj.map (h.app d.unop).op s) :=
  rfl

end GroupTorsor

end CategoryTheory.Sheaf
