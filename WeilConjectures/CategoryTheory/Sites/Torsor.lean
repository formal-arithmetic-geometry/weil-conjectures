/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Torsors under a sheaf of abelian groups

Let `G` be a sheaf of abelian groups on a site `(C, J)`. A `G`-torsor is a sheaf of sets `T`
with an action of `G` which is simply transitive on the sections over every object and such
that `T` has sections locally. The isomorphism classes of `G`-torsors are classified by
`H¹(G) = Ext¹(ℤ, G)`.

## Main definitions

- `CategoryTheory.Sheaf.Torsor`: a `G`-torsor.
- `CategoryTheory.Sheaf.Torsor.Iso`: an isomorphism of `G`-torsors, and
  `CategoryTheory.Sheaf.Torsor.setoid` the relation of being isomorphic.
- `CategoryTheory.Sheaf.Torsor.trivial`: the trivial torsor `G`.

## Main statements

- `CategoryTheory.Sheaf.nonempty_equiv_ext_torsor`: `Ext¹(ℤ, G)` is in bijection with the
  isomorphism classes of `G`-torsors. The proof is `sorry`.
- `CategoryTheory.Sheaf.nonempty_equiv_H_one_torsor`: so is `H¹(G)`.
- `CategoryTheory.Sheaf.subsingleton_H_one_iff`: `H¹(G) = 0` if and only if every `G`-torsor
  is trivial.

## TODO

The bijections are only recorded as the existence of an equivalence of types. The canonical
map sends an extension `0 → G → E → ℤ → 0` to the torsor `π⁻¹(1)`, and it carries the Baer
sum to the contracted product of torsors.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory.Sheaf

open Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The sieve on `U` of the morphisms `V ⟶ U` such that the presheaf `F` has a section
over `V`. -/
def nonemptySieve (F : Cᵒᵖ ⥤ Type w) (U : C) : Sieve U where
  arrows V _ := Nonempty (F.obj (op V))
  downward_closed {_ _} _ := fun ⟨t⟩ g ↦ ⟨F.map g.op t⟩

/-- A *torsor* under a sheaf `G` of abelian groups: a sheaf of sets `T` with an action
`G × T → T` of `G` which is simply transitive on the sections over every object, and such
that `T` has sections locally, i.e. every object is covered by objects over which `T` has a
section. Equivalently, `T` is locally isomorphic to `G` with its translation action.
(blueprint: `def-sc-gm-torsor`, for a general abelian sheaf `G` on a general site; the étale
`𝔾ₘ`-torsors and the Zariski `𝒪ˣ`-torsors of the blueprint are the cases
`G = AlgebraicGeometry.Scheme.gmSheaf X` and `G = AlgebraicGeometry.Scheme.unitsSheaf X`) -/
structure Torsor (G : Sheaf J AddCommGrpCat.{w}) where
  /-- The underlying sheaf of sets. -/
  sheaf : Sheaf J (Type w)
  /-- The action of `G` on `T`. -/
  vadd (U : Cᵒᵖ) : G.obj.obj U → sheaf.obj.obj U → sheaf.obj.obj U
  zero_vadd (U : Cᵒᵖ) (t : sheaf.obj.obj U) : vadd U 0 t = t
  add_vadd (U : Cᵒᵖ) (g h : G.obj.obj U) (t : sheaf.obj.obj U) :
    vadd U (g + h) t = vadd U g (vadd U h t)
  map_vadd {U V : Cᵒᵖ} (f : U ⟶ V) (g : G.obj.obj U) (t : sheaf.obj.obj U) :
    sheaf.obj.map f (vadd U g t) = vadd V (G.obj.map f g) (sheaf.obj.map f t)
  /-- The action is simply transitive on the sections over every object. -/
  bijective_vadd (U : Cᵒᵖ) (t : sheaf.obj.obj U) : Function.Bijective (vadd U · t)
  /-- The torsor has sections locally. -/
  nonemptySieve_mem (U : C) : nonemptySieve sheaf.obj U ∈ J U

namespace Torsor

variable {G : Sheaf J AddCommGrpCat.{w}}

/-- An isomorphism of `G`-torsors: an isomorphism of the underlying sheaves of sets which
commutes with the action of `G`. -/
structure Iso (T T' : Torsor G) where
  /-- The isomorphism of underlying sheaves of sets. -/
  iso : T.sheaf ≅ T'.sheaf
  map_vadd (U : Cᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U) :
    iso.hom.hom.app U (T.vadd U g t) = T'.vadd U g (iso.hom.hom.app U t)

/-- The identity isomorphism of a torsor. -/
def Iso.refl (T : Torsor G) : Iso T T where
  iso := CategoryTheory.Iso.refl _
  map_vadd _ _ _ := rfl

/-- The inverse of an isomorphism of torsors. -/
def Iso.symm {T T' : Torsor G} (e : Iso T T') : Iso T' T where
  iso := e.iso.symm
  map_vadd U g t := by
    let f := ((sheafSections J (Type w)).obj U).mapIso e.iso
    have h (x : T'.sheaf.obj.obj U) : e.iso.hom.hom.app U (e.iso.inv.hom.app U x) = x :=
      Iso.inv_hom_id_apply f x
    apply f.toEquiv.injective
    change e.iso.hom.hom.app U (e.iso.inv.hom.app U _) = e.iso.hom.hom.app U _
    rw [h, e.map_vadd]
    exact congr_arg _ (h t).symm

/-- The composition of two isomorphisms of torsors. -/
def Iso.trans {T T' T'' : Torsor G} (e : Iso T T') (e' : Iso T' T'') : Iso T T'' where
  iso := e.iso ≪≫ e'.iso
  map_vadd U g t := by
    change e'.iso.hom.hom.app U (e.iso.hom.hom.app U _) = _
    rw [e.map_vadd, e'.map_vadd]
    rfl

/-- Being isomorphic is an equivalence relation on `G`-torsors; its quotient is the set of
isomorphism classes of `G`-torsors. -/
instance setoid : Setoid (Torsor G) where
  r T T' := Nonempty (Iso T T')
  iseqv := ⟨fun T ↦ ⟨Iso.refl T⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩

variable (G) in
/-- The trivial `G`-torsor: `G` acting on itself by translation. -/
def trivial : Torsor G where
  sheaf := (sheafCompose J (forget AddCommGrpCat.{w})).obj G
  vadd U g t := (g + show G.obj.obj U from t : G.obj.obj U)
  zero_vadd U t := zero_add (show G.obj.obj U from t)
  add_vadd U g h t := add_assoc g h (show G.obj.obj U from t)
  map_vadd f g _ := map_add (G.obj.map f).hom g _
  bijective_vadd U t := (Equiv.addRight (show G.obj.obj U from t)).bijective
  nonemptySieve_mem U := J.superset_covering (fun _ _ _ ↦ ⟨(0 : G.obj.obj _)⟩) (J.top_mem U)

end Torsor

variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- **Extensions and torsors.** For a sheaf `G` of abelian groups on a site, the group
`Ext¹(ℤ, G)` of extensions `0 → G → E → ℤ → 0` is in bijection with the set of isomorphism
classes of `G`-torsors. The canonical bijection sends an extension `E` with projection
`π : E → ℤ` to the torsor `π⁻¹(1)`; its inverse sends `T` to `⊔_{n ∈ ℤ} T^{⊗ n}`.

Only the existence of a bijection is recorded. The proof is `sorry`.
(blueprint: `lem-sc-ext-torsor`) -/
theorem nonempty_equiv_ext_torsor (G : Sheaf J AddCommGrpCat.{w}) :
    Nonempty (Abelian.Ext ((constantSheaf J AddCommGrpCat.{w}).obj
      (AddCommGrpCat.of (ULift ℤ))) G 1 ≃ _root_.Quotient (Torsor.setoid (G := G))) :=
  sorry

/-- **First cohomology classifies torsors.** For a sheaf `G` of abelian groups on a site,
`H¹(G)` is in bijection with the set of isomorphism classes of `G`-torsors: it is
`Ext¹(ℤ, G)`, to which `CategoryTheory.Sheaf.nonempty_equiv_ext_torsor` applies.

The vanishing direction is also proved directly, without torsors, in
`CategoryTheory.Sheaf.subsingleton_H_one_of_surjective`.
(blueprint: `lem-sc-torsor-h1`) -/
theorem nonempty_equiv_H_one_torsor (G : Sheaf J AddCommGrpCat.{w}) :
    Nonempty (H G 1 ≃ _root_.Quotient (Torsor.setoid (G := G))) :=
  nonempty_equiv_ext_torsor G

/-- `H¹(G)` vanishes if and only if every `G`-torsor is trivial. -/
theorem subsingleton_H_one_iff (G : Sheaf J AddCommGrpCat.{w}) :
    Subsingleton (H G 1) ↔ ∀ T : Torsor G, T ≈ Torsor.trivial G := by
  obtain ⟨e⟩ := nonempty_equiv_H_one_torsor G
  rw [e.subsingleton_congr]
  refine ⟨fun h T ↦ _root_.Quotient.exact (Subsingleton.elim (h := h) ⟦T⟧ ⟦Torsor.trivial G⟧),
    fun h ↦ ⟨fun a b ↦ ?_⟩⟩
  induction a using _root_.Quotient.inductionOn
  induction b using _root_.Quotient.inductionOn
  exact _root_.Quotient.sound (Setoid.trans (h _) (Setoid.symm (h _)))

end CategoryTheory.Sheaf
