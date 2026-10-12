/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.NonvanishingTensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Pullback of tensor-power sections and their nonvanishing loci

Source: Stacks Project, Modules, Tags 01CD and 01CT; Morphisms, Tag 0892, part (2).
(blueprint: lem-weil-pbc-tensor-power-section-nonvanishing-pullback).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- A section of a positive tensor power pulls back to a section of the same power
of the pulled-back invertible module, with inverse-image nonvanishing locus.

Source: Stacks Project, Modules, Tags 01CD and 01CT; Morphisms, Tag 0892, part (2).
(blueprint: lem-weil-pbc-tensor-power-section-nonvanishing-pullback).

Proof: identify the tensor-formula pullback with the usual module pullback by
uniqueness of left adjoints to module pushforward (`nonempty_tensorPullbackAdjunction`).
The usual pullback is monoidal. Its unit comparison and tensor comparison give by
induction an isomorphism from the pullback of `L.tensorPow n` to
`((tensorPullback g).obj L).tensorPow n`, including the structure module at exponent
zero. Apply the pullback adjunction unit to `s`, identify the
inverse image of the top open with the top open, and transport this section through
the tensor-power isomorphism to obtain `t`.

At a point `y`, the fibre formula of `invertible_pullback_tensor`, applied to the
invertible module `L.tensorPow n`, identifies the value of the pulled-back section
with `1` tensored with the value of `s` at `g y`. Tensor powers are invertible by
induction using the invertible structure module and invertible tensor products.
A vector over a field becomes zero after extending scalars to another field if and
only if it was zero: choose a basis, or extend a nonzero vector to a basis. The
residue-field map here is an injective unital map of fields. Finally the kernel of
the stalk-to-fibre map is the maximal ideal times the stalk module, as follows by
identifying extension to the residue field with the quotient by that submodule.
Thus nonvanishing in the sense of `nonvanishingLocus` is exactly a nonzero fibre
value. Module isomorphisms preserve that condition. This proves the displayed
equality, for all points of `Y`, without any assumption on the morphism `g`.
-/
theorem exists_tensorPow_section_nonvanishing_pullback {X Y : Scheme.{u}}
    (g : Y ⟶ X) (L : X.Modules) [L.IsInvertible] (n : ℕ) (hn : 0 < n)
    (s : (L.tensorPow n).val.presheaf.obj (Opposite.op ⊤)) :
    ∃ t : (((tensorPullback g).obj L).tensorPow n).val.presheaf.obj (Opposite.op ⊤),
      nonvanishingLocus (((tensorPullback g).obj L).tensorPow n) t =
        g ⁻¹' nonvanishingLocus (L.tensorPow n) s := by
  classical
  have stalk_map_smul : ∀ {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
      (x : X) (r : X.presheaf.stalk x)
      (m : ↑(TopCat.Presheaf.stalk M.val.presheaf x)),
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (f.mapPresheaf) (r • m) =
        r • (show ↑(TopCat.Presheaf.stalk N.val.presheaf x) from
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.mapPresheaf m) := by
    intro X M N f x r m
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
    have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
    rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
      ← TopCat.Presheaf.germ_res_apply M.val.presheaf
        (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m,
      ← PresheafOfModules.germ_smul]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change TopCat.Presheaf.germ N.val.presheaf (U ⊓ V) x hx
        (f.app (U ⊓ V) (_ • _)) = _
    rw [Hom.app_smul, PresheafOfModules.germ_smul]
    rfl
  have nonvanishingLocus_iso : ∀ {X : Scheme.{u}} {M N : X.Modules}
      (e : M ≅ N) (s : M.val.presheaf.obj (Opposite.op ⊤)),
      nonvanishingLocus N (e.hom.app ⊤ s) = nonvanishingLocus M s := by
    intro X M N e s
    ext y
    let F := toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
    let a := F.mapIso e
    let f : ↑(TopCat.Presheaf.stalk M.val.presheaf y) →ₗ[X.presheaf.stalk y]
        ↑(TopCat.Presheaf.stalk N.val.presheaf y) :=
      { toFun := a.hom
        map_add' := map_add a.hom.hom
        map_smul' := stalk_map_smul e.hom y }
    let g : ↑(TopCat.Presheaf.stalk N.val.presheaf y) →ₗ[X.presheaf.stalk y]
        ↑(TopCat.Presheaf.stalk M.val.presheaf y) :=
      { toFun := a.inv
        map_add' := map_add a.inv.hom
        map_smul' := stalk_map_smul e.inv y }
    have hg : f (TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial s) =
        TopCat.Presheaf.germ N.val.presheaf ⊤ y trivial (e.hom.app ⊤ s) := by
      exact TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ y trivial e.hom.mapPresheaf s
    have hi : ∀ m, g (f m) = m := by
      intro m
      exact ConcreteCategory.congr_hom a.hom_inv_id m
    have hf := Submodule.smul_top_le_comap_smul_top
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) f
    have hb := Submodule.smul_top_le_comap_smul_top
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) g
    change _ ∉ _ ↔ _ ∉ _
    rw [← hg]
    constructor
    · intro h hm
      exact h (hf hm)
    · intro h hm
      apply h
      have hh := hb hm
      change g (f (TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial s)) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y)
            ↑(TopCat.Presheaf.stalk M.val.presheaf y)) at hh
      rwa [hi] at hh
  have tensorPow_iso : ∀ {X : Scheme.{u}} {M N : X.Modules}
      (e : M ≅ N) (n : ℕ), Nonempty (M.tensorPow n ≅ N.tensorPow n) := by
    intro X M N e n
    induction n with
    | zero => exact ⟨Iso.refl _⟩
    | succ n ih =>
      obtain ⟨a⟩ := ih
      exact ⟨MonoidalCategory.tensorIso e a⟩
  have _hpos : 0 < n := hn
  let a := (Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (pullbackPushforwardAdjunction g)
  obtain ⟨b⟩ := nonempty_pullback_tensorPow_iso g L n
  obtain ⟨c⟩ := tensorPow_iso (a.app L).symm n
  let e := a.app (L.tensorPow n) ≪≫ b ≪≫ c
  let r : Γ((tensorPullback g).obj (L.tensorPow n), ⊤) :=
    ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
      (L.tensorPow n)).val.app (Opposite.op ⊤) s
  refine ⟨e.hom.app ⊤ r, ?_⟩
  rw [nonvanishingLocus_iso e r]
  ext y
  exact nonvanishing_tensorPullback g (L.tensorPow n) s y

end AlgebraicGeometry.Scheme.Modules
