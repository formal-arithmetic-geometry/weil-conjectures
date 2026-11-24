/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber

/-! # Comparing two field fibres over the same point

## References

* Stacks Project, Tag 055G
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The comparison isomorphism of fibres over a common field.  Given a point `t` of `T`,
a point `s` of `S`, and morphisms `z : U ⟶ Spec κ(t)`, `k : U ⟶ V`, `y : V ⟶ Spec κ(s)`
inducing the same morphism `U ⟶ S`, the `U`-base change of the fibre of
`pullback.snd f g` over `t` is identified with the `k`-base change of the `y`-base change
of the fibre of `f` over `s`.  It is built from iterated pullback isomorphisms. -/
noncomputable def commonFieldFibreIso {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (t : T) (s : S) {U V : Scheme.{u}} (z : U ⟶ Spec (T.residueField t)) (k : U ⟶ V)
    (y : V ⟶ Spec (S.residueField s))
    (heq : (z ≫ T.fromSpecResidueField t) ≫ g = (k ≫ y) ≫ S.fromSpecResidueField s) :
    pullback ((pullback.snd f g).fiberToSpecResidueField t) z ≅
      pullback (pullback.snd (f.fiberToSpecResidueField s) y) k :=
  pullbackLeftPullbackSndIso (pullback.snd f g) (T.fromSpecResidueField t) z ≪≫
    pullbackLeftPullbackSndIso f g (z ≫ T.fromSpecResidueField t) ≪≫
    pullback.congrHom rfl heq ≪≫
    (pullbackLeftPullbackSndIso f (S.fromSpecResidueField s) (k ≫ y)).symm ≪≫
    (pullbackLeftPullbackSndIso (f.fiberToSpecResidueField s) y k).symm

@[reassoc (attr := simp)]
lemma commonFieldFibreIso_hom_snd {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (t : T) (s : S) {U V : Scheme.{u}} (z : U ⟶ Spec (T.residueField t)) (k : U ⟶ V)
    (y : V ⟶ Spec (S.residueField s))
    (heq : (z ≫ T.fromSpecResidueField t) ≫ g = (k ≫ y) ≫ S.fromSpecResidueField s) :
    (commonFieldFibreIso f g t s z k y heq).hom ≫ pullback.snd _ k = pullback.snd _ z := by
  have h : (pullbackLeftPullbackSndIso f (S.fromSpecResidueField s) (k ≫ y)).inv ≫
      pullback.snd (f.fiberToSpecResidueField s) (k ≫ y) = pullback.snd _ _ := by
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_snd _ _ _).symm
  simp only [commonFieldFibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd,
    Category.comp_id, h, pullbackLeftPullbackSndIso_hom_snd]
  rfl

/-- A field fibre of a pulled-back family surjects onto a prescribed field fibre, via the
base-change projection along a surjection `Spec E → Spec K` composed with the comparison
isomorphism `commonFieldFibreIso` (Stacks, Tag 055G). -/
theorem exists_common_field_fibre_comparison {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (t : T) (s : S) (ht : g t = s)
    (K : Type u) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (S.residueField s))) :
    ∃ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t)))
      (k : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of K))
      (heq : (z ≫ T.fromSpecResidueField t) ≫ g = (k ≫ y) ≫ S.fromSpecResidueField s),
      Surjective k ∧ Surjective ((commonFieldFibreIso f g t s z k y heq).hom ≫
        pullback.fst (pullback.snd (f.fiberToSpecResidueField s) y) k) := by
  classical
  let a := T.fromSpecResidueField t ≫ g
  let b := y ≫ S.fromSpecResidueField s
  let x : Spec (CommRingCat.of (T.residueField t)) := Nonempty.some inferInstance
  let v : Spec (CommRingCat.of K) := Nonempty.some inferInstance
  have hab : a x = b v := by
    change g (T.fromSpecResidueField t x) = S.fromSpecResidueField s (y v)
    rw [Scheme.fromSpecResidueField_apply, Scheme.fromSpecResidueField_apply, ht]
  obtain ⟨r, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x v hab
  let R := pullback a b
  let E := R.residueField r
  let z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t)) :=
    R.fromSpecResidueField r ≫ pullback.fst a b
  let k : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of K) :=
    R.fromSpecResidueField r ≫ pullback.snd a b
  have heq : (z ≫ T.fromSpecResidueField t) ≫ g =
      (k ≫ y) ≫ S.fromSpecResidueField s := by
    simp only [z, k, Category.assoc]
    exact congrArg (R.fromSpecResidueField r ≫ ·) (pullback.condition (f := a) (g := b))
  have : Surjective k :=
    ⟨fun w ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  exact ⟨E, inferInstance, z, k, heq, this, inferInstance⟩

end AlgebraicGeometry
