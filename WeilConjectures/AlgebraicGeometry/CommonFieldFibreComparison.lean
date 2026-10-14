/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber

/-! # Comparing two field fibres over the same point

Source: Stacks Project, Tag 055G, descent from the étale model;
Mathlib's pullback carrier and iterated pullback isomorphisms.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A field fibre of a pulled-back family surjects onto a prescribed field fibre.

Source: Stacks Project, Tag 055G, descent from the model by common field extension.
Proof: form the fibre product of Spec κ(t) and Spec K over S. Both field points
map to s, so it is nonempty. The residue field E of any point of that product gives
compatible maps to Spec κ(t) and Spec K. Associativity of pullbacks identifies the
E-fibre of X ×_S T over t with the E-base change of the prescribed K-fibre of X.
The projection to the K-fibre is surjective since the map Spec E → Spec K is
surjective and surjectivity is preserved by base change.

(blueprint: lem-sbc-common-field-fibre-comparison) -/
theorem exists_common_field_fibre_comparison {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (t : T) (s : S) (ht : g t = s)
    (K : Type u) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (S.residueField s))) :
    ∃ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t)))
      (p : pullback ((pullback.snd f g).fiberToSpecResidueField t) z ⟶
        pullback (f.fiberToSpecResidueField s) y), Surjective p := by
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
  let e :=
    pullbackLeftPullbackSndIso (pullback.snd f g) (T.fromSpecResidueField t) z ≪≫
    pullbackLeftPullbackSndIso f g (z ≫ T.fromSpecResidueField t) ≪≫
    pullback.congrHom rfl heq ≪≫
    (pullbackLeftPullbackSndIso f (S.fromSpecResidueField s) (k ≫ y)).symm ≪≫
    (pullbackLeftPullbackSndIso (f.fiberToSpecResidueField s) y k).symm
  have : Surjective k :=
    ⟨fun w ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  refine ⟨E, inferInstance, z,
    e.hom ≫ pullback.fst (pullback.snd (f.fiberToSpecResidueField s) y) k, ?_⟩
  infer_instance

end AlgebraicGeometry
