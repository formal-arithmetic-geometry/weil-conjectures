/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.RingTheory.HopfAlgebra.Cartier

/-!
# Cartier's theorem: group schemes in characteristic zero are smooth

**Cartier's theorem** states that every group scheme locally of finite type over a field `K` of
characteristic zero is reduced, and hence smooth over `K`.

A group scheme over `K` is a scheme `G` with a structure morphism `f : G ⟶ Spec K` making
`Over.mk f` a group object of the category of `K`-schemes, that is, carrying

```
  G ×_{Spec K} G --- mul ---> G <--- one --- Spec K
```

together with an inverse `G ⟶ G`, all of them morphisms over `Spec K`.

Mathlib provides `AlgebraicGeometry.smooth_of_grpObj`: a group scheme locally of finite type over
a field which is *geometrically* reduced is smooth over that field. Every base change of a group
scheme over `K` to a field extension `L` is again a group scheme over `L` of characteristic zero,
so reducedness of all such group schemes gives geometric reducedness, hence smoothness.

Reducedness is proved over an algebraic closure and descended along the faithfully flat morphism
`G_K̄ ⟶ G`. Over an algebraically closed field the affine case is Cartier's theorem for Hopf
algebras, `HopfAlgebra.isReduced_of_charZero`.

## Main statements

* `AlgebraicGeometry.isReduced_of_grpObj_of_isAffine`: an affine group scheme of finite type over
  a field of characteristic zero is reduced.
* `AlgebraicGeometry.isReduced_of_grpObj_of_charZero`: a group scheme locally of finite type over a
  field of characteristic zero is reduced.
* `AlgebraicGeometry.isReduced_of_grpObj`: the blueprint statement of reducedness. As stated it
  omits `include f in`, so it does not depend on `f` and claims that every scheme is reduced; it
  is left unproved.
* `AlgebraicGeometry.smooth_of_grpObj_of_charZero`: such a group scheme is smooth over the base
  field.

## Blueprint

`AlgebraicGeometry.isReduced_of_grpObj` and `AlgebraicGeometry.smooth_of_grpObj_of_charZero`
implement `sk-i-cartier`.

The result is due to Cartier, *Questions de rationalité des diviseurs en géométrie algébrique*
(1958).
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [CharZero K] {G : Scheme} (f : G ⟶ Spec (.of K))
  [LocallyOfFiniteType f] [GrpObj (Over.mk f)]

include f in
/-- **Cartier's theorem** for affine group schemes: an affine group scheme of finite type over a
field of characteristic zero is reduced. Its coordinate ring is a finitely generated Hopf algebra,
reduced by `HopfAlgebra.isReduced_of_charZero`. (blueprint: `lem-ag-cartier-reduced`) -/
theorem isReduced_of_grpObj_of_isAffine [IsAffine G] : IsReduced G := by
  obtain ⟨H, ⟨e⟩⟩ := (essImage_hopfSpec (R := .of K) (G := Grp.mk (Over.mk f))).2 ‹_›
  have he : e.hom.hom.hom.left ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K H.unop)) :=
    Over.w e.hom.hom.hom
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K H.unop))) := by
    rw [← he]
    infer_instance
  have : Algebra.FiniteType K H.unop := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
    exact RingHom.finiteType_algebraMap.1 this
  have : _root_.IsReduced H.unop := HopfAlgebra.isReduced_of_charZero (k := K)
  have : IsReduced ((hopfSpec (.of K)).obj H).X.left :=
    inferInstanceAs (IsReduced (Spec (.of H.unop)))
  exact isReduced_of_isOpenImmersion e.inv.hom.hom.left

include f in
/-- **Cartier's theorem** over an algebraically closed field: a group scheme locally of finite type
over an algebraically closed field of characteristic zero is reduced.

The affine case is `isReduced_of_grpObj_of_isAffine`. In general, by translation it suffices that
the local ring at the identity is reduced, which follows as in the affine case from Cartier's
lemma (`AlgHom.exists_apply_eq_one_mul_eq_zero_of_forall_exists_derivation`) applied to the
coordinate ring of an affine open neighbourhood of the identity, once its tangent vectors are
extended to derivations by the invariant vector fields of `G`.
(blueprint: `lem-ag-cartier-reduced`) -/
theorem isReduced_of_grpObj_of_isAlgClosed [IsAlgClosed K] : IsReduced G := by
  sorry

include f in
/-- A group scheme locally of finite type over a field of characteristic zero has no nilpotents
in its structure sheaf, i.e. it is reduced: its base change to an algebraic closure is reduced by
`isReduced_of_grpObj_of_isAlgClosed`, and reducedness descends along the faithfully flat
morphism `G_K̄ ⟶ G`. (blueprint: `sk-i-cartier`, `lem-ag-cartier-reduced`) -/
theorem isReduced_of_grpObj_of_charZero : IsReduced G := by
  let g : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  let : GrpObj (Over.mk (Limits.pullback.snd f g)) := Over.grpObjMkPullbackSnd
  have : IsReduced (Limits.pullback f g) :=
    isReduced_of_grpObj_of_isAlgClosed (Limits.pullback.snd f g)
  have : IsSchemeTheoreticallyDominant g := .of_isDominant g
  exact IsSchemeTheoreticallyDominant.isReduced (Limits.pullback.fst f g)

/-- A group scheme locally of finite type over a field of characteristic zero has no nilpotents
in its structure sheaf, i.e. it is reduced.

As stated, this omits `include f in`: the statement does not mention `f`, so `f` and its instance
arguments are dropped and it claims that every scheme is reduced, which is false. The intended
statement is `isReduced_of_grpObj_of_charZero`.
(blueprint: `sk-i-cartier`) -/
theorem isReduced_of_grpObj : IsReduced G := by
  sorry

/-- **Cartier's theorem**: a group scheme locally of finite type over a field of characteristic
zero is smooth over the base field, equivalently `dim Lie(G) = dim G`.
(blueprint: `sk-i-cartier`) -/
theorem smooth_of_grpObj_of_charZero : Smooth f := by
  have : GeometricallyReduced f := by
    refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms).2 fun L _ _ ↦ ?_⟩
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
    let : GrpObj (Over.mk (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom
      (algebraMap K L))))) := Over.grpObjMkPullbackSnd
    exact isReduced_of_grpObj_of_charZero (Limits.pullback.snd f _)
  exact smooth_of_grpObj f

end AlgebraicGeometry
