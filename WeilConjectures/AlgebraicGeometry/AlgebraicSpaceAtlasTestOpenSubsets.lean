/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointClasses
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.Data.Quot

/-!
# Scheme-test subset identities through an étale atlas

Source: Stacks Project, Properties of Spaces, Tags 03BX (`lemma-topology-points`)
and 03H4 (`lemma-points-cartesian`)
(blueprint: lem-a1-space-atlas-test-open-subsets).

All openness assertions concern scheme topologies. No topology on the field-valued
point classes of the algebraic space is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

-- Naturality on scheme points is proved using the residue-field extension.
private theorem schemePointMap_comp {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {U V : Over S} (k : U ⟶ V)
    (a : yoneda.obj V ⟶ F) (x : U.left) :
    schemePointMap (yoneda.map k ≫ a) x = schemePointMap a (k.left x) := by
  apply Quot.sound
  let e := Spec.map (k.left.residueFieldMap x)
  have he : e ≫ V.left.fromSpecResidueField (k.left x) =
      U.left.fromSpecResidueField x ≫ k.left :=
    k.left.SpecMap_residueFieldMap_fromSpecResidueField x
  let r : Over.mk (U.left.fromSpecResidueField x ≫ U.hom) ⟶
      Over.mk (V.left.fromSpecResidueField (k.left x) ≫ V.hom) :=
    Over.homMk e (by
      change e ≫ (V.left.fromSpecResidueField (k.left x) ≫ V.hom) =
        U.left.fromSpecResidueField x ≫ U.hom
      rw [← Category.assoc, he, Category.assoc, Over.w])
  refine ⟨U.left.residueField x, inferInstance,
    U.left.fromSpecResidueField x ≫ U.hom, 𝟙 _, r, ?_⟩
  dsimp only [PointRepresentative.value]
  rw [CategoryTheory.op_id, F.map_id]
  change (yoneda.map k ≫ a).app _ (Over.homMk _ rfl) =
    F.map r.op (a.app _ (Over.homMk _ rfl))
  rw [← NatTrans.naturality_apply]
  apply congrArg (a.app _)
  apply Over.OverMorphism.ext
  exact he.symm

-- A point of a fibre product of field spectra gives a common extension.
private theorem pointRepresentative_rel_equivalence {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type u) : Equivalence (PointRepresentative.Rel (F := F)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact ⟨p.K, inferInstance, p.base, 𝟙 _, 𝟙 _, rfl⟩
  · rintro p q ⟨K, hK, s, a, b, h⟩
    exact ⟨K, hK, s, b, a, h.symm⟩
  · rintro p q r ⟨K, hK, s, a, b, h⟩ ⟨L, hL, t, c, d, h'⟩
    let P := Limits.pullback b c
    let i : P ⟶ Over.mk s := Limits.pullback.fst b c
    let j : P ⟶ Over.mk t := Limits.pullback.snd b c
    have sq : IsPullback i.left j.left b.left c.left :=
      (IsPullback.of_hasPullback b c).map (Over.forget S)
    obtain ⟨z, _, _⟩ := Scheme.exists_preimage_of_isPullback sq
      (IsLocalRing.closedPoint K) (IsLocalRing.closedPoint L)
      (@Subsingleton.elim (Spec (CommRingCat.of q.K)) inferInstance _ _)
    let H := Over.mk (P.left.fromSpecResidueField z ≫ P.hom)
    let e : H ⟶ P := Over.homMk (P.left.fromSpecResidueField z) rfl
    refine ⟨P.left.residueField z, inferInstance, H.hom, e ≫ i ≫ a, e ≫ j ≫ d, ?_⟩
    have hij : (e ≫ i) ≫ b = (e ≫ j) ≫ c := by
      simp only [Category.assoc, i, j, Limits.pullback.condition]
    calc
      F.map (e ≫ i ≫ a).op p.value = F.map (e ≫ i).op (F.map a.op p.value) := by
        simp only [op_comp, F.map_comp, types_comp_apply, Category.assoc]
      _ = F.map (e ≫ i).op (F.map b.op q.value) := congrArg _ h
      _ = F.map ((e ≫ i) ≫ b).op q.value := by
        simp only [op_comp, F.map_comp, types_comp_apply]
      _ = F.map ((e ≫ j) ≫ c).op q.value := by rw [hij]
      _ = F.map (e ≫ j).op (F.map c.op q.value) := by
        simp only [op_comp, F.map_comp, types_comp_apply]
      _ = F.map (e ≫ j).op (F.map d.op r.value) := congrArg _ h'
      _ = F.map (e ≫ j ≫ d).op r.value := by
        simp only [op_comp, F.map_comp, types_comp_apply, Category.assoc]

private theorem equal_point_classes_witness {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {C U : Over S}
    (c : yoneda.obj C ⟶ F) (f : yoneda.obj U ⟶ F)
    (x : C.left) (y : U.left) (h : schemePointMap c x = schemePointMap f y) :
    ∃ (K : Type u) (_ : Field K) (s : Spec (CommRingCat.of K) ⟶ S)
      (a : Over.mk s ⟶ C) (b : Over.mk s ⟶ U) (z : Spec (CommRingCat.of K)),
      a.left z = x ∧ b.left z = y ∧ c.app (op (Over.mk s)) a =
        f.app (op (Over.mk s)) b := by
  have hr := (pointRepresentative_rel_equivalence F).eqvGen_iff.mp
    (Quot.eqvGen_exact h)
  obtain ⟨K, hK, s, a, b, hab⟩ := hr
  let rx : Over.mk (C.left.fromSpecResidueField x ≫ C.hom) ⟶ C :=
    Over.homMk (C.left.fromSpecResidueField x) rfl
  let ry : Over.mk (U.left.fromSpecResidueField y ≫ U.hom) ⟶ U :=
    Over.homMk (U.left.fromSpecResidueField y) rfl
  refine ⟨K, hK, s, a ≫ rx, b ≫ ry, IsLocalRing.closedPoint K, ?_, ?_, ?_⟩
  · change C.left.fromSpecResidueField x (a.left (IsLocalRing.closedPoint K)) = x
    exact Scheme.fromSpecResidueField_apply x _
  · change U.left.fromSpecResidueField y (b.left (IsLocalRing.closedPoint K)) = y
    exact Scheme.fromSpecResidueField_apply y _
  · change F.map a.op (c.app _ rx) = F.map b.op (f.app _ ry) at hab
    simpa only [← NatTrans.naturality_apply, yoneda_obj_map, Quiver.Hom.unop_op,
      ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk] using hab

private theorem property_on_scheme_test {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F : (Over S)ᵒᵖ ⥤ Type u} {W T Q : Over S}
    {w : yoneda.obj W ⟶ F} {t : yoneda.obj T ⟶ F} {q : Q ⟶ T} {b : Q ⟶ W}
    (sq : IsPullback (yoneda.map b) (yoneda.map q) w t)
    (hw : IsRepresentableWith (P.inverseImage (Over.forget S)) w) : P q.left := by
  obtain ⟨V, r, s, hs, hr⟩ := hw T t
  let e : Q ≅ V := yoneda.preimageIso (sq.isoIsPullback _ _ hs)
  have he : e.hom ≫ r = q := by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, e, Functor.preimageIso_hom, Functor.map_preimage]
      using sq.isoIsPullback_hom_snd _ _ hs
  rw [← he]
  change P (e.hom.left ≫ r.left)
  exact (P.cancel_left_of_respectsIso _ _).mpr hr

/-- Pulling a fixed surjective étale atlas back to a scheme gives the inverse-image
identities, the descent of openness, and the image identity for arbitrary point subsets.
If the test map is representable étale, its base change is étale and the image identity
identifies an open subset of the atlas.
Source: Stacks, Properties of Spaces, Tags 03BX and 03H4; Morphisms, Tag 03WT
(blueprint: lem-a1-space-atlas-test-open-subsets).
Proof:
1. Scheme-test representability of the atlas gives a scheme `Q` representing `T ×_E W`.
   Its projection `q` is surjective étale by [def-trf-algebraic-space]. Scheme morphisms
   are continuous, and [lem-weil-pbc-etale-morphism-open-map] makes `q` open.
2. The representing square commutes. Restricting the two residue-field representatives
   to the residue field of each point of `Q` proves equality of their point classes,
   using [def-a1-algebraic-space-point-classes].
3. This equality gives the first inverse-image identity. Surjectivity of `q` gives both
   inclusions in the second, image identity.
4. If the atlas preimage of `A` is open, pull it back along the continuous `b` and
   push it forward along the open `q`. Step 3 identifies the result with the test preimage.
5. For `B`, commutativity gives one inclusion in the last image identity. Conversely,
   [lem-a1-space-fibre-product-point] lifts every pair of points with equal image classes
   to `Q`, proving the other inclusion.
6. If the test map is representable étale, its scheme test along the atlas makes `b`
   étale. For open `B`, continuity of `q` and openness of `b` make `b(q⁻¹(B))` open;
   step 5 gives the desired subset of `W`. Only scheme topologies were used. -/
theorem exists_atlas_test_open_subsets {S : Scheme.{u}} (E : AlgebraicSpace S)
    (W T : Over S) (w : yoneda.obj W ⟶ E.obj.obj) (t : yoneda.obj T ⟶ E.obj.obj)
    (hw : IsEtale w) (hs : IsSurjective w) :
    ∃ (Q : Over S) (q : Q ⟶ T) (b : Q ⟶ W),
      IsPullback (yoneda.map q) (yoneda.map b) t w ∧
      Etale q.left ∧ Surjective q.left ∧ Continuous q.left ∧ IsOpenMap q.left ∧
      (∀ A : Set (Point E.obj.obj),
        q.left ⁻¹' (schemePointMap t ⁻¹' A) = b.left ⁻¹' (schemePointMap w ⁻¹' A) ∧
        q.left '' (b.left ⁻¹' (schemePointMap w ⁻¹' A)) = schemePointMap t ⁻¹' A ∧
        (IsOpen (schemePointMap w ⁻¹' A) → IsOpen (schemePointMap t ⁻¹' A))) ∧
      (∀ B : Set T.left,
        b.left '' (q.left ⁻¹' B) = schemePointMap w ⁻¹' (schemePointMap t '' B)) ∧
      (IsEtale t → Etale b.left ∧ ∀ B : Set T.left, IsOpen B →
        IsOpen (schemePointMap w ⁻¹' (schemePointMap t '' B))) := by
  classical
  obtain ⟨Q, q, b, sq, hlift, _⟩ := exists_scheme_fibreProduct_point E T W t w
  have hq : Etale q.left := property_on_scheme_test @Etale sq.flip hw
  have hsurj : Surjective q.left := property_on_scheme_test @Surjective sq.flip hs
  have hcomm (z : Q.left) : schemePointMap t (q.left z) =
      schemePointMap w (b.left z) := by
    rw [← schemePointMap_comp, ← schemePointMap_comp, sq.w]
  have himage (B : Set T.left) :
      b.left '' (q.left ⁻¹' B) = schemePointMap w ⁻¹' (schemePointMap t '' B) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨q.left z, hz, hcomm z⟩
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨z, hzx, hzy⟩ := hlift x y (equal_point_classes_witness t w x y hxy)
      refine ⟨z, ?_, hzy⟩
      change q.left z ∈ B
      rw [hzx]
      exact hx
  refine ⟨Q, q, b, sq, hq, hsurj, q.left.continuous, q.left.isOpenMap, ?_,
    himage, ?_⟩
  · intro A
    have hpre : q.left ⁻¹' (schemePointMap t ⁻¹' A) =
        b.left ⁻¹' (schemePointMap w ⁻¹' A) := by
      ext z
      exact (congrArg (· ∈ A) (hcomm z)).to_iff
    have him : q.left '' (b.left ⁻¹' (schemePointMap w ⁻¹' A)) =
        schemePointMap t ⁻¹' A := by
      rw [← hpre, Set.image_preimage_eq _ q.left.surjective]
    refine ⟨hpre, him, ?_⟩
    intro hA
    rw [← him]
    exact q.left.isOpenMap _ (hA.preimage b.left.continuous)
  · intro ht
    have hb : Etale b.left := property_on_scheme_test @Etale sq ht
    refine ⟨hb, ?_⟩
    intro B hB
    rw [← himage]
    exact b.left.isOpenMap _ (hB.preimage q.left.continuous)

end AlgebraicGeometry.AlgebraicSpace
