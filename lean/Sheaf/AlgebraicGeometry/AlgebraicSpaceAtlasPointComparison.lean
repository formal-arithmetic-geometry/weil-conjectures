module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Logic.Relation

/-!
# Common-atlas point comparison

Source: Stacks Project, Properties of Spaces, Tags 03BX and 03H4
(blueprint: lem-a1-space-atlas-point-comparison).

The common scheme presentation compares subsets using only the topologies of schemes.
No topology on the set of algebraic-space point classes is used.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

private theorem pointRepresentative_equivalence {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type u) : Equivalence (PointRepresentative.Rel (F := F)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨x.K, inferInstance, x.base, 𝟙 _, 𝟙 _, rfl⟩
  · rintro x y ⟨L, hL, s, a, b, hab⟩
    exact ⟨L, hL, s, b, a, hab.symm⟩
  · rintro x y z ⟨L, hL, s, a, b, hab⟩ ⟨M, hM, t, c, d, hcd⟩
    let P := Limits.pullback b.left c.left
    obtain ⟨v, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := b.left) (g := c.left) (IsLocalRing.closedPoint L)
      (IsLocalRing.closedPoint M)
      (Subsingleton.elim (α := Spec (CommRingCat.of y.K)) _ _)
    let e₀ : Spec (P.residueField v) ⟶ Spec (CommRingCat.of L) :=
      P.fromSpecResidueField v ≫ Limits.pullback.fst b.left c.left
    let f₀ : Spec (P.residueField v) ⟶ Spec (CommRingCat.of M) :=
      P.fromSpecResidueField v ≫ Limits.pullback.snd b.left c.left
    have hef : e₀ ≫ b.left = f₀ ≫ c.left := by
      dsimp only [e₀, f₀]
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
    let e : Over.mk (e₀ ≫ s) ⟶ Over.mk s := Over.homMk e₀ rfl
    let f : Over.mk (e₀ ≫ s) ⟶ Over.mk t := Over.homMk f₀ (by
      change f₀ ≫ t = e₀ ≫ s
      have hb : b.left ≫ y.base = s := Over.w b
      have hc : c.left ≫ y.base = t := Over.w c
      rw [← hc, ← hb, ← Category.assoc, ← hef, Category.assoc])
    have hef' : e ≫ b = f ≫ c := by
      apply Over.OverMorphism.ext
      exact hef
    refine ⟨P.residueField v, inferInstance, e₀ ≫ s, e ≫ a, f ≫ d, ?_⟩
    have heval := congrArg (fun k ↦ F.map k.op y.value) hef'
    simp only [CategoryTheory.op_comp, F.map_comp, types_comp_apply]
    rw [hab, ← hcd]
    simpa only [CategoryTheory.op_comp, F.map_comp, types_comp_apply] using heval

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

private theorem point_class_common_field {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {W V : Over S}
    (w : yoneda.obj W ⟶ F) (p : yoneda.obj V ⟶ F)
    (x : W.left) (y : V.left) (h : schemePointMap w x = schemePointMap p y) :
    ∃ (K : Type u) (_ : Field K) (s : Spec (CommRingCat.of K) ⟶ S)
      (a : Over.mk s ⟶ W) (b : Over.mk s ⟶ V) (t : Spec (CommRingCat.of K)),
      a.left t = x ∧ b.left t = y ∧
        w.app (Opposite.op (Over.mk s)) a = p.app (Opposite.op (Over.mk s)) b := by
  have hr := (pointRepresentative_equivalence F).eqvGen_iff.mp (Quot.eq.mp h)
  obtain ⟨K, hK, s, a, b, hab⟩ := hr
  let rx : Over.mk (W.left.fromSpecResidueField x ≫ W.hom) ⟶ W :=
    Over.homMk (W.left.fromSpecResidueField x) rfl
  let ry : Over.mk (V.left.fromSpecResidueField y ≫ V.hom) ⟶ V :=
    Over.homMk (V.left.fromSpecResidueField y) rfl
  refine ⟨K, hK, s, a ≫ rx, b ≫ ry, IsLocalRing.closedPoint K, ?_, ?_, ?_⟩
  · exact W.left.fromSpecResidueField_apply x _
  · exact V.left.fromSpecResidueField_apply y _
  · change F.map a.op (w.app _ rx) = F.map b.op (p.app _ ry) at hab
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply] at hab
    exact hab

private theorem representable_property_scheme_test {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) [P.RespectsIso]
    {F : (Over S)ᵒᵖ ⥤ Type u} {W V Q : Over S}
    {w : yoneda.obj W ⟶ F} {p : yoneda.obj V ⟶ F} {a : Q ⟶ W}
    {b : Q ⟶ V} (h : IsPullback (yoneda.map a) (yoneda.map b) w p)
    (hp : IsRepresentableWith P p) : P a := by
  obtain ⟨T, r, q, hq, hr⟩ := hp W w
  let c : T ⟶ V := yoneda.preimage q
  have hc : yoneda.map c = q := Functor.map_preimage _ _
  have hq' : IsPullback (yoneda.map r) (yoneda.map c) w p := by
    rw [hc]
    exact hq.flip
  let e : Q ≅ T := yoneda.preimageIso (h.isoIsPullback _ _ hq')
  have he : e.hom ≫ r = a := by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, e, Functor.preimageIso_hom, Functor.map_preimage]
      using h.isoIsPullback_hom_fst _ _ hq'
  rw [← he, P.cancel_left_of_respectsIso]
  exact hr

/-- Two surjective étale scheme atlases have a common scheme fibre product with
surjective étale, continuous open projections. The projections lift every pair of scheme
points with equal image class, transport the two inverse images of every subset, and
show that the atlases detect the same open subsets.
Source: Stacks Project, Properties of Spaces, Tag 03BX, proof comparing presentations,
and Tag 03H4 (blueprint: lem-a1-space-atlas-point-comparison).

Proof: (1) Apply `IsEtale` and `IsSurjective` from [def-trf-algebraic-space] to each
atlas tested along the other. Representability and uniqueness of fibre products give
a single representing scheme `Q`, with both projections surjective and étale.
(2) Scheme morphisms are continuous [def-pc-scheme]; the étale projections are open by
[lem-weil-pbc-etale-morphism-open-map].
(3) Apply [lem-a1-space-fibre-product-point] to `W`, `V`, `w`, `p`. Equality of image
classes supplies a common field extension on which the two representatives agree;
its map into the represented fibre product gives a point over the specified pair.
(4) For `B = schemePointMap w ⁻¹' A` and `C = schemePointMap p ⁻¹' A`, commutativity
of the square and [def-a1-algebraic-space-point-classes] give `a ⁻¹' B = b ⁻¹' C`.
Surjectivity of the two projections then gives `a '' (b ⁻¹' C) = B` and
`b '' (a ⁻¹' B) = C`.
(5) If `B` is open, pull it back along continuous `a` and take its image along open `b`
to obtain open `C`. Interchanging the projections proves the converse. -/
theorem exists_atlas_point_comparison {S : Scheme.{u}} (E : AlgebraicSpace S)
    (W V : Over S) (w : yoneda.obj W ⟶ E.obj.obj) (p : yoneda.obj V ⟶ E.obj.obj)
    (hw : IsEtale w) (hsw : IsSurjective w) (hp : IsEtale p) (hsp : IsSurjective p) :
    ∃ (Q : Over S) (a : Q ⟶ W) (b : Q ⟶ V),
      IsPullback (yoneda.map a) (yoneda.map b) w p ∧
      Etale a.left ∧ Surjective a.left ∧ Etale b.left ∧ Surjective b.left ∧
      Continuous a.left ∧ IsOpenMap a.left ∧ Continuous b.left ∧ IsOpenMap b.left ∧
      (∀ (x : W.left) (y : V.left), schemePointMap w x = schemePointMap p y →
        ∃ z : Q.left, a.left z = x ∧ b.left z = y) ∧
      (∀ A : Set (Point E.obj.obj),
        a.left '' (b.left ⁻¹' (schemePointMap p ⁻¹' A)) = schemePointMap w ⁻¹' A ∧
        b.left '' (a.left ⁻¹' (schemePointMap w ⁻¹' A)) = schemePointMap p ⁻¹' A ∧
        (IsOpen (schemePointMap w ⁻¹' A) ↔ IsOpen (schemePointMap p ⁻¹' A))) := by
  classical
  obtain ⟨Q, a, b, hQ, hlift, _⟩ := exists_scheme_fibreProduct_point E W V w p
  have ha : Etale a.left := representable_property_scheme_test
    (MorphismProperty.inverseImage @Etale (Over.forget S)) hQ hp
  have hsa : Surjective a.left := representable_property_scheme_test
    (MorphismProperty.inverseImage @Surjective (Over.forget S)) hQ hsp
  have hb : Etale b.left := representable_property_scheme_test
    (MorphismProperty.inverseImage @Etale (Over.forget S)) hQ.flip hw
  have hsb : Surjective b.left := representable_property_scheme_test
    (MorphismProperty.inverseImage @Surjective (Over.forget S)) hQ.flip hsw
  have comm : ∀ z : Q.left, schemePointMap w (a.left z) =
      schemePointMap p (b.left z) := by
    intro z
    rw [← schemePointMap_comp, ← schemePointMap_comp, hQ.w]
  refine ⟨Q, a, b, hQ, ha, hsa, hb, hsb, a.left.continuous,
    a.left.isOpenMap, b.left.continuous, b.left.isOpenMap, ?_, ?_⟩
  · intro x y hxy
    exact hlift x y (point_class_common_field w p x y hxy)
  · intro A
    have pre : a.left ⁻¹' (schemePointMap w ⁻¹' A) =
        b.left ⁻¹' (schemePointMap p ⁻¹' A) := by
      ext z
      exact (congrArg (fun t ↦ t ∈ A) (comm z)).to_iff
    have ia : a.left '' (b.left ⁻¹' (schemePointMap p ⁻¹' A)) =
        schemePointMap w ⁻¹' A := by
      rw [← pre, Set.image_preimage_eq _ a.left.surjective]
    have ib : b.left '' (a.left ⁻¹' (schemePointMap w ⁻¹' A)) =
        schemePointMap p ⁻¹' A := by
      rw [pre, Set.image_preimage_eq _ b.left.surjective]
    refine ⟨ia, ib, ?_⟩
    constructor
    · intro h
      rw [← ib]
      exact b.left.isOpenMap _ (h.preimage a.left.continuous)
    · intro h
      rw [← ia]
      exact a.left.isOpenMap _ (h.preimage b.left.continuous)

end AlgebraicGeometry.AlgebraicSpace
