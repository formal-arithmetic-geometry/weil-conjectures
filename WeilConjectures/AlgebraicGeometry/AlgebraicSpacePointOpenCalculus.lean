/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.ProperCurveModuli
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Data.Quot

/-! # Point images and open subspaces of algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 03H4, 03H5, 03BX, 03BZ and 03IR
(blueprint: lem-a1-space-point-open-calculus).

The compatible-pair lifting clause expresses surjectivity onto the set-theoretic fibre
product without choosing a model of that set. The atlas clause supplies an actual open
scheme pullback square, with its underlying open identified by the point-image formula.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private theorem representative_rel_equivalence {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type u) : Equivalence (PointRepresentative.Rel (F := F)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact ⟨p.K, inferInstance, p.base, 𝟙 _, 𝟙 _, rfl⟩
  · rintro p q ⟨L, hL, s, a, b, h⟩
    exact ⟨L, hL, s, b, a, h.symm⟩
  · rintro p q r ⟨L, hL, s, a, b, h⟩ ⟨M, hM, t, c, d, k⟩
    let P := Limits.pullback b c
    let l : P ⟶ Over.mk s := Limits.pullback.fst b c
    let m : P ⟶ Over.mk t := Limits.pullback.snd b c
    have sq : IsPullback l.left m.left b.left c.left :=
      (IsPullback.of_hasPullback b c).map (Over.forget S)
    obtain ⟨v, _, _⟩ := Scheme.exists_preimage_of_isPullback sq
      (IsLocalRing.closedPoint L) (IsLocalRing.closedPoint M)
      (Subsingleton.elim (α := Spec (CommRingCat.of q.K)) _ _)
    let e : Over.mk (P.left.fromSpecResidueField v ≫ P.hom) ⟶ P :=
      Over.homMk (P.left.fromSpecResidueField v) rfl
    let l' := e ≫ l
    let m' := e ≫ m
    have hlm : l' ≫ b = m' ≫ c := by
      dsimp [l', m', l, m]
      rw [Category.assoc, Category.assoc, Limits.pullback.condition]
    refine ⟨P.left.residueField v, inferInstance,
      P.left.fromSpecResidueField v ≫ P.hom, l' ≫ a, m' ≫ d, ?_⟩
    calc
      F.map (l' ≫ a).op p.value = F.map l'.op (F.map a.op p.value) := by
        simp only [op_comp, F.map_comp, types_comp_apply]
      _ = F.map l'.op (F.map b.op q.value) := congrArg (F.map l'.op) h
      _ = F.map (l' ≫ b).op q.value := by simp only [op_comp, F.map_comp, types_comp_apply]
      _ = F.map (m' ≫ c).op q.value := by rw [hlm]
      _ = F.map m'.op (F.map c.op q.value) := by simp only [op_comp, F.map_comp, types_comp_apply]
      _ = F.map m'.op (F.map d.op r.value) := congrArg (F.map m'.op) k
      _ = F.map (m' ≫ d).op r.value := by simp only [op_comp, F.map_comp, types_comp_apply]

private theorem common_field_of_eq {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (p q : PointRepresentative F)
    (h : Quot.mk PointRepresentative.Rel p = Quot.mk PointRepresentative.Rel q) :
    p.Rel q :=
  (representative_rel_equivalence F).eqvGen_iff.mp (Quot.eq.mp h)

private theorem pointImage_eq_range {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    pointImage f = Set.range (mapPoint f) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Quot.mk _ a, rfl⟩
  · rintro ⟨a, rfl⟩
    induction a using Quot.inductionOn with
    | h a => exact ⟨a, rfl⟩

private theorem mapPoint_comp {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (g : G ⟶ H) (x : Point F) :
    mapPoint (f ≫ g) x = mapPoint g (mapPoint f x) := by
  induction x using Quot.inductionOn with
  | h x => rfl

private theorem point_pullback_lift {S : Scheme.{u}}
    {P F G H : (Over S)ᵒᵖ ⥤ Type u} {l : P ⟶ F} {r : P ⟶ G}
    {f : F ⟶ H} {g : G ⟶ H} (sq : IsPullback l r f g)
    (x : Point F) (y : Point G) (h : mapPoint f x = mapPoint g y) :
    ∃ z : Point P, mapPoint l z = x ∧ mapPoint r z = y := by
  induction x using Quot.inductionOn with
  | h x =>
    induction y using Quot.inductionOn with
    | h y =>
      obtain ⟨L, hL, s, a, b, hab⟩ := common_field_of_eq (x.map f) (y.map g) h
      let x' : yoneda.obj (Over.mk s) ⟶ F := yonedaEquiv.symm (F.map a.op x.value)
      let y' : yoneda.obj (Over.mk s) ⟶ G := yonedaEquiv.symm (G.map b.op y.value)
      have comm : x' ≫ f = y' ≫ g := by
        apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_comp]
        simpa only [x', y', Equiv.apply_symm_apply, NatTrans.naturality_apply,
          PointRepresentative.map] using hab
      let z' := sq.lift x' y' comm
      let z : PointRepresentative P := ⟨L, s, yonedaEquiv z'⟩
      refine ⟨Quot.mk _ z, ?_, ?_⟩
      · apply Quot.sound
        refine ⟨L, hL, s, 𝟙 _, a, ?_⟩
        change F.map (𝟙 _).op (l.app _ (yonedaEquiv z')) = F.map a.op x.value
        rw [op_id, F.map_id]
        simpa only [yonedaEquiv_comp, x', Equiv.apply_symm_apply, types_id_apply]
          using congrArg yonedaEquiv (sq.lift_fst x' y' comm)
      · apply Quot.sound
        refine ⟨L, hL, s, 𝟙 _, b, ?_⟩
        change G.map (𝟙 _).op (r.app _ (yonedaEquiv z')) = G.map b.op y.value
        rw [op_id, G.map_id]
        simpa only [yonedaEquiv_comp, y', Equiv.apply_symm_apply, types_id_apply]
          using congrArg yonedaEquiv (sq.lift_snd x' y' comm)

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

private theorem scheme_points_bijective {S : Scheme.{u}} (T : Over S) :
    Function.Bijective (schemePointMap (𝟙 (yoneda.obj T))) := by
  constructor
  · intro x y h
    obtain ⟨L, hL, s, a, b, hab⟩ := common_field_of_eq _ _ h
    have hv := congrArg (fun k : Over.mk s ⟶ T ↦ k.left (IsLocalRing.closedPoint L)) hab
    change (a.left ≫ T.left.fromSpecResidueField x) (IsLocalRing.closedPoint L) =
      (b.left ≫ T.left.fromSpecResidueField y) (IsLocalRing.closedPoint L) at hv
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hv
    exact (T.left.fromSpecResidueField_apply x _).symm.trans
      (hv.trans (T.left.fromSpecResidueField_apply y _))
  · intro x
    induction x using Quot.inductionOn with
    | h x =>
      let t : T.left := x.value.left (IsLocalRing.closedPoint x.K)
      refine ⟨t, ?_⟩
      let e := Spec.map (T.left.descResidueField (Scheme.stalkClosedPointTo x.value.left))
      have he : e ≫ T.left.fromSpecResidueField t = x.value.left :=
        Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField x.K T.left _
      let r : Over.mk x.base ⟶ Over.mk (T.left.fromSpecResidueField t ≫ T.hom) :=
        Over.homMk e (by
          change e ≫ (T.left.fromSpecResidueField t ≫ T.hom) = x.base
          rw [← Category.assoc, he]
          exact Over.w x.value)
      apply Quot.sound
      refine ⟨x.K, inferInstance, x.base, r, 𝟙 _, ?_⟩
      change r ≫ Over.homMk (T.left.fromSpecResidueField t) rfl = 𝟙 _ ≫ x.value
      apply Over.OverMorphism.ext
      change e ≫ T.left.fromSpecResidueField t = (𝟙 _ ≫ x.value).left
      simpa only [Category.id_comp] using he

private theorem schemePointMap_surjective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (a : yoneda.obj T ⟶ F) (ha : IsSurjective a) :
    Function.Surjective (schemePointMap a) := by
  intro x
  induction x using Quot.inductionOn with
  | h x =>
    let t : yoneda.obj (Over.mk x.base) ⟶ F := yonedaEquiv.symm x.value
    obtain ⟨V, p, q, hq, hp⟩ := ha (Over.mk x.base) t
    have : Surjective p.left := hp
    obtain ⟨v, _⟩ := p.left.surjective (IsLocalRing.closedPoint x.K)
    refine ⟨(yoneda.preimage q).left v, ?_⟩
    rw [← schemePointMap_comp, Functor.map_preimage, hq.w]
    apply Quot.sound
    let r : Over.mk (V.left.fromSpecResidueField v ≫ V.hom) ⟶ Over.mk x.base :=
      Over.homMk (V.left.fromSpecResidueField v ≫ p.left) (by
        change (V.left.fromSpecResidueField v ≫ p.left) ≫ (Over.mk x.base).hom =
          V.left.fromSpecResidueField v ≫ V.hom
        rw [Category.assoc, Over.w p])
    refine ⟨V.left.residueField v, inferInstance,
      V.left.fromSpecResidueField v ≫ V.hom, 𝟙 _, r, ?_⟩
    dsimp only [PointRepresentative.value]
    rw [CategoryTheory.op_id, F.map_id]
    change t.app _ ((Over.homMk _ rfl) ≫ p) = F.map r.op x.value
    rw [yonedaEquiv_symm_app_apply]
    rfl

private theorem scheme_test_image {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} {V T : Over S}
    {q : yoneda.obj V ⟶ F} {i : V ⟶ T} {f : F ⟶ G} {a : yoneda.obj T ⟶ G}
    (sq : IsPullback q (yoneda.map i) f a) :
    schemePointMap a ⁻¹' pointImage f = Set.range i.left := by
  ext x
  rw [pointImage_eq_range]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, _, hz⟩ := point_pullback_lift sq y
      (schemePointMap (𝟙 (yoneda.obj T)) x) hy
    obtain ⟨v, rfl⟩ := (scheme_points_bijective V).2 z
    have hv : schemePointMap (𝟙 (yoneda.obj T)) (i.left v) =
        schemePointMap (𝟙 (yoneda.obj T)) x := by
      rw [← schemePointMap_comp]
      exact hz
    exact ⟨v, (scheme_points_bijective T).1 hv⟩
  · rintro ⟨v, rfl⟩
    refine ⟨schemePointMap q v, ?_⟩
    change schemePointMap (q ≫ f) v = _
    rw [sq.w, schemePointMap_comp]

private theorem surjective_iff_point_surjective {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (hf : IsRepresentable f) :
    IsSurjective f ↔ Function.Surjective (mapPoint f) := by
  constructor
  · intro hs y
    induction y using Quot.inductionOn with
    | h y =>
      let a : yoneda.obj (Over.mk y.base) ⟶ G := yonedaEquiv.symm y.value
      obtain ⟨V, i, q, sq, hi⟩ := hs (Over.mk y.base) a
      have : Surjective i.left := hi
      obtain ⟨v, _⟩ := i.left.surjective (IsLocalRing.closedPoint y.K)
      refine ⟨schemePointMap q v, ?_⟩
      change schemePointMap (q ≫ f) v = _
      rw [sq.w]
      apply Quot.sound
      let r : Over.mk (V.left.fromSpecResidueField v ≫ V.hom) ⟶ Over.mk y.base :=
        Over.homMk (V.left.fromSpecResidueField v ≫ i.left) (by
          change (V.left.fromSpecResidueField v ≫ i.left) ≫ (Over.mk y.base).hom =
            V.left.fromSpecResidueField v ≫ V.hom
          rw [Category.assoc, Over.w])
      refine ⟨V.left.residueField v, inferInstance,
        V.left.fromSpecResidueField v ≫ V.hom, 𝟙 _, r, ?_⟩
      dsimp only [PointRepresentative.value]
      rw [op_id, G.map_id]
      change a.app _ ((Over.homMk _ rfl) ≫ i) = G.map r.op y.value
      rw [yonedaEquiv_symm_app_apply]
      rfl
  · intro hs T a
    obtain ⟨V, i, q, sq, _⟩ := hf T a
    refine ⟨V, i, q, sq, ⟨?_⟩⟩
    intro x
    have hx : x ∈ schemePointMap a ⁻¹' pointImage f := by
      rw [pointImage_eq_range]
      exact hs _
    rwa [scheme_test_image sq] at hx

private theorem representableWith_baseChange {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) {A B C D : (Over S)ᵒᵖ ⥤ Type u}
    {q : D ⟶ A} {p : D ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (sq : IsPullback q p f g) (hf : IsRepresentableWith P f) :
    IsRepresentableWith P p := by
  intro T a
  obtain ⟨U, r, b, hb, hr⟩ := hf T (a ≫ g)
  let l := sq.lift b (yoneda.map r ≫ a) (by simpa only [Category.assoc] using hb.w)
  refine ⟨U, r, l, ?_, hr⟩
  apply IsPullback.of_right (h₁₂ := q) (h₂₂ := g) _ (sq.lift_snd _ _ _) sq
  simpa only [l, IsPullback.lift_fst] using hb

private theorem schemePointMap_continuous {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (a : yoneda.obj T ⟶ F) (ha : IsEtale a) : Continuous (schemePointMap a) := by
  rw [continuous_iff_coinduced_le]
  exact le_iSup_of_le T (le_iSup_of_le a (le_iSup_of_le ha le_rfl))

private theorem schemePointMap_topology {S : Scheme.{u}} (B : AlgebraicSpace S) :
    ∀ (T : Over S) (a : yoneda.obj T ⟶ B.obj.obj),
      Continuous (schemePointMap a) ∧ (IsEtale a → IsOpenMap (schemePointMap a)) := by
  obtain ⟨W, w, I, A, ι, _, _, _, _, _, hw, _, τ, hτ, _, hall⟩ :=
    exists_affine_etale_cover_and_point_topology B
  have heq : pointTopologicalSpace B.obj.obj = τ := by
    apply le_antisymm
    · exact iSup_le fun T ↦ iSup_le fun t ↦ iSup_le fun ht ↦
        (continuous_iff_coinduced_le.mp (hall T t).1)
    · rw [hτ]
      exact continuous_iff_coinduced_le.mp (schemePointMap_continuous w hw)
  intro T a
  rw [heq]
  exact ⟨(hall T a).1, fun ha ↦ ((hall T a).2 ha).1⟩

private theorem pointMap_continuous {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} (B : AlgebraicSpace S) (f : F ⟶ B.obj.obj) :
    Continuous (mapPoint f) := by
  apply continuous_iSup_dom.mpr
  intro T
  apply continuous_iSup_dom.mpr
  intro a
  apply continuous_iSup_dom.mpr
  intro ha
  apply continuous_coinduced_dom.mpr
  exact (schemePointMap_topology B T (a ≫ f)).1

private theorem pointMap_open {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} (B : AlgebraicSpace S) (f : F ⟶ B.obj.obj)
    (hf : IsEtale f) : IsOpenMap (mapPoint f) := by
  obtain ⟨W, w, hw, hsw⟩ := B.property.2
  obtain ⟨V, i, q, sq, hi⟩ := hf W w
  have hq : IsEtale q := representableWith_baseChange _ sq.flip hw
  have hsq : IsSurjective q := representableWith_baseChange _ sq.flip hsw
  have : Etale i.left := hi
  apply IsOpenMap.of_comp (schemePointMap_continuous q hq)
    (schemePointMap_surjective q hsq)
  have comm : mapPoint f ∘ schemePointMap q = schemePointMap w ∘ i.left := by
    funext x
    change schemePointMap (q ≫ f) x = _
    rw [sq.w, schemePointMap_comp]
    rfl
  rw [comm]
  exact ((schemePointMap_topology B W w).2 hw).comp i.left.isOpenMap

private theorem subfunctor_points_injective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} (J : Subfunctor F) :
    Function.Injective (mapPoint J.ι) := by
  intro x y h
  induction x using Quot.inductionOn with
  | h x =>
    induction y using Quot.inductionOn with
    | h y =>
      obtain ⟨L, hL, s, a, b, hab⟩ := common_field_of_eq (x.map J.ι) (y.map J.ι) h
      apply Quot.sound
      refine ⟨L, hL, s, a, b, ?_⟩
      exact Subtype.ext hab

private theorem subfunctor_le_of_pointImage_subset {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} (J₁ J₂ : Subfunctor F)
    (hJ₂ : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) J₂.ι)
    (h : pointImage J₁.ι ⊆ pointImage J₂.ι) : J₁ ≤ J₂ := by
  intro T b hb
  let a : yoneda.obj T.unop ⟶ J₁.toFunctor := yonedaEquiv.symm ⟨b, hb⟩
  obtain ⟨V, i, q, sq, hi⟩ := hJ₂ T.unop (a ≫ J₁.ι)
  have hs : Function.Surjective i.left := by
    intro x
    have hx : schemePointMap (a ≫ J₁.ι) x ∈ pointImage J₂.ι := by
      apply h
      rw [pointImage_eq_range]
      exact ⟨schemePointMap a x, rfl⟩
    have hx' : x ∈ schemePointMap (a ≫ J₁.ι) ⁻¹' pointImage J₂.ι := hx
    rwa [scheme_test_image sq] at hx'
  have : IsOpenImmersion i.left := hi
  have : IsIso i.left := isIso_of_isOpenImmersion_of_opensRange_eq_top i.left
    (TopologicalSpace.Opens.ext (Set.range_eq_univ.mpr hs))
  have : IsIso ((Over.forget S).map i) := (show IsIso i.left from inferInstance)
  have : IsIso i := isIso_of_reflects_iso i (Over.forget S)
  have hh : (yoneda.map (inv i) ≫ q) ≫ J₂.ι = a ≫ J₁.ι := by
    rw [Category.assoc, sq.w, ← Category.assoc, ← Functor.map_comp]
    simp
  have hv := congrArg yonedaEquiv hh
  simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map, a, Equiv.apply_symm_apply] at hv
  change (q.app T (inv i)).val = b at hv
  rw [← hv]
  exact (q.app T (inv i)).property

private theorem pointImage_mono {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {J₁ J₂ : Subfunctor F} (h : J₁ ≤ J₂) :
    pointImage J₁.ι ⊆ pointImage J₂.ι := by
  rw [pointImage_eq_range, pointImage_eq_range]
  rintro _ ⟨x, rfl⟩
  refine ⟨mapPoint (Subfunctor.homOfLe h) x, ?_⟩
  rw [← mapPoint_comp, Subfunctor.homOfLe_ι]


/-- Point images commute with fibre products, representable surjectivity is detected on
points, morphisms are continuous, representable étale morphisms are open, and open
subspaces embed openly on points and have their subfunctor order detected on points.
Source: Stacks Project, Properties of Spaces, Tags 03H4, 03H5, 03BX, 03BZ and 03IR
(blueprint: lem-a1-space-point-open-calculus).

Proof:
1. The common-field relation is an equivalence: reflexivity and symmetry are immediate;
   for transitivity, take a point of the scheme pullback of the two common fields over
   the middle field, and restrict to its residue field. Thus equality in `Quot` gives
   actual common-field agreement. Scheme points correspond bijectively to point classes
   of their Yoneda functors, by factorization through the residue field.
2. In any presheaf pullback square, common-field agreement of the two images gives
   compatible Yoneda maps over that field. The pullback lift gives a point projecting
   to both original classes. Applied to the sheaf pullback square, this gives the first
   clause; commutativity and the lift give the projection-image formula.
3. On a representable scheme test, this same lifting result identifies the image of the
   scheme projection with the inverse image of the point image. Consequently point
   surjectivity implies surjectivity on every scheme test. Conversely, a surjective test
   over a field spectrum has a point; its residue-field representative lifts that class.
4. The topology supplied by lem-a1-space-affine-etale-cover equals the final topology:
   every etale test is continuous for the former, and the atlas is itself a test for the
   latter. Its scheme-source continuity assertion and the final-topology criterion then
   give continuity of every presheaf map to an algebraic space.
5. Pull a representable etale map back along a surjective etale atlas of its target.
   The resulting scheme projection is etale, and the other side is representable etale
   and surjective by pullback pasting. On points that side is continuous and surjective.
   The composite to the target is open, as the composite of the etale scheme projection
   and the atlas point map. Openness descends along the continuous surjection.
6. An open-subfunctor inclusion is representable etale by its scheme-test definition.
   It is injective on point classes: common-field equality in the ambient functor is
   already equality in the subfunctor. Steps 4 and 5 therefore give its open embedding.
   Its representing open-immersion square has the asserted point image by step 3.
7. Subfunctor inclusion gives point-image inclusion by composition. Conversely, test a
   section of the first subfunctor against the second open subfunctor. The representing
   open immersion is point-surjective by step 3, so it is an isomorphism; its inverse
   lifts the section. This proves subfunctor inclusion on every scheme. Apply the same
   argument to the full subfunctor to obtain the final full-image assertion. -/
theorem point_open_calculus {S : Scheme.{u}} :
    (∀ (A B C : AlgebraicSpace S) (a : A ⟶ B) (c : C ⟶ B),
      (∀ (x : Point A.obj.obj) (z : Point C.obj.obj),
        mapPoint a.hom.hom x = mapPoint c.hom.hom z →
          ∃ t : Point (Limits.pullback a.hom c.hom).obj,
            mapPoint (Limits.pullback.fst a.hom c.hom).hom t = x ∧
            mapPoint (Limits.pullback.snd a.hom c.hom).hom t = z) ∧
      pointImage (Limits.pullback.snd a.hom c.hom).hom =
        mapPoint c.hom.hom ⁻¹' pointImage a.hom.hom) ∧
    (∀ (A B : AlgebraicSpace S) (a : A ⟶ B), IsRepresentable a.hom.hom →
      (IsSurjective a.hom.hom ↔ Function.Surjective (mapPoint a.hom.hom))) ∧
    (∀ (A B : AlgebraicSpace S) (a : A ⟶ B), Continuous (mapPoint a.hom.hom)) ∧
    (∀ (A B : AlgebraicSpace S) (a : A ⟶ B), IsEtale a.hom.hom →
      IsOpenMap (mapPoint a.hom.hom)) ∧
    (∀ (B : AlgebraicSpace S) (J : OpenSubspace B),
      Topology.IsOpenEmbedding (mapPoint J.val.ι) ∧
      ∀ (U : Over S) (p : yoneda.obj U ⟶ B.obj.obj), IsEtale p → IsSurjective p →
        ∃ (V : Over S) (i : V ⟶ U) (q : yoneda.obj V ⟶ J.val.toFunctor),
          IsPullback q (yoneda.map i) J.val.ι p ∧ IsOpenImmersion i.left ∧
          schemePointMap p ⁻¹' pointImage J.val.ι = Set.range i.left) ∧
    (∀ (B : AlgebraicSpace S) (J₁ J₂ : OpenSubspace B),
      pointImage J₁.val.ι ⊆ pointImage J₂.val.ι ↔ J₁.val ≤ J₂.val) ∧
    (∀ (B : AlgebraicSpace S) (J : OpenSubspace B),
      pointImage J.val.ι = Set.univ → J.val = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B C a c
    have sq : IsPullback (Limits.pullback.fst a.hom c.hom).hom
        (Limits.pullback.snd a.hom c.hom).hom a.hom.hom c.hom.hom :=
      (sheafToPresheaf _ _).map_isPullback (IsPullback.of_hasPullback a.hom c.hom)
    refine ⟨point_pullback_lift sq, ?_⟩
    rw [pointImage_eq_range, pointImage_eq_range]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨mapPoint (Limits.pullback.fst a.hom c.hom).hom t, ?_⟩
      rw [← mapPoint_comp, ← mapPoint_comp, sq.w]
    · rintro ⟨x, hx⟩
      obtain ⟨t, _, ht⟩ := point_pullback_lift sq x z hx
      exact ⟨t, ht⟩
  · intro A B a ha
    exact surjective_iff_point_surjective a.hom.hom ha
  · intro A B a
    exact pointMap_continuous B a.hom.hom
  · intro A B a ha
    exact pointMap_open B a.hom.hom ha
  · intro B J
    have he : IsEtale J.val.ι := by
      intro T a
      obtain ⟨V, i, q, sq, hi⟩ := J.property T a
      have : IsOpenImmersion i.left := hi
      exact ⟨V, i, q, sq, inferInstance⟩
    refine ⟨Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (pointMap_continuous B J.val.ι) (subfunctor_points_injective J.val)
      (pointMap_open B J.val.ι he), ?_⟩
    intro U p _ _
    obtain ⟨V, i, q, sq, hi⟩ := J.property U p
    exact ⟨V, i, q, sq, hi, scheme_test_image sq⟩
  · intro B J₁ J₂
    exact ⟨subfunctor_le_of_pointImage_subset J₁.val J₂.val J₂.property,
      pointImage_mono⟩
  · intro B J h
    apply le_antisymm le_top
    apply subfunctor_le_of_pointImage_subset ⊤ J.val J.property
    rw [h]
    exact Set.subset_univ _

end AlgebraicGeometry.AlgebraicSpace
