/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import WeilConjectures.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.CategoryTheory.Limits.Yoneda

/-! # Flat locally finitely presented algebraic-space morphisms are universally open

Source: Stacks Project, Morphisms of Spaces, Tag 042S, lemma-fppf-open
(blueprint: lem-sfb-flat-lfp-space-universally-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

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

private theorem schemePointMap_continuous {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (a : yoneda.obj T ⟶ F) (ha : IsEtale a) : Continuous (schemePointMap a) := by
  rw [continuous_iff_coinduced_le]
  exact le_iSup_of_le T (le_iSup_of_le a (le_iSup_of_le ha le_rfl))

private theorem schemePointMap_open {S : Scheme.{u}} (F : AlgebraicSpace S)
    {T : Over S} (a : yoneda.obj T ⟶ F.obj.obj) (ha : IsEtale a) :
    IsOpenMap (schemePointMap a) := by
  obtain ⟨W, w, I, A, ι, _, _, _, _, _, hw, _, τ, hτ, _, hall⟩ :=
    exists_affine_etale_cover_and_point_topology F
  have heq : pointTopologicalSpace F.obj.obj = τ := by
    apply le_antisymm
    · exact iSup_le fun T ↦ iSup_le fun t ↦ iSup_le fun ht ↦
        (continuous_iff_coinduced_le.mp (hall T t).1)
    · rw [hτ]
      exact continuous_iff_coinduced_le.mp (schemePointMap_continuous w hw)
  change @IsOpenMap _ _ _ (pointTopologicalSpace F.obj.obj) _
  rw [heq]
  exact ((hall T a).2 ha).1

private theorem surjective_comp {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsSurjective f) (hg : IsSurjective g) : IsSurjective (f ≫ g) := by
  intro T a
  obtain ⟨V, p, q, hq, hp⟩ := hg T a
  obtain ⟨U, r, s, hs, hr⟩ := hf V q
  have : Surjective p.left := hp
  have : Surjective r.left := hr
  refine ⟨U, r ≫ p, s, ?_, (show Surjective (r.left ≫ p.left) by infer_instance)⟩
  simpa only [Functor.map_comp] using hs.paste_vert hq

private theorem surjective_scheme_test {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} {f : F ⟶ G} (hf : IsSurjective f)
    {U T : Over S} {p : U ⟶ T} {q : yoneda.obj U ⟶ F}
    {a : yoneda.obj T ⟶ G} (hq : IsPullback q (yoneda.map p) f a) :
    Surjective p.left := by
  obtain ⟨V, r, s, hs, hr⟩ := hf T a
  let e : U ≅ V := yoneda.preimageIso (hq.isoIsPullback _ _ hs)
  have he : e.hom ≫ r = p := by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, e, Functor.preimageIso_hom, Functor.map_preimage]
      using hq.isoIsPullback_hom_snd _ _ hs
  have : Surjective r.left := hr
  rw [← he]
  change Surjective (e.hom.left ≫ r.left)
  infer_instance

private theorem yoneda_etale_surjective {S : Scheme.{u}} {U V : Over S}
    (f : U ⟶ V) (hf : Etale f.left) (hs : Surjective f.left) :
    IsEtale (yoneda.map f) ∧ IsSurjective (yoneda.map f) := by
  have tests : ∀ (T : Over S) (a : yoneda.obj T ⟶ yoneda.obj V),
      ∃ (W : Over S) (p : W ⟶ T) (q : yoneda.obj W ⟶ yoneda.obj U),
        IsPullback q (yoneda.map p) (yoneda.map f) a ∧
          Etale p.left ∧ Surjective p.left := by
    intro T a
    let g := yoneda.preimage a
    let W := Limits.pullback f g
    let p : W ⟶ T := Limits.pullback.snd f g
    let q : W ⟶ U := Limits.pullback.fst f g
    have sq := IsPullback.of_hasPullback f g
    have sq' := (Over.forget S).map_isPullback sq
    refine ⟨W, p, yoneda.map q, ?_,
      MorphismProperty.of_isPullback sq' hf, MorphismProperty.of_isPullback sq' hs⟩
    simpa only [g, Functor.map_preimage] using yoneda.map_isPullback sq
  constructor
  · intro T a
    obtain ⟨W, p, q, hq, hp, _⟩ := tests T a
    exact ⟨W, p, q, hq, hp⟩
  · intro T a
    obtain ⟨W, p, q, hq, _, hp⟩ := tests T a
    exact ⟨W, p, q, hq, hp⟩

private theorem compatible_atlases {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    ∃ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ Y.obj.obj) (h : U ⟶ V),
      IsEtale a ∧ IsSurjective a ∧ IsEtale b ∧ IsSurjective b ∧
        a ≫ f.hom.hom = yoneda.map h ≫ b := by
  obtain ⟨U₀, a₀, ha₀, hsa₀⟩ := X.property.2
  obtain ⟨V, b, hb, hsb⟩ := Y.property.2
  obtain ⟨U, p, q, hq, hp⟩ := hb U₀ (a₀ ≫ f.hom.hom)
  have hsp : Surjective p.left := surjective_scheme_test hsb hq
  obtain ⟨hep, hsup⟩ := yoneda_etale_surjective p hp hsp
  refine ⟨U, V, yoneda.map p ≫ a₀, b, yoneda.preimage q,
    isEtale_comp _ _ hep ha₀, surjective_comp _ _ hsup hsa₀, hb, hsb, ?_⟩
  simpa only [Functor.map_preimage, Category.assoc] using hq.w.symm

-- Stacks, Morphisms of Spaces, Tag 03Z5: openness descends through a source atlas.
private theorem universallyOpen_of_atlas
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
    (b : yoneda.obj V ⟶ Y.obj.obj) (h : U ⟶ V)
    (ha : IsEtale a) (hsa : IsSurjective a)
    (hb : IsEtale b)
    (comm : a ≫ f.hom.hom = yoneda.map h ≫ b)
    (hh : UniversallyOpen h.left) : MapIsUniversallyOpen f := by
  intro Y' g
  let F := X.obj.obj
  let f₀ := f.hom.hom
  let g₀ := g.hom.hom
  let P := Limits.pullback f.hom g.hom
  let p := (Limits.pullback.snd f.hom g.hom).hom
  let q := (Limits.pullback.fst f.hom g.hom).hom
  have sqP : IsPullback q p f₀ g₀ :=
    (sheafToPresheaf _ _).map_isPullback (IsPullback.of_hasPullback f.hom g.hom)
  obtain ⟨W, w, hw, hsw⟩ := Y'.property.2
  obtain ⟨Z, zW, zV, sqZ, hzW⟩ := hb W (w ≫ g₀)
  let r : Z ⟶ V := yoneda.preimage zV
  have hr : yoneda.map r = zV := Functor.map_preimage _ _
  let T := Limits.pullback h r
  let tU : T ⟶ U := Limits.pullback.fst h r
  let tZ : T ⟶ Z := Limits.pullback.snd h r
  let k : T ⟶ W := tZ ≫ zW
  have sqT : IsPullback (yoneda.map tU) (yoneda.map tZ)
      (yoneda.map h) zV := by
    rw [← hr]
    exact yoneda.map_isPullback (IsPullback.of_hasPullback h r)
  have outer : IsPullback (yoneda.map tU) (yoneda.map k)
      (a ≫ f₀) (w ≫ g₀) := by
    rw [comm]
    simpa only [k, Functor.map_comp] using sqT.paste_vert sqZ
  let Q := Limits.pullback f₀ (w ≫ g₀)
  let qX : Q ⟶ F := Limits.pullback.fst _ _
  let qW : Q ⟶ yoneda.obj W := Limits.pullback.snd _ _
  have sqQ : IsPullback qX qW f₀ (w ≫ g₀) := IsPullback.of_hasPullback _ _
  let l₁ : yoneda.obj T ⟶ Q :=
    sqQ.lift (yoneda.map tU ≫ a) (yoneda.map k) (by
      simpa only [Category.assoc] using outer.w)
  have sq₁ : IsPullback (yoneda.map tU) l₁ a qX := by
    apply IsPullback.of_bot (v₂₁ := qW) _ (sqQ.lift_fst _ _ _).symm sqQ
    simpa only [l₁, IsPullback.lift_snd] using outer
  let l₂ : Q ⟶ P.obj := sqP.lift qX (qW ≫ w) (by
    simpa only [Category.assoc] using sqQ.w)
  have sq₂ : IsPullback qW l₂ w p := by
    apply IsPullback.of_bot (v₂₁ := q) _ (sqP.lift_snd _ _ _).symm sqP.flip
    simpa only [l₂, IsPullback.lift_fst] using sqQ.flip
  let c : yoneda.obj T ⟶ P.obj := l₁ ≫ l₂
  have hc : IsEtale c := isEtale_comp _ _
    (representableWith_baseChange _ sq₁ ha)
    (representableWith_baseChange _ sq₂ hw)
  have hsc : IsSurjective c := surjective_comp _ _
    (representableWith_baseChange _ sq₁ hsa)
    (representableWith_baseChange _ sq₂ hsw)
  have hs : IsPullback tU.left tZ.left h.left r.left :=
    (Over.forget S).map_isPullback (IsPullback.of_hasPullback h r)
  have : UniversallyOpen tZ.left := MorphismProperty.of_isPullback hs hh
  have : Etale zW.left := hzW
  have hk : IsOpenMap k.left := zW.left.isOpenMap.comp tZ.left.isOpenMap
  have hccomp : c ≫ p = yoneda.map k ≫ w := by
    change (l₁ ≫ l₂) ≫ p = _
    rw [Category.assoc, show l₂ ≫ p = qW ≫ w from sqP.lift_snd _ _ _,
      ← Category.assoc, show l₁ ≫ qW = yoneda.map k from sqQ.lift_snd _ _ _]
  have hcomp : mapPoint p ∘ schemePointMap c = schemePointMap w ∘ k.left := by
    funext x
    change schemePointMap (c ≫ p) x = _
    rw [hccomp, schemePointMap_comp]
    rfl
  apply IsOpenMap.of_comp (schemePointMap_continuous c hc)
    (schemePointMap_surjective c hsc)
  rw [hcomp]
  exact (schemePointMap_open Y' w hw).comp hk


private theorem mapPoint_comp {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (g : G ⟶ H) (x : Point F) :
    mapPoint (f ≫ g) x = mapPoint g (mapPoint f x) := by
  induction x using Quot.inductionOn with
  | h x => rfl

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

private theorem open_pointImage_of_universallyOpen
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : MapIsUniversallyOpen f) : IsOpen (pointImage f.hom.hom) := by
  let idY : Y.obj ⟶ Y.obj := (𝟙 Y : Y ⟶ Y).hom
  let p := Limits.pullback.snd f.hom idY
  let q := Limits.pullback.fst f.hom idY
  have hid : idY = 𝟙 Y.obj := rfl
  let i : X.obj ⟶ Limits.pullback f.hom idY :=
    Limits.pullback.lift (𝟙 X.obj) f.hom (by rw [hid]; simp)
  have hp : q.hom ≫ f.hom.hom = p.hom := by
    simpa [p, q, hid] using congrArg (fun k ↦ k.hom)
      (Limits.pullback.condition (f := f.hom) (g := idY))
  have hi : i.hom ≫ p.hom = f.hom.hom := by
    change (i ≫ p).hom = f.hom.hom
    simp [i, p]
  have hr : Set.range (mapPoint p.hom) = Set.range (mapPoint f.hom.hom) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨mapPoint q.hom x, ?_⟩
      rw [← mapPoint_comp, hp]
    · rintro ⟨x, rfl⟩
      refine ⟨mapPoint i.hom x, ?_⟩
      rw [← mapPoint_comp, hi]
  rw [pointImage_eq_range, ← hr]
  simpa only [Set.image_univ] using hf Y (𝟙 Y) Set.univ isOpen_univ

/-- A flat locally finitely presented morphism of algebraic spaces is universally open,
and its whole point image is open. No properness or quasi-compactness is assumed.
Source: Stacks, Morphisms of Spaces, Tag 042S, with Tags 03Z5 and 03H4
(blueprint: lem-sfb-flat-lfp-space-universally-open).
Proof: (1) Choose surjective étale scheme atlases `U₀ → X` and `V → Y` and form
`U = U₀ ×_Y V`, a scheme by the representable diagonal. By
[lem-trf-space-fibre-products-etale-covers] its projections give a surjective étale
atlas `p : U → X` and a compatible map `α : U → V`; composition of scheme-test
étale maps uses [lem-weil-pbc-etale-composition-cancellation](2).
(2) The two chart hypotheses make `α` flat and locally finitely presented, so
[lem-weil-pbc-flat-lfp-open] makes it universally open.
(3) For any algebraic-space base change `Y' → Y`, choose an atlas `W → Y'`.
Set `P = X ×_Y Y'`, `Z = V ×_Y W` and `T = U ×_V Z`. The fibre-product node
makes `Z,T` schemes and supplies a surjective étale atlas `a : T → P`, since
`T → P ×_Y' W` is the pullback of `p` and `P ×_Y' W → P` is the pullback of `W`.
(4) The map `T → Z` is a scheme base change of `α`, hence open. The map `Z → W`
is étale, hence open by [lem-weil-pbc-etale-morphism-open-map]. Thus `h : T → W`
is open.
(5) For open `O ⊆ |P|`, put `A = |a|⁻¹(O)`. Then
`|W → Y'|⁻¹(|P → Y'|(O)) = |h|(A)`: one inclusion is commutativity; for the
other, matching point classes lift to `P ×_Y' W` after a common field extension,
and then lift to `T` by surjectivity. This uses the point convention of
[lem-trf-space-fibre-products-etale-covers], without identifying the topological
fibre product with a fibre product of topological spaces.
(6) The right side is open, so the quotient topology of the atlas `W → Y'` makes
`|P → Y'|(O)` open. This proves universal openness. The identity base change and
`O = |X|` give the open whole image. The argument also covers empty spaces and opens. -/
theorem universallyOpen_of_flat_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : MapIsFlat f) (hlfp : MapIsLocallyOfFinitePresentation f) :
    MapIsUniversallyOpen f ∧ IsOpen (pointImage f.hom.hom) := by
  obtain ⟨U, V, a, b, h, ha, hsa, hb, _, comm⟩ := compatible_atlases f
  have : Flat h.left := hf U V a b h ha hb comm
  have : LocallyOfFinitePresentation h.left := hlfp U V a b h ha hb comm
  have hopen : MapIsUniversallyOpen f :=
    universallyOpen_of_atlas f U V a b h ha hsa hb comm inferInstance
  exact ⟨hopen, open_pointImage_of_universallyOpen f hopen⟩

end AlgebraicGeometry.AlgebraicSpace
