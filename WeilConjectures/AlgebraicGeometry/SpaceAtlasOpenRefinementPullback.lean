/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointClasses
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Open refinement of a prescribed algebraic-space atlas

Source: Stacks Project, Properties of Spaces, Tag 03FX, proof of
lemma-cover-by-union-affines; point classes: Tags 03BU and 03BV
(blueprint: lem-a1-space-atlas-open-refinement-pullback).

A pullback square of presheaves states that the canonical coproduct comparison is an
isomorphism. Representable presheaves and the algebraic space are fppf sheaves, so this
also gives the claimed isomorphism of sheaves, with the prescribed projections.
-/

@[expose] public section

universe u v

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private noncomputable def over_coproduct_isColimit {S : Scheme.{u}} {I : Type v}
    [Small.{u} I] (U : I → Over S) :
    IsColimit (Cofan.mk (∐ U).left (fun i ↦ (Sigma.ι U i).left)) :=
  (isColimitMapCoconeCofanMkEquiv (Over.forget S) _ _).1
    (isColimitOfPreserves (Over.forget S) (coproductIsCoproduct U))

private theorem coproduct_geometry {I : Type v} [Small.{u} I] (U : I → Scheme.{u})
    (C : Scheme.{u}) (k : ∀ i, U i ⟶ C) (hc : IsColimit (Cofan.mk C k)) :
    (∀ i, IsOpenImmersion (k i)) ∧ (∀ x : C, ∃ i y, k i y = x) ∧
    (∀ i j, i ≠ j → ∀ x y, k i x ≠ k j y) := by
  let e : (∐ U) ≅ C := (coproductIsCoproduct U).coconePointUniqueUpToIso hc
  have hk (i : I) : Sigma.ι U i ≫ e.hom = k i :=
    (coproductIsCoproduct U).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [← hk]
    infer_instance
  · intro x
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover U).exists_eq (e.inv x)
    change (Sigma.ι U i) y = e.inv x at hy
    refine ⟨i, y, ?_⟩
    rw [← hk, Scheme.Hom.comp_apply, hy]
    exact congrArg (fun f : C ⟶ C ↦ f x) e.inv_hom_id
  · intro i j hij x y hxy
    have h := congrArg (fun z ↦ e.inv z) hxy
    simp only [← hk, ← Scheme.Hom.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
    exact hij (congrArg Sigma.fst ((sigmaι_eq_iff U i j x y).mp h))

private theorem over_sigma_property {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    {U : I → Over S} {T : Over S} (f : ∀ i, U i ⟶ T)
    (hf : ∀ i, P (f i).left) : P (Sigma.desc f).left := by
  let hc := over_coproduct_isColimit U
  let e : (∐ fun i ↦ (U i).left) ≅ (∐ U).left :=
    (coproductIsCoproduct _).coconePointUniqueUpToIso hc
  have he : e.hom ≫ (Sigma.desc f).left = Sigma.desc (fun i ↦ (f i).left) := by
    apply Sigma.hom_ext
    intro i
    have hk : Sigma.ι (fun i ↦ (U i).left) i ≫ e.hom = (Sigma.ι U i).left :=
      (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
    rw [← Category.assoc, hk]
    change (Sigma.ι U i ≫ Sigma.desc f).left = _
    simp
  have h := IsZariskiLocalAtSource.sigmaDesc (P := P) hf
  rw [← he] at h
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mp h

private theorem property_of_scheme_test {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {G F : (Over S)ᵒᵖ ⥤ Type u} {f : G ⟶ F}
    (hf : IsRepresentableWith (P.inverseImage (Over.forget S)) f)
    {T U : Over S} {a : yoneda.obj T ⟶ F} {p : U ⟶ T}
    {q : yoneda.obj U ⟶ G} (h : IsPullback q (yoneda.map p) f a) : P p.left := by
  obtain ⟨V, r, b, hb, hr⟩ := hf T a
  let e : U ≅ V := yoneda.preimageIso (h.isoIsPullback _ _ hb)
  have he : e.hom ≫ r = p := by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, e, Functor.preimageIso_hom, Functor.map_preimage] using
      h.isoIsPullback_hom_snd _ _ hb
  have hP : P (e.hom.left ≫ r.left) :=
    MorphismProperty.RespectsIso.precomp P e.hom.left r.left hr
  simpa only [← Over.comp_left, he] using hP

private theorem over_sigma_pullback {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {P V : Over S} (a : P ⟶ V) (U : I → Over S) (j : ∀ i, U i ⟶ V) :
    IsPullback
      (Sigma.desc (fun i ↦ pullback.snd a (j i) ≫ Sigma.ι U i))
      (Sigma.desc (fun i ↦ pullback.fst a (j i))) (Sigma.desc j) a := by
  let r := Sigma.desc j
  let Q := Limits.pullback a r
  let D := fun i ↦ Limits.pullback a (j i)
  let l (i : I) : D i ⟶ Q := pullback.lift (pullback.fst a (j i))
    (pullback.snd a (j i) ≫ Sigma.ι U i) (by simp [r, pullback.condition])
  have hl (i : I) : IsPullback (l i) (pullback.snd a (j i))
      (pullback.snd a r) (Sigma.ι U i) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback a r)
    · simpa only [l, pullback.lift_fst, r, Sigma.ι_desc] using
        (IsPullback.of_hasPullback a (j i))
    · simp [l, r]
  have hg := coproduct_geometry (fun i ↦ (U i).left) (∐ U).left
    (fun i ↦ (Sigma.ι U i).left) (over_coproduct_isColimit U)
  have hop (i : I) : IsOpenImmersion (l i).left :=
    MorphismProperty.of_isPullback ((hl i).flip.map (Over.forget S)) (hg.1 i)
  have hcov : ∀ x : Q.left, ∃ i y, (l i).left y = x := by
    intro x
    obtain ⟨i, y, hy⟩ := hg.2.1 ((pullback.snd a r).left x)
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
      ((hl i).map (Over.forget S)) x y hy.symm
    exact ⟨i, z, hz⟩
  have hd : ∀ i k, i ≠ k → ∀ x y, (l i).left x ≠ (l k).left y := by
    intro i k hik x y hxy
    apply hg.2.2 i k hik ((pullback.snd a (j i)).left x)
      ((pullback.snd a (j k)).left y)
    have hi := congrArg (fun f : D i ⟶ ∐ U ↦ f.left x) (hl i).w
    have hk := congrArg (fun f : D k ⟶ ∐ U ↦ f.left y) (hl k).w
    exact hi.symm.trans ((congrArg (fun z ↦ (pullback.snd a r).left z) hxy).trans hk)
  let : ∀ i, IsOpenImmersion (l i).left := hop
  have hcQ : IsColimit (Cofan.mk Q.left (fun i ↦ (l i).left)) := by
    apply Nonempty.some
    apply nonempty_isColimit_cofanMk_of
    · refine le_antisymm le_top ?_
      intro x _
      change x ∈ ⨆ i, (l i).left.opensRange
      rw [TopologicalSpace.Opens.mem_iSup]
      obtain ⟨i, y, hy⟩ := hcov x
      exact ⟨i, y, hy⟩
    · intro i k hik
      apply disjoint_iff.mpr
      apply le_antisymm ?_ bot_le
      rintro x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
      exact hd i k hik y z (hy.trans hz.symm)
  let hcD := over_coproduct_isColimit D
  let e : (∐ D).left ≅ Q.left := hcD.coconePointUniqueUpToIso hcQ
  have he : (Sigma.desc l).left = e.hom := by
    apply Cofan.IsColimit.hom_ext hcD
    intro i
    change (Sigma.ι D i ≫ Sigma.desc l).left = _
    rw [Sigma.ι_desc]
    exact (hcD.comp_coconePointUniqueUpToIso_hom hcQ ⟨i⟩).symm
  have : IsIso (Sigma.desc l).left := he ▸ inferInstance
  have : IsIso ((Over.forget S).map (Sigma.desc l)) := ‹IsIso (Sigma.desc l).left›
  have : IsIso (Sigma.desc l) := isIso_of_reflects_iso (Sigma.desc l) (Over.forget S)
  apply IsPullback.flip
  refine IsPullback.of_iso_pullback ?_ (asIso (Sigma.desc l)) ?_ ?_
  · constructor
    apply Sigma.hom_ext
    intro i
    simp [pullback.condition]
  · apply Sigma.hom_ext
    intro i
    simp [l, r]
  · apply Sigma.hom_ext
    intro i
    simp [l, r]

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

/-- Any open covering refines a prescribed atlas, with the coproduct of the pulled-back
opens representing every scheme test. An affine such covering can be chosen over affine
opens of the base.
Source: Stacks, Tag 03FX (blueprint: lem-a1-space-atlas-open-refinement-pullback).

Proof:
1. For T → E, represent T ×_E V by P using def-trf-algebraic-space. Its projection
   P → T is surjective étale. By def-pc-fibre-product and
   lem-weil-pbc-open-fibre-product, P ×_V U_i → P is the inverse-image open of U_i;
   these opens cover P. Form their coproduct using lem-weil-pbc-scheme-coproduct-family.
   Its maps to T and to the chart coproduct agree over E: equality can be checked on
   its component Zariski cover, which is fppf by lem-pc-zariski-coverings-are-fppf.
2. Given a test Z and compatible maps Z → T and Z → W, the inverse images of the
   disjoint open components of W partition Z. Factor the map to W on each piece
   through U_i by lem-weil-pbc-morphism-factors-through-open-subscheme. The two
   pullback universal properties give a map to P ×_V U_i. Glue these component maps
   by lem-weil-pbc-scheme-morphism-gluing. Pullback uniqueness and gluing uniqueness
   show that this is inverse to the comparison and natural in Z. This proves the
   displayed IsPullback, including its actual coproduct projection maps.
3. By lem-weil-pbc-etale-composition-cancellation the component projections to T
   are étale; lem-weil-pbc-etale-local-on-source makes their coproduct projection
   étale. Lift a point of T to P, then to a covering open, to prove surjectivity.
   These squares on all scheme tests give representability, surjectivity and
   étaleness of the refined atlas by def-trf-algebraic-space.
4. Represent a point class by Spec K → E. Its scheme-test pullback is surjective
   over the one-point scheme Spec K, hence has a point z. Use its residue field and
   lem-weil-pbc-morphism-from-spec-field to obtain a point of W whose image agrees
   with the original class over κ(z). The same lemma factors that field-valued
   point through the residue field of its image in W. Thus schemePointMap is
   surjective, by def-a1-algebraic-space-point-classes, without a K-rational lift.
5. For each point v of V choose an affine open of S around its image, and then an
   affine open of V around v inside its inverse image, by
   lem-weil-pbc-affine-opens-basis twice. The structural map factors through the
   chosen base open by lem-weil-pbc-morphism-factors-through-open-subscheme.
   Index by the points of V, as allowed by def-weil-size-convention. If V is empty
   take the empty family. An empty prescribed covering forces V and P empty;
   surjectivity of P → T forces T empty. All coproducts, gluing and source-local
   étaleness above therefore still apply to the empty family. -/
theorem space_atlas_open_refinement_pullback {S : Scheme.{u}} (E : AlgebraicSpace S)
    (V : Over S) (p : yoneda.obj V ⟶ E.obj.obj)
    (hp : IsRepresentable p) (hpEt : IsEtale p) (hpSurj : IsSurjective p) :
    (∀ (I : Type v) [Small.{u} I] (U : I → Over S) (j : ∀ i : I, U i ⟶ V),
      (∀ i : I, IsOpenImmersion (j i).left) →
      (∀ x : V.left, ∃ (i : I) (y : (U i).left), (j i).left y = x) →
      (∀ (T : Over S) (t : yoneda.obj T ⟶ E.obj.obj),
        ∃ (P : Over S) (q : P ⟶ T) (a : P ⟶ V),
          IsPullback (yoneda.map a) (yoneda.map q) p t ∧
          (∀ i : I, IsOpenImmersion (pullback.fst a (j i)).left) ∧
          (∀ x : P.left, ∃ (i : I) (y : (Limits.pullback a (j i)).left),
            (pullback.fst a (j i)).left y = x) ∧
          IsPullback
            (yoneda.map (Sigma.desc (fun i : I ↦
              pullback.snd a (j i) ≫ Sigma.ι U i)))
            (yoneda.map (Sigma.desc (fun i : I ↦ pullback.fst a (j i) ≫ q)))
            (yoneda.map (Sigma.desc j) ≫ p) t ∧
          Surjective (Sigma.desc (fun i : I ↦ pullback.fst a (j i) ≫ q)).left ∧
          Etale (Sigma.desc (fun i : I ↦ pullback.fst a (j i) ≫ q)).left) ∧
      IsRepresentable (yoneda.map (Sigma.desc j) ≫ p) ∧
      IsSurjective (yoneda.map (Sigma.desc j) ≫ p) ∧
      IsEtale (yoneda.map (Sigma.desc j) ≫ p) ∧
      Function.Surjective (schemePointMap (yoneda.map (Sigma.desc j) ≫ p))) ∧
    ∃ (I : Type u) (U : I → Over S) (j : ∀ i : I, U i ⟶ V),
      (∀ i : I, IsOpenImmersion (j i).left) ∧
      (∀ x : V.left, ∃ (i : I) (y : (U i).left), (j i).left y = x) ∧
      (∀ i : I, IsAffine (U i).left) ∧
      (∀ i : I, ∃ (B : S.Opens) (_ : IsAffineOpen B) (b : (U i).left ⟶ B.toScheme),
        b ≫ B.ι = (U i).hom) := by
  classical
  -- First form the coproduct pullback entirely in schemes and paste with the atlas square.
  constructor
  · intro I _ U j hj hcover
    have htests (T : Over S) (t : yoneda.obj T ⟶ E.obj.obj) :
        ∃ (P : Over S) (q : P ⟶ T) (a : P ⟶ V),
          IsPullback (yoneda.map a) (yoneda.map q) p t ∧
          (∀ i : I, IsOpenImmersion (pullback.fst a (j i)).left) ∧
          (∀ x : P.left, ∃ (i : I) (y : (Limits.pullback a (j i)).left),
            (pullback.fst a (j i)).left y = x) ∧
          IsPullback
            (yoneda.map (Sigma.desc (fun i : I ↦
              pullback.snd a (j i) ≫ Sigma.ι U i)))
            (yoneda.map (Sigma.desc (fun i : I ↦ pullback.fst a (j i) ≫ q)))
            (yoneda.map (Sigma.desc j) ≫ p) t ∧
          Surjective (Sigma.desc (fun i : I ↦ pullback.fst a (j i) ≫ q)).left ∧
          Etale (Sigma.desc (fun i : I ↦ pullback.fst a (j i) ≫ q)).left := by
      obtain ⟨P, q, b, hb, _⟩ := hp T t
      have hq : Etale q.left := property_of_scheme_test @Etale hpEt hb
      let a : P ⟶ V := yoneda.preimage b
      have ha : yoneda.map a = b := yoneda.map_preimage b
      have hpb : IsPullback (yoneda.map a) (yoneda.map q) p t := ha.symm ▸ hb
      have hqs : Surjective q.left := property_of_scheme_test @Surjective hpSurj hb
      have hopen (i : I) : IsOpenImmersion (pullback.fst a (j i)).left :=
        MorphismProperty.of_isPullback
          ((IsPullback.of_hasPullback a (j i)).flip.map (Over.forget S)) (hj i)
      have hcov : ∀ x : P.left, ∃ (i : I) (y : (Limits.pullback a (j i)).left),
          (pullback.fst a (j i)).left y = x := by
        intro x
        obtain ⟨i, y, hy⟩ := hcover (a.left x)
        obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
          ((IsPullback.of_hasPullback a (j i)).map (Over.forget S)) x y hy.symm
        exact ⟨i, z, hz⟩
      let D := fun i ↦ Limits.pullback a (j i)
      have hcomp : IsPullback
          (yoneda.map (Sigma.desc (fun i ↦ pullback.snd a (j i) ≫ Sigma.ι U i)))
          (yoneda.map (Sigma.desc (fun i ↦ pullback.fst a (j i) ≫ q)))
          (yoneda.map (Sigma.desc j) ≫ p) t := by
        have h := ((over_sigma_pullback a U j).map yoneda).paste_vert hpb
        have heq : Sigma.desc (fun i ↦ pullback.fst a (j i)) ≫ q =
            Sigma.desc (fun i ↦ pullback.fst a (j i) ≫ q) := by
          apply Sigma.hom_ext
          intro i
          simp
        rw [← heq, Functor.map_comp]
        exact h
      have hsurj : Surjective
          (Sigma.desc (fun i ↦ pullback.fst a (j i) ≫ q)).left := by
        constructor
        intro x
        obtain ⟨y, hy⟩ := hqs.surj x
        obtain ⟨i, z, hz⟩ := hcov y
        refine ⟨(Sigma.ι D i).left z, ?_⟩
        change ((Sigma.ι D i ≫
          Sigma.desc (fun i ↦ pullback.fst a (j i) ≫ q)).left) z = x
        rw [Sigma.ι_desc]
        change q.left ((pullback.fst a (j i)).left z) = x
        rw [hz, hy]
      have he : Etale (Sigma.desc (fun i ↦ pullback.fst a (j i) ≫ q)).left := by
        apply over_sigma_property @Etale
        intro i
        have : IsOpenImmersion (pullback.fst a (j i)).left := hopen i
        have : Etale q.left := hq
        change Etale ((pullback.fst a (j i)).left ≫ q.left)
        infer_instance
      exact ⟨P, q, a, hpb, hopen, hcov, hcomp, hsurj, he⟩
    have hs : IsSurjective (yoneda.map (Sigma.desc j) ≫ p) := by
      intro T t
      obtain ⟨P, q, a, _, _, _, h, hs, _⟩ := htests T t
      exact ⟨_, _, _, h, hs⟩
    refine ⟨htests, ?_, hs, ?_, schemePointMap_surjective _ hs⟩
    · intro T t
      obtain ⟨P, q, a, _, _, _, h, _, _⟩ := htests T t
      exact ⟨_, _, _, h, trivial⟩
    · intro T t
      obtain ⟨P, q, a, _, _, _, h, _, he⟩ := htests T t
      exact ⟨_, _, _, h, he⟩
  · have hbase (x : V.left) : ∃ B : S.Opens, IsAffineOpen B ∧ V.hom x ∈ B := by
      obtain ⟨B, hB, hx, _⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
          (show V.hom x ∈ (⊤ : S.Opens) from trivial)
      exact ⟨B, hB, hx⟩
    choose B hB hxB using hbase
    have hopen (x : V.left) : ∃ A : V.left.Opens,
        IsAffineOpen A ∧ x ∈ A ∧ A ≤ V.hom ⁻¹ᵁ B x := by
      exact (TopologicalSpace.Opens.isBasis_iff_nbhd.mp V.left.isBasis_affineOpens) (hxB x)
    choose A hA hxA hAB using hopen
    let U (x : V.left) : Over S := Over.mk ((A x).ι ≫ V.hom)
    let j (x : V.left) : U x ⟶ V := Over.homMk (A x).ι rfl
    refine ⟨V.left, U, j, ?_, ?_, ?_, ?_⟩
    · intro x
      exact inferInstanceAs (IsOpenImmersion (A x).ι)
    · intro x
      exact ⟨x, ⟨x, hxA x⟩, rfl⟩
    · intro x
      exact hA x
    · intro x
      exact ⟨B x, hB x, V.hom.resLE (B x) (A x) (hAB x),
        V.hom.resLE_comp_ι (hAB x)⟩

end AlgebraicGeometry.AlgebraicSpace
