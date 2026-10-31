/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import WeilConjectures.AlgebraicGeometry.EnlargedEtaleRingedSite
import Mathlib.Topology.Category.TopCat.EpiMono

/-!
# The open image of an étale scheme map to an algebraic space

Source: Stacks Project, Properties of Spaces, Tag 06NF, `lemma-etale-image-open`,
first assertion and factorization (blueprint: lem-a1-etale-scheme-map-open-image).

The point-image equality is expanded on field-valued representatives. Membership in an
open subspace means that the representative factors through it. Membership in the image
of a scheme means that the representative lifts to the scheme after a field extension;
this is exactly equality with a scheme point over a common field extension.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private theorem pullback_cancel_mono {C : Type*} [Category C]
    {P G H F E : C} {q : P ⟶ G} {p : P ⟶ H} {f : G ⟶ E} {a : H ⟶ E}
    (j : E ⟶ F) [Mono j] (h : IsPullback q p (f ≫ j) (a ≫ j)) :
    IsPullback q p f a := by
  exact IsPullback.of_isLimit
    (PullbackCone.isLimitOfFactors _ _ j f a rfl rfl h.cone h.isLimit)

private theorem representable_comp {S : Scheme.{u}}
    {E F G : (Over S)ᵒᵖ ⥤ Type u} {f : E ⟶ F} {g : F ⟶ G}
    (hf : IsRepresentable f) (hg : IsRepresentable g) : IsRepresentable (f ≫ g) := by
  intro T a
  obtain ⟨V, p, q, hq, _⟩ := hg T a
  obtain ⟨W, r, s, hs, _⟩ := hf V q
  refine ⟨W, r ≫ p, s, ?_, trivial⟩
  simpa only [yoneda.map_comp] using hs.paste_vert hq

private theorem representable_cancel_mono {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) {E F G : (Over S)ᵒᵖ ⥤ Type u}
    {f : E ⟶ F} (g : F ⟶ G) [Mono g]
    (hf : IsRepresentableWith P (f ≫ g)) : IsRepresentableWith P f := by
  intro T a
  obtain ⟨V, p, q, hq, hp⟩ := hf T (a ≫ g)
  exact ⟨V, p, q, pullback_cancel_mono g hq, hp⟩

private theorem representable_baseChange {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) {E F G H : (Over S)ᵒᵖ ⥤ Type u}
    {q : H ⟶ E} {p : H ⟶ G} {f : E ⟶ F} {a : G ⟶ F}
    (h : IsPullback q p f a) (hf : IsRepresentableWith P f) :
    IsRepresentableWith P p := by
  intro T b
  obtain ⟨V, r, s, hs, hr⟩ := hf T (b ≫ a)
  let t := h.lift s (yoneda.map r ≫ b) (by simpa using hs.w)
  refine ⟨V, r, t, ?_, hr⟩
  apply IsPullback.of_right (by simpa [t] using hs) (h.lift_snd _ _ _) h

-- Glue in the target sheaf, then glue maps to its representing scheme pullback.
private theorem representable_isSheaf {S : Scheme.{u}}
    {F : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {G : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F.obj) (hf : IsRepresentable f) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) G := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply Presieve.isSheaf_of_yoneda
  intro T R hR α
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  obtain ⟨a, ha, huniq⟩ :=
    (Presieve.isSheafFor_iff_yonedaSheafCondition.mp (hF R hR)) (α ≫ f)
  obtain ⟨V, p, q, hq, _⟩ := hf T a
  let β := hq.lift α R.functorInclusion ha.symm
  have hV := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology.over S) (yoneda.obj V)
  obtain ⟨b, hb, hbuniq⟩ :=
    (Presieve.isSheafFor_iff_yonedaSheafCondition.mp (hV R hR)) β
  refine ⟨b ≫ q, ?_, ?_⟩
  · change R.functorInclusion ≫ (b ≫ q) = α
    rw [← Category.assoc, hb]
    exact hq.lift_fst _ _ _
  · intro c hc
    have hcf : c ≫ f = a := by
      apply huniq
      rw [← Category.assoc, hc]
    let d := hq.lift c (𝟙 _) (by simpa using hcf)
    have hd : R.functorInclusion ≫ d = β := by
      apply hq.hom_ext
      · simp [d, β, hc]
      · simp [d, β]
    have he : d = b := hbuniq _ hd
    calc
      c = d ≫ q := (hq.lift_fst _ _ _).symm
      _ = b ≫ q := by rw [he]

-- A point of the scheme test supplies a lift over its residue field.
private theorem surjective_field_lift {S : Scheme.{u}}
    {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) (hf : IsSurjective f)
    (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (x : F.obj (op (Over.mk s))) :
    ∃ (L : Type u) (_ : Field L) (e : K →+* L)
      (y : G.obj (op (Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s)))),
      f.app _ y = F.map (Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl).op x := by
  obtain ⟨V, p, q, hq, hp⟩ := hf (Over.mk s) (yonedaEquiv.symm x)
  have := hp
  obtain ⟨z, _⟩ := p.left.surjective (IsLocalRing.closedPoint K)
  let L : Type u := V.left.residueField z
  let r := V.left.fromSpecResidueField z
  let a := r ≫ p.left
  let e : K →+* L := (Spec.preimage a).hom
  have he : Spec.map (CommRingCat.ofHom e) = a := Spec.map_preimage a
  let b : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ V :=
    Over.homMk r (by
      rw [he]
      change r ≫ V.hom = (r ≫ p.left) ≫ s
      rw [Category.assoc]
      exact congrArg (fun t ↦ r ≫ t) p.w.symm)
  refine ⟨L, inferInstance, e, q.app _ b, ?_⟩
  have hh := congrArg (fun t ↦ t.app _ b) hq.w
  change f.app _ (q.app _ b) = F.map (b ≫ p).op x at hh
  have hb : b ≫ p = Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl := by
    apply Over.OverMorphism.ext
    exact he.symm
  rw [hb] at hh
  exact hh

-- An open subscheme of a field spectrum containing an extension-valued point is everything.
private theorem open_field_lift_descends {S : Scheme.{u}}
    {G F : (Over S)ᵒᵖ ⥤ Type u} (j : G ⟶ F)
    (hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j)
    (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (x : F.obj (op (Over.mk s)))
    (L : Type u) [Field L] (e : K →+* L)
    (y : G.obj (op (Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s))))
    (hy : j.app _ y = F.map
      (Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl).op x) :
    ∃ z : G.obj (op (Over.mk s)), j.app _ z = x := by
  obtain ⟨V, p, q, hq, hp⟩ := hj (Over.mk s) (yonedaEquiv.symm x)
  let a : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ Over.mk s :=
    Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl
  have hw : yonedaEquiv.symm y ≫ j = yoneda.map a ≫ yonedaEquiv.symm x := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply,
      ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
    exact hy
  let b := yoneda.preimage (hq.lift (yonedaEquiv.symm y) (yoneda.map a) hw)
  have := hp
  have hsur : Function.Surjective p.left := by
    intro t
    refine ⟨b.left (IsLocalRing.closedPoint L), ?_⟩
    exact @Subsingleton.elim (PrimeSpectrum K) inferInstance _ _
  have : Epi p.left.base := (TopCat.epi_iff_surjective _).mpr hsur
  have : IsIso p.left := IsOpenImmersion.isIso p.left
  have : IsIso ((Over.forget S).map p) := ‹IsIso p.left›
  have : IsIso p := isIso_of_reflects_iso p (Over.forget S)
  refine ⟨q.app _ (inv p), ?_⟩
  have hh := congrArg (fun t ↦ t.app _ (inv p)) hq.w
  change j.app _ (q.app _ (inv p)) = F.map ((inv p) ≫ p).op x at hh
  rw [IsIso.inv_hom_id, op_id] at hh
  rw [F.map_id] at hh
  exact hh

-- The diagonal and an atlas are obtained by cancellation and pullback, respectively.
private theorem openSubspace_isAlgebraicSpace {S : Scheme.{u}}
    (X : AlgebraicSpace S) (A : OpenSubspace X)
    (hA : Presheaf.IsSheaf (Scheme.fppfTopology.over S) A.val.toFunctor) :
    IsAlgebraicSpace ⟨A.val.toFunctor, hA⟩ := by
  have hj : IsRepresentable A.val.ι := by
    intro T a
    obtain ⟨V, p, q, hq, _⟩ := A.property T a
    exact ⟨V, p, q, hq, trivial⟩
  constructor
  · apply representable_cancel_mono ⊤ (prod.map A.val.ι A.val.ι)
    have h := representable_comp hj X.property.1
    dsimp only [IsRepresentable] at h
    simpa only [prod.lift_map, Category.id_comp, prod.comp_lift,
      Category.comp_id] using h
  · obtain ⟨U, w, hw, hs⟩ := X.property.2
    obtain ⟨V, p, q, hq, _⟩ := A.property U w
    exact ⟨V, q,
      representable_baseChange _ hq.flip hw,
      representable_baseChange _ hq.flip hs⟩

/-- An étale scheme map factors through its open point image as a representable,
surjective étale map. Componentwise injectivity identifies the image space as a
subfunctor; its inclusion is representable by open immersions.
Source: Stacks Project, Properties of Spaces, Tag 06NF, first assertion and factorization
(blueprint: lem-a1-etale-scheme-map-open-image).
Proof: apply `lem-a1-space-etale-open-image` to `E = h_U`, `F = X` and `q = f`.
The general theorem supplies the open subspace, its representable open inclusion, and
the representable surjective étale factorization. Its point image is the image of
`|h_U| → |X|`; the field-valued point classes of `h_U` are exactly those of `U`.
For the displayed point condition, a class is in the scheme image precisely when its
representative lifts after a field extension: restrict a scheme representative along the
common field extension in the equivalence relation. A representative of a class in an
open subspace factors through that subspace already over its original field, since the
pullback open subscheme of `Spec K` is nonempty after extension and hence is all of
`Spec K`. These observations give the final equivalence. -/
theorem etaleSchemeMap_openImage {S : Scheme.{u}} (X : AlgebraicSpace S) (U : Over S)
    (f : yoneda.obj U ⟶ X.obj.obj) (hf : IsRepresentable f) (he : IsEtale f) :
    ∃ (Xf : AlgebraicSpace S) (j : Xf ⟶ X) (ff : yoneda.obj U ⟶ Xf.obj.obj),
      (∀ T : (Over S)ᵒᵖ, Function.Injective (j.hom.hom.app T)) ∧
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom ∧
      ff ≫ j.hom.hom = f ∧
      IsRepresentable ff ∧ IsSurjective ff ∧ IsEtale ff ∧
      ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
        (x : X.obj.obj.obj (op (Over.mk s))),
        (∃ y : Xf.obj.obj.obj (op (Over.mk s)), j.hom.hom.app _ y = x) ↔
          ∃ (L : Type u) (_ : Field L) (e : K →+* L)
            (y : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ U),
            f.app _ y =
              X.obj.obj.map (Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl).op x := by
  let E := schemeSpace U
  let q : E ⟶ X := ObjectProperty.homMk ⟨f⟩
  obtain ⟨_, A, _, ⟨ff, hff, heff, hsff⟩, _⟩ := etale_open_image E X q he
  change ff ≫ A.val.ι = f at hff
  change yoneda.obj U ⟶ A.val.toFunctor at ff
  have hj : IsRepresentable A.val.ι := by
    intro T a
    obtain ⟨V, p, r, hr, _⟩ := A.property T a
    exact ⟨V, p, r, hr, trivial⟩
  have hA := representable_isSheaf A.val.ι hj
  let Xf : AlgebraicSpace S :=
    ⟨⟨A.val.toFunctor, hA⟩, openSubspace_isAlgebraicSpace X A hA⟩
  let j : Xf ⟶ X := ObjectProperty.homMk ⟨A.val.ι⟩
  refine ⟨Xf, j, ff, fun T ↦ Subtype.val_injective, A.property, hff, ?_, hsff,
    heff, ?_⟩
  · apply representable_cancel_mono ⊤ A.val.ι
    rwa [hff]
  · intro K inst s x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨L, hL, e, z, hz⟩ := surjective_field_lift ff hsff K s y
      refine ⟨L, hL, e, z, ?_⟩
      rw [← hff]
      change A.val.ι.app _ (ff.app _ z) = _
      rw [hz]
      exact congrArg
        (X.obj.obj.map (Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s))
          (V := Over.mk s) (Spec.map (CommRingCat.ofHom e)) rfl).op) hy
    · rintro ⟨L, instL, e, y, hy⟩
      apply open_field_lift_descends A.val.ι A.property K s x L e (ff.app _ y)
      rw [← hff] at hy
      exact hy

end AlgebraicGeometry.AlgebraicSpace
