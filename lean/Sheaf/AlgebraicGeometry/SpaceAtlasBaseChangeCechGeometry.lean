/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Base change of an algebraic-space atlas and its Čech overlap

Source: Stacks Project, Morphisms of Spaces, Tag 03M8, proof of
`lemma-compute-pushforward` (blueprint: lem-trf-space-atlas-base-change-cech-geometry).

Fibre products are specified by their universal properties, allowing any choice of
representing objects. The overlap is over `W = V ×_Y X`, correcting the printed subscript
`X` in the source. All induced arrows are fixed by their projection equations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private theorem etale_source_represented {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (hf : IsEtale f)
    (T : Over S) (e : G ≅ yoneda.obj T) :
    ∃ U : Over S, Nonempty (F ≅ yoneda.obj U) := by
  obtain ⟨U, p, q, sq, _⟩ := hf T e.inv
  have : IsIso q := sq.isIso_fst_of_isIso
  exact ⟨U, ⟨(asIso q).symm⟩⟩

private theorem representable_etale_chartwise {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : IsEtale f.hom.hom) :
    IsChartwiseEtale f := by
  intro T a ha
  exact isEtale_comp a f.hom.hom ha hf

private theorem surjective_jointlySurjective {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (hf : IsSurjective f) :
    IsJointlySurjective (fun _ : Unit ↦ f) := by
  intro K _ s x
  obtain ⟨T, p, q, sq, hp⟩ := hf (Over.mk s) (yonedaEquiv.symm x)
  obtain ⟨t, _⟩ := hp.surj (IsLocalRing.closedPoint K)
  let L := T.left.residueField t
  let b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    T.left.fromSpecResidueField t ≫ p.left
  let e : K →+* L := (Spec.preimage b).hom
  have he : Spec.map (CommRingCat.ofHom e) = b := Spec.map_preimage b
  let a : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ T :=
    Over.homMk (T.left.fromSpecResidueField t) (by
      change T.left.fromSpecResidueField t ≫ T.hom =
        Spec.map (CommRingCat.ofHom e) ≫ s
      rw [he]
      change T.left.fromSpecResidueField t ≫ T.hom =
        (T.left.fromSpecResidueField t ≫ p.left) ≫ s
      rw [Category.assoc]
      have hw : p.left ≫ s = T.hom := Over.w p
      rw [hw])
  refine ⟨(), L, inferInstance, e, q.app _ a, ?_⟩
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app sq.w
    (op (Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s)))) a
  change f.app _ (q.app _ a) = G.map (a ≫ p).op x at h
  have ha : a ≫ p = Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl := by
    apply Over.OverMorphism.ext
    exact he.symm
  simpa only [ha, Over.mk, CostructuredArrow.mk] using h

/-- Geometry of the base-changed atlas, including its realization in the enlarged site.
Here `R`, `W`, `Z`, `Q` are respectively `U ×_X U`, `V ×_Y X`, `V ×_Y U`,
`V ×_Y R`. The equations for `c`, `q₁`, `q₂` specify the unique induced maps.
The two equations for the isomorphism identify its projections with `q₁`, `q₂`;
thus on every test scheme it sends `((v,u₁),(v,u₂))` to `(v,(u₁,u₂))`.
Source: Stacks, Tag 03M8, covering and overlap sentences of the proof
(blueprint: lem-trf-space-atlas-base-change-cech-geometry).

Proof:
1. Apply [lem-trf-space-fibre-products-etale-covers] to the displayed pullbacks.
   Each projection from `R` is a base change of the atlas `p`; `Z → U`, `Q → R`
   and `W → X` are base changes of `v`. Scheme-test representability gives schemes
   representing `R`, `Z`, `Q`, and [lem-trf-space-chartwise-etale-permanence] gives
   the asserted étaleness, including that of composites to `X`.
2. The projection equations identify `Z` with `W ×_X U`. Scheme-test surjectivity
   of `p` gives a lift of every field-valued point after a residue-field extension,
   hence joint surjectivity in [def-trf-algebraic-space-jointly-surjective-family].
   Pulling back this singleton covering gives the singleton `c : Z → W`.
3. By [lem-trf-space-enlarged-etale-ringed-site-model], the étale structure maps
   make `U`, `R`, `W`, `Z`, `Q` enlarged-site objects. All projection equations are
   equations over `X`, so the indicated arrows are morphisms of that site, and `c`
   is a covering there by its chartwise étaleness and joint surjectivity.
4. The maps on sections `((v,u₁),(v,u₂)) ↦ (v,(u₁,u₂))` and its coordinatewise
   inverse are well-defined by the four pullback equations. They commute with
   restrictions and are inverse. They preserve the two projections to `Z`, hence
   also the map to `W`. This constructs the specified canonical sheaf isomorphism,
   which is an algebraic-space isomorphism because the subcategory is full. -/
theorem space_atlas_base_change_cech_geometry {S : Scheme.{u}}
    (X Y : AlgebraicSpace S) (U V : Over S)
    (f : X ⟶ Y) (p : schemeSpace U ⟶ X) (v : schemeSpace V ⟶ Y)
    (hp : IsEtale p.hom.hom) (hps : IsSurjective p.hom.hom)
    (hv : IsEtale v.hom.hom)
    (R W Z Q : AlgebraicSpace S)
    (p₁ p₂ : R ⟶ schemeSpace U) (r : IsPullback p₁.hom p₂.hom p.hom p.hom)
    (wV : W ⟶ schemeSpace V) (wX : W ⟶ X)
    (w : IsPullback wV.hom wX.hom v.hom f.hom)
    (zV : Z ⟶ schemeSpace V) (zU : Z ⟶ schemeSpace U)
    (z : IsPullback zV.hom zU.hom v.hom (p ≫ f).hom)
    (qV : Q ⟶ schemeSpace V) (qR : Q ⟶ R)
    (q : IsPullback qV.hom qR.hom v.hom (p₁ ≫ p ≫ f).hom)
    (c : Z ⟶ W) (hcV : c ≫ wV = zV) (hcX : c ≫ wX = zU ≫ p)
    (q₁ q₂ : Q ⟶ Z)
    (hq₁V : q₁ ≫ zV = qV) (hq₂V : q₂ ≫ zV = qV)
    (hq₁U : q₁ ≫ zU = qR ≫ p₁) (hq₂U : q₂ ≫ zU = qR ≫ p₂) :
    (∃ T : Over S, Nonempty (R.obj.obj ≅ yoneda.obj T)) ∧
    (∃ T : Over S, Nonempty (Z.obj.obj ≅ yoneda.obj T)) ∧
    (∃ T : Over S, Nonempty (Q.obj.obj ≅ yoneda.obj T)) ∧
    IsEtale p₁.hom.hom ∧ IsEtale p₂.hom.hom ∧
    IsEtale zU.hom.hom ∧ IsEtale qR.hom.hom ∧ IsChartwiseEtale wX ∧
    IsChartwiseEtale c ∧ IsJointlySurjective (fun _ : Unit ↦ c.hom.hom) ∧
    (∃ (Xₓ Uₓ Rₓ Wₓ Zₓ Qₓ : X.EnlargedEtaleSite)
      (p₁ₓ p₂ₓ : Rₓ ⟶ Uₓ) (zUₓ : Zₓ ⟶ Uₓ) (qRₓ : Qₓ ⟶ Rₓ)
      (cₓ : Zₓ ⟶ Wₓ) (q₁ₓ q₂ₓ : Qₓ ⟶ Zₓ) (wXₓ : Wₓ ⟶ Xₓ),
      Xₓ.obj = Over.mk (𝟙 X) ∧ Uₓ.obj = Over.mk p ∧ Rₓ.obj = Over.mk (p₁ ≫ p) ∧
      Wₓ.obj = Over.mk wX ∧ Zₓ.obj = Over.mk (zU ≫ p) ∧
      Qₓ.obj = Over.mk (qR ≫ p₁ ≫ p) ∧
      HEq p₁ₓ.hom.left p₁ ∧ HEq p₂ₓ.hom.left p₂ ∧
      HEq zUₓ.hom.left zU ∧ HEq qRₓ.hom.left qR ∧ HEq cₓ.hom.left c ∧
      HEq q₁ₓ.hom.left q₁ ∧ HEq q₂ₓ.hom.left q₂ ∧ HEq wXₓ.hom.left wX ∧
      Presieve.ofArrows (fun _ : Unit ↦ Zₓ) (fun _ : Unit ↦ cₓ) ∈
        X.enlargedEtalePrecoverage Wₓ) ∧
    (∃ e : Limits.pullback c.hom c.hom ≅ Q.obj,
      e.hom ≫ q₁.hom = Limits.pullback.fst c.hom c.hom ∧
      e.hom ≫ q₂.hom = Limits.pullback.snd c.hom c.hom) := by
  have map_sq := fun {A B C D : AlgebraicSpace S} {a : D ⟶ A} {b : D ⟶ B}
      {f : A ⟶ C} {g : B ⟶ C} (sq : IsPullback a.hom b.hom f.hom g.hom) ↦
    (sheafToPresheaf _ _).map_isPullback sq
  have hp₁ : IsEtale p₁.hom.hom :=
    representableWith_baseChange _ (map_sq r.flip) hp
  have hp₂ : IsEtale p₂.hom.hom :=
    representableWith_baseChange _ (map_sq r) hp
  have hzU : IsEtale zU.hom.hom :=
    representableWith_baseChange _ (map_sq z) hv
  have hqR : IsEtale qR.hom.hom :=
    representableWith_baseChange _ (map_sq q) hv
  have hwX : IsEtale wX.hom.hom :=
    representableWith_baseChange _ (map_sq w) hv
  have hc : IsPullback zU.hom c.hom p.hom wX.hom := by
    apply IsPullback.of_bot (h₃₁ := v.hom) (v₂₁ := wV.hom) (v₂₂ := f.hom)
    · simpa only [← InducedCategory.comp_hom, hcV] using z.flip
    · exact congrArg (fun k ↦ k.hom) hcX.symm
    · exact w.flip
  have hce : IsEtale c.hom.hom :=
    representableWith_baseChange _ (map_sq hc) hp
  have hcs : IsSurjective c.hom.hom :=
    representableWith_baseChange _ (map_sq hc) hps
  have hj := surjective_jointlySurjective c.hom.hom hcs
  obtain ⟨T, hT⟩ := etale_source_represented p₁.hom.hom hp₁ U (Iso.refl _)
  obtain ⟨A, hA⟩ := etale_source_represented zU.hom.hom hzU U (Iso.refl _)
  obtain ⟨B, hB⟩ := etale_source_represented qR.hom.hom hqR T hT.some
  have hpc := representable_etale_chartwise p hp
  have hrpc := representable_etale_chartwise (p₁ ≫ p)
    (isEtale_comp _ _ hp₁ hp)
  have hzpc := representable_etale_chartwise (zU ≫ p)
    (isEtale_comp _ _ hzU hp)
  have hqpc := representable_etale_chartwise (qR ≫ p₁ ≫ p)
    (isEtale_comp _ _ hqR (isEtale_comp _ _ hp₁ hp))
  have hwc := representable_etale_chartwise wX hwX
  have hcc := representable_etale_chartwise c hce
  have hpp : p₁ ≫ p = p₂ ≫ p := ObjectProperty.hom_ext _ r.w
  have hqc : q₁ ≫ c = q₂ ≫ c := by
    apply ObjectProperty.hom_ext
    apply w.hom_ext
    · simp only [← InducedCategory.comp_hom, Category.assoc, hcV, hq₁V, hq₂V]
    · simp only [← InducedCategory.comp_hom, Category.assoc, hcX,
        ← Category.assoc q₁ zU p, ← Category.assoc q₂ zU p,
        hq₁U, hq₂U, Category.assoc, hpp]
  have sq₁ : IsPullback q₁.hom qR.hom zU.hom p₁.hom := by
    apply IsPullback.of_right (h₁₂ := zV.hom) (h₂₂ := (p ≫ f).hom)
    · simpa only [← InducedCategory.comp_hom, hq₁V] using q
    · exact congrArg (fun k ↦ k.hom) hq₁U
    · exact z
  have sq : IsPullback q₁.hom q₂.hom c.hom c.hom := by
    apply IsPullback.of_bot (v₂₁ := zU.hom) (v₂₂ := wX.hom) (h₃₁ := p.hom)
    · simpa only [← InducedCategory.comp_hom, hq₂U, hcX] using sq₁.paste_vert r
    · exact congrArg (fun k ↦ k.hom) hqc
    · exact hc.flip
  refine ⟨⟨T, hT⟩, ⟨A, hA⟩, ⟨B, hB⟩, hp₁, hp₂, hzU, hqR, hwc, hcc, hj, ?_,
    ⟨sq.isoPullback.symm, sq.isoPullback_inv_fst, sq.isoPullback_inv_snd⟩⟩
  have hid : IsChartwiseEtale (𝟙 X) := by
    intro T a ha
    simpa using ha
  let Xₓ : X.EnlargedEtaleSite := ⟨Over.mk (𝟙 X), hid⟩
  let Uₓ : X.EnlargedEtaleSite := ⟨Over.mk p, hpc⟩
  let Rₓ : X.EnlargedEtaleSite := ⟨Over.mk (p₁ ≫ p), hrpc⟩
  let Wₓ : X.EnlargedEtaleSite := ⟨Over.mk wX, hwc⟩
  let Zₓ : X.EnlargedEtaleSite := ⟨Over.mk (zU ≫ p), hzpc⟩
  let Qₓ : X.EnlargedEtaleSite := ⟨Over.mk (qR ≫ p₁ ≫ p), hqpc⟩
  let p₁ₓ : Rₓ ⟶ Uₓ := ObjectProperty.homMk (Over.homMk p₁ rfl)
  let p₂ₓ : Rₓ ⟶ Uₓ := ObjectProperty.homMk (Over.homMk p₂ hpp.symm)
  let zUₓ : Zₓ ⟶ Uₓ := ObjectProperty.homMk (Over.homMk zU rfl)
  let qRₓ : Qₓ ⟶ Rₓ := ObjectProperty.homMk (Over.homMk qR rfl)
  let cₓ : Zₓ ⟶ Wₓ := ObjectProperty.homMk (Over.homMk c hcX)
  have hq₁p : q₁ ≫ (zU ≫ p) = qR ≫ p₁ ≫ p := by
    rw [← Category.assoc, hq₁U, Category.assoc]
  have hq₂p : q₂ ≫ (zU ≫ p) = qR ≫ p₁ ≫ p := by
    rw [← Category.assoc, hq₂U, Category.assoc, ← hpp]
  let q₁ₓ : Qₓ ⟶ Zₓ := ObjectProperty.homMk (Over.homMk q₁ hq₁p)
  let q₂ₓ : Qₓ ⟶ Zₓ := ObjectProperty.homMk (Over.homMk q₂ hq₂p)
  let wXₓ : Wₓ ⟶ Xₓ := ObjectProperty.homMk (Over.homMk wX (Category.comp_id _))
  refine ⟨Xₓ, Uₓ, Rₓ, Wₓ, Zₓ, Qₓ, p₁ₓ, p₂ₓ, zUₓ, qRₓ, cₓ, q₁ₓ, q₂ₓ, wXₓ,
    rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, ?_⟩
  constructor
  · rintro M a ⟨i⟩
    exact hcc
  · intro K _ s x
    obtain ⟨i, L, hL, e, y, hy⟩ := hj K s x
    exact ⟨⟨⟨Zₓ, cₓ⟩, ⟨()⟩⟩, L, hL, e, y, hy⟩

-- The fixed interface retains geometric hypotheses; naturality uses only uniqueness.
set_option linter.unusedVariables false in
/-- Naturality of the canonical overlap isomorphism under every change `V' → V`
of étale test schemes over `Y`. All three base-change maps below are specified by
both projections, so none is an arbitrary choice of comparison map. The map `d`
is the induced map between the two Čech overlaps, likewise fixed by both projections.
Source: Stacks, Tag 03M8, functoriality in `V` in the proof
(blueprint: lem-trf-space-atlas-base-change-cech-geometry).

Proof: by the pullback universal properties, `aW`, `aZ`, `aQ` change only the
`V'` coordinate by `a` and leave the `X`, `U`, `R` coordinates unchanged.
Either composite in the asserted square sends `((v',u₁),(v',u₂))` to
`(a(v'),(u₁,u₂))`. The maps agree on all test schemes and commute with
restriction, hence are equal natural transformations and equal sheaf maps.
This is step 5 of the node, using [lem-trf-space-fibre-products-etale-covers]
and [def-trf-algebraic-space]. -/
theorem space_atlas_base_change_cech_naturality {S : Scheme.{u}}
    (X Y : AlgebraicSpace S) (U V V' : Over S)
    (f : X ⟶ Y) (p : schemeSpace U ⟶ X)
    (v : schemeSpace V ⟶ Y) (v' : schemeSpace V' ⟶ Y)
    (hp : IsEtale p.hom.hom) (hps : IsSurjective p.hom.hom)
    (hv : IsEtale v.hom.hom) (hv' : IsEtale v'.hom.hom)
    (a : V' ⟶ V) (ha : yoneda.map a ≫ v.hom.hom = v'.hom.hom)
    (R W Z Q W' Z' Q' : AlgebraicSpace S)
    (p₁ p₂ : R ⟶ schemeSpace U) (r : IsPullback p₁.hom p₂.hom p.hom p.hom)
    (wV : W ⟶ schemeSpace V) (wX : W ⟶ X)
    (w : IsPullback wV.hom wX.hom v.hom f.hom)
    (zV : Z ⟶ schemeSpace V) (zU : Z ⟶ schemeSpace U)
    (z : IsPullback zV.hom zU.hom v.hom (p ≫ f).hom)
    (qV : Q ⟶ schemeSpace V) (qR : Q ⟶ R)
    (q : IsPullback qV.hom qR.hom v.hom (p₁ ≫ p ≫ f).hom)
    (wV' : W' ⟶ schemeSpace V') (wX' : W' ⟶ X)
    (w' : IsPullback wV'.hom wX'.hom v'.hom f.hom)
    (zV' : Z' ⟶ schemeSpace V') (zU' : Z' ⟶ schemeSpace U)
    (z' : IsPullback zV'.hom zU'.hom v'.hom (p ≫ f).hom)
    (qV' : Q' ⟶ schemeSpace V') (qR' : Q' ⟶ R)
    (q' : IsPullback qV'.hom qR'.hom v'.hom (p₁ ≫ p ≫ f).hom)
    (c : Z ⟶ W) (hcV : c ≫ wV = zV) (hcX : c ≫ wX = zU ≫ p)
    (c' : Z' ⟶ W') (hcV' : c' ≫ wV' = zV') (hcX' : c' ≫ wX' = zU' ≫ p)
    (q₁ q₂ : Q ⟶ Z) (q₁' q₂' : Q' ⟶ Z')
    (hq₁V : q₁ ≫ zV = qV) (hq₂V : q₂ ≫ zV = qV)
    (hq₁U : q₁ ≫ zU = qR ≫ p₁) (hq₂U : q₂ ≫ zU = qR ≫ p₂)
    (hq₁V' : q₁' ≫ zV' = qV') (hq₂V' : q₂' ≫ zV' = qV')
    (hq₁U' : q₁' ≫ zU' = qR' ≫ p₁) (hq₂U' : q₂' ≫ zU' = qR' ≫ p₂)
    (e : Limits.pullback c.hom c.hom ≅ Q.obj)
    (he₁ : e.hom ≫ q₁.hom = Limits.pullback.fst c.hom c.hom)
    (he₂ : e.hom ≫ q₂.hom = Limits.pullback.snd c.hom c.hom)
    (e' : Limits.pullback c'.hom c'.hom ≅ Q'.obj)
    (he₁' : e'.hom ≫ q₁'.hom = Limits.pullback.fst c'.hom c'.hom)
    (he₂' : e'.hom ≫ q₂'.hom = Limits.pullback.snd c'.hom c'.hom)
    (aW : W' ⟶ W) (aZ : Z' ⟶ Z) (aQ : Q' ⟶ Q)
    (haWV : aW.hom.hom ≫ wV.hom.hom = wV'.hom.hom ≫ yoneda.map a)
    (haWX : aW ≫ wX = wX')
    (haZV : aZ.hom.hom ≫ zV.hom.hom = zV'.hom.hom ≫ yoneda.map a)
    (haZU : aZ ≫ zU = zU')
    (haQV : aQ.hom.hom ≫ qV.hom.hom = qV'.hom.hom ≫ yoneda.map a)
    (haQR : aQ ≫ qR = qR')
    (d : Limits.pullback c'.hom c'.hom ⟶ Limits.pullback c.hom c.hom)
    (hd₁ : d ≫ Limits.pullback.fst c.hom c.hom =
      Limits.pullback.fst c'.hom c'.hom ≫ aZ.hom)
    (hd₂ : d ≫ Limits.pullback.snd c.hom c.hom =
      Limits.pullback.snd c'.hom c'.hom ≫ aZ.hom) :
    d ≫ e.hom = e'.hom ≫ aQ.hom := by
  have arrow_naturality (i : Q ⟶ Z) (i' : Q' ⟶ Z')
      (hiV : i ≫ zV = qV) (hiV' : i' ≫ zV' = qV')
      (t : R ⟶ schemeSpace U)
      (hiU : i ≫ zU = qR ≫ t) (hiU' : i' ≫ zU' = qR' ≫ t) :
      aQ.hom ≫ i.hom = i'.hom ≫ aZ.hom := by
    apply z.hom_ext
    · apply Sheaf.hom_ext
      have hi : i.hom.hom ≫ zV.hom.hom = qV.hom.hom :=
        congrArg (fun k ↦ k.hom.hom) hiV
      have hi' : i'.hom.hom ≫ zV'.hom.hom = qV'.hom.hom :=
        congrArg (fun k ↦ k.hom.hom) hiV'
      change (aQ.hom.hom ≫ i.hom.hom) ≫ zV.hom.hom =
        (i'.hom.hom ≫ aZ.hom.hom) ≫ zV.hom.hom
      rw [Category.assoc, hi, haQV, Category.assoc, haZV,
        ← Category.assoc, hi']
    · have hi : i.hom ≫ zU.hom = qR.hom ≫ t.hom :=
        congrArg (fun k ↦ k.hom) hiU
      have hi' : i'.hom ≫ zU'.hom = qR'.hom ≫ t.hom :=
        congrArg (fun k ↦ k.hom) hiU'
      have ht : aQ.hom ≫ qR.hom = qR'.hom := congrArg (fun k ↦ k.hom) haQR
      have hu : aZ.hom ≫ zU.hom = zU'.hom := congrArg (fun k ↦ k.hom) haZU
      rw [Category.assoc, hi, ← Category.assoc, ht, Category.assoc, hu, hi']
  have h₁ := arrow_naturality q₁ q₁' hq₁V hq₁V' p₁ hq₁U hq₁U'
  have h₂ := arrow_naturality q₂ q₂' hq₂V hq₂V' p₂ hq₂U hq₂U'
  have eq₁ : (d ≫ e.hom) ≫ q₁.hom = (e'.hom ≫ aQ.hom) ≫ q₁.hom := by
    rw [Category.assoc, he₁, hd₁, Category.assoc, h₁,
      ← Category.assoc, he₁']
  have eq₂ : (d ≫ e.hom) ≫ q₂.hom = (e'.hom ≫ aQ.hom) ≫ q₂.hom := by
    rw [Category.assoc, he₂, hd₂, Category.assoc, h₂,
      ← Category.assoc, he₂']
  apply q.hom_ext
  · have h := congrArg (fun k ↦ k ≫ zV.hom) eq₁
    simpa only [Category.assoc, ← InducedCategory.comp_hom, hq₁V] using h
  · apply r.hom_ext
    · have h := congrArg (fun k ↦ k ≫ zU.hom) eq₁
      simpa only [Category.assoc, ← InducedCategory.comp_hom, hq₁U] using h
    · have h := congrArg (fun k ↦ k ≫ zU.hom) eq₂
      simpa only [Category.assoc, ← InducedCategory.comp_hom, hq₂U] using h

end AlgebraicGeometry.AlgebraicSpace
