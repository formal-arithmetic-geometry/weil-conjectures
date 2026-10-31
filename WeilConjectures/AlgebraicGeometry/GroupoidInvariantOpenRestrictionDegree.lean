/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Restriction of a groupoid scheme to an invariant open

Source: Stacks Project, `groupoids.tex`, Tags 02VB and 03BC, and the final sentences
of Tag 03BI (blueprint: lem-a1-groupoid-invariant-open-restriction-degree).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem factor_preimage {X Y H : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens)
    (a : H ⟶ X) (b : H ⟶ W.toScheme) (h : a ≫ f = b ≫ W.ι) :
    ∃ a' : H ⟶ (f ⁻¹ᵁ W).toScheme, a' ≫ (f ⁻¹ᵁ W).ι = a := by
  have hr : Set.range a ⊆ Set.range (f ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change f (a x) ∈ W
    have hx := congrArg (fun f : H ⟶ Y ↦ f x) h
    change f (a x) = (b x).1 at hx
    rw [hx]
    exact (b x).property
  exact ⟨IsOpenImmersion.lift _ _ hr, IsOpenImmersion.lift_fac _ _ hr⟩

private theorem groupoid_of_mono {U R W V : Scheme.{u}}
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hG : IsGroupoidScheme s t e i c) (j : W ⟶ U) (k : V ⟶ R) [Mono j] [Mono k]
    (s' t' : V ⟶ W) (e' : W ⟶ V) (i' : V ⟶ V) (c' : pullback s' t' ⟶ V)
    (hs : s' ≫ j = k ≫ s) (ht : t' ≫ j = k ≫ t)
    (he : e' ≫ k = j ≫ e) (hi : i' ≫ k = k ≫ i)
    (hc : c' ≫ k = pullback.map s' t' s t k k j hs ht ≫ c) :
    IsGroupoidScheme s' t' e' i' c' := by
  have lift_eq {H : Scheme.{u}} (a b : H ⟶ V)
      (h : a ≫ s' = b ≫ t') (h' : (a ≫ k) ≫ s = (b ≫ k) ≫ t) :
      (pullback.lift a b h ≫ c') ≫ k =
        pullback.lift (a ≫ k) (b ≫ k) h' ≫ c := by
    rw [Category.assoc, hc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp
  have endpoints {H : Scheme.{u}} (a b : H ⟶ V) (h : a ≫ s' = b ≫ t') :
      (a ≫ k) ≫ s = (b ≫ k) ≫ t := by
    simpa only [Category.assoc, ← hs, ← ht] using congrArg (fun f ↦ f ≫ j) h
  refine {
    identity_source := ?_
    identity_target := ?_
    inverse_source := ?_
    inverse_target := ?_
    composition_source := ?_
    composition_target := ?_
    identity_comp := ?_
    comp_identity := ?_
    inverse_comp := ?_
    comp_inverse := ?_
    associative := ?_ }
  · apply (cancel_mono j).mp
    rw [Category.assoc, hs, ← Category.assoc, he, Category.assoc,
      hG.identity_source, Category.comp_id, Category.id_comp]
  · apply (cancel_mono j).mp
    rw [Category.assoc, ht, ← Category.assoc, he, Category.assoc,
      hG.identity_target, Category.comp_id, Category.id_comp]
  · apply (cancel_mono j).mp
    rw [Category.assoc, hs, ← Category.assoc, hi, Category.assoc, hG.inverse_source, ht]
  · apply (cancel_mono j).mp
    rw [Category.assoc, ht, ← Category.assoc, hi, Category.assoc, hG.inverse_target, hs]
  · apply (cancel_mono j).mp
    rw [Category.assoc, hs, ← Category.assoc, hc]
    simp [Category.assoc, hG.composition_source, hs]
  · apply (cancel_mono j).mp
    rw [Category.assoc, ht, ← Category.assoc, hc]
    simp [Category.assoc, hG.composition_target, ht]
  · intro H a h
    apply (cancel_mono k).mp
    rw [lift_eq _ _ h (endpoints _ _ h)]
    have q : (a ≫ t' ≫ e') ≫ k = (a ≫ k) ≫ t ≫ e := by
      simp only [Category.assoc, he, reassoc_of% ht]
    have hh : ((a ≫ k) ≫ t ≫ e) ≫ s = (a ≫ k) ≫ t := by
      simp [Category.assoc, hG.identity_source]
    simpa only [q] using hG.identity_comp H (a ≫ k) hh
  · intro H a h
    apply (cancel_mono k).mp
    rw [lift_eq _ _ h (endpoints _ _ h)]
    have q : (a ≫ s' ≫ e') ≫ k = (a ≫ k) ≫ s ≫ e := by
      simp only [Category.assoc, he, reassoc_of% hs]
    have hh : (a ≫ k) ≫ s = ((a ≫ k) ≫ s ≫ e) ≫ t := by
      simp [Category.assoc, hG.identity_target]
    simpa only [q] using hG.comp_identity H (a ≫ k) hh
  · intro H a h
    apply (cancel_mono k).mp
    rw [lift_eq _ _ h (endpoints _ _ h)]
    have q : (a ≫ i') ≫ k = (a ≫ k) ≫ i := by
      simp only [Category.assoc, hi]
    have hh : ((a ≫ k) ≫ i) ≫ s = (a ≫ k) ≫ t := by
      simp [Category.assoc, hG.inverse_source]
    simpa only [q, Category.assoc, he, reassoc_of% hs] using hG.inverse_comp H (a ≫ k) hh
  · intro H a h
    apply (cancel_mono k).mp
    rw [lift_eq _ _ h (endpoints _ _ h)]
    have q : (a ≫ i') ≫ k = (a ≫ k) ≫ i := by
      simp only [Category.assoc, hi]
    have hh : (a ≫ k) ≫ s = ((a ≫ k) ≫ i) ≫ t := by
      simp [Category.assoc, hG.inverse_target]
    simpa only [q, Category.assoc, he, reassoc_of% ht] using hG.comp_inverse H (a ≫ k) hh
  · intro H a b d hab hbd hl hr
    apply (cancel_mono k).mp
    have hab' := endpoints a b hab
    have hbd' := endpoints b d hbd
    have hl' : (pullback.lift (a ≫ k) (b ≫ k) hab' ≫ c) ≫ s = (d ≫ k) ≫ t := by
      rw [← lift_eq a b hab hab']
      exact endpoints _ _ hl
    have hr' : (a ≫ k) ≫ s = (pullback.lift (b ≫ k) (d ≫ k) hbd' ≫ c) ≫ t := by
      rw [← lift_eq b d hbd hbd']
      exact endpoints _ _ hr
    rw [lift_eq _ _ hl (endpoints _ _ hl), lift_eq _ _ hr (endpoints _ _ hr)]
    simpa only [lift_eq a b hab hab', lift_eq b d hbd hbd'] using
      hG.associative H (a ≫ k) (b ≫ k) (d ≫ k) hab' hbd' hl' hr'

private theorem inverse_involution {U R : Scheme.{u}}
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hG : IsGroupoidScheme s t e i c) : i ≫ i = 𝟙 R := by
  have hsi : (i ≫ i) ≫ s = s := by
    simp [Category.assoc, hG.inverse_source, hG.inverse_target]
  have hab : (i ≫ i) ≫ s = i ≫ t := by
    simp [hsi, hG.inverse_target]
  have hbd : i ≫ s = (𝟙 R) ≫ t := by simp [hG.inverse_source]
  have hl : (pullback.lift (i ≫ i) i hab ≫ c) ≫ s = (𝟙 R) ≫ t := by
    simp [Category.assoc, hG.composition_source, hG.inverse_source]
  have hr : (i ≫ i) ≫ s = (pullback.lift i (𝟙 R) hbd ≫ c) ≫ t := by
    simp [Category.assoc, hG.composition_target, hG.inverse_target,
      hG.inverse_source]
  have hleft : pullback.lift (i ≫ i) i hab ≫ c = t ≫ e := by
    simpa only [← Category.assoc, hG.inverse_source] using
      hG.inverse_comp R i (by simp [Category.assoc, hG.inverse_source])
  have hright : pullback.lift i (𝟙 R) hbd ≫ c = s ≫ e := by
    simpa only [Category.id_comp] using
      hG.inverse_comp R (𝟙 R) (by simp [hG.inverse_source])
  have hunitL (h : (t ≫ e) ≫ s = (𝟙 R) ≫ t) :
      pullback.lift (t ≫ e) (𝟙 R) h ≫ c = 𝟙 R := by
    simpa only [Category.id_comp] using hG.identity_comp R (𝟙 R)
      (by simp [Category.assoc, hG.identity_source])
  have hunitR (h : (i ≫ i) ≫ s = (s ≫ e) ≫ t) :
      pullback.lift (i ≫ i) (s ≫ e) h ≫ c = i ≫ i := by
    simpa only [← Category.assoc, hsi] using hG.comp_identity R (i ≫ i)
      (by simp [Category.assoc, hG.identity_target])
  have hass := hG.associative R (i ≫ i) i (𝟙 R) hab hbd hl hr
  simpa only [hleft, hright, hunitL, hunitR] using hass.symm

private theorem degree_transport {X Y : Scheme.{u}} (s t : X ⟶ Y) (i : X ⟶ X)
    [IsIso i] (h : i ≫ s = t) (r : ℕ) (hs : s.IsFiniteLocallyFreeOfDegree r) :
    t.IsFiniteLocallyFreeOfDegree r := by
  subst t
  exact {
    toIsFiniteLocallyFree := {
      toIsFinite := inferInstance
      toFlat := inferInstance
      toLocallyOfFinitePresentation := inferInstance }
    fiberDegree_eq := fun y ↦ (Scheme.Hom.fiberDegree_comp_left_of_isIso i s y).trans
      (hs.fiberDegree_eq y) }

/-- A groupoid restricts uniquely to an invariant open, and its restricted inverse
identifies source and target, preserving finite locally free degree.

Source: Stacks Project, Tags 02VB (`lemma-restrict-groupoid`), 03BC
(`definition-invariant-open`, following paragraph), and the last two sentences of
03BI (`lemma-finite-locally-free-disjoint-free`)
(blueprint: lem-a1-groupoid-invariant-open-restriction-degree).

Proof plan:
1. Set `V = s ⁻¹ᵁ W = t ⁻¹ᵁ W`. The images of both structure maps on `V` lie
   in `W`. Factor them uniquely through `W.ι` using
   lem-weil-pbc-morphism-factors-through-open-subscheme. Open inclusions are monic
   by lem-weil-pbc-open-immersion-monomorphism, so their composites detect equality.
2. The identities `e ≫ s = 𝟙 U` and `i ≫ s = t` in def-a1-groupoid-scheme imply
   that `W.ι ≫ e` and `V.ι ≫ i` land in `V`. The same factorization lemma gives
   the unique restricted identity and inverse morphisms.
3. By def-pc-fibre-product, the two inclusion maps and the source/target squares
   induce `pullback.map sW tW s t V.ι V.ι W.ι hs ht`. Since composition has source
   the source of its second factor, its composite with this map lands in `V`.
   Factor uniquely through `V.ι` to obtain the restricted composition.
4. On points of every test scheme the inclusions of `W` and `V` are injective.
   Compose each endpoint, unit, inverse and associativity equation with these
   inclusions, use the original groupoid laws and the pullback universal property,
   then cancel the inclusions. This gives def-a1-groupoid-scheme for the restrictions;
   naturality is precomposition. The unique factorizations give uniqueness of all maps:
   each restricted map is the only map satisfying its own compatibility square.
5. Uniqueness of inverses in the original groupoid of points gives `i ≫ i = 𝟙 R`.
   Cancel `V.ι` to deduce `iW ≫ iW = 𝟙 V`. Thus `iW` is its own inverse, and
   `iW ≫ sW = tW` identifies the restricted structure morphisms over `W`.
6. If `sW` is finite locally free, this identification transfers its affine finite
   coordinate algebras, flat stalk algebras and affine finite-presentation charts
   to `tW`. These are respectively def-weil-finite-integral-morphism,
   def-weil-flat-morphism and def-sbc-locally-finite-presentation, hence the three
   conditions of def-pc-finite-locally-free.
7. Base change of the involution to every residue field gives inverse isomorphisms
   of the source and target fibres, by def-pc-fibre-product. Their section rings are
   isomorphic over that residue field, so their dimensions, and thus their degrees
   in def-pc-finite-locally-free, agree. For the empty open all maps are the unique
   maps of empty schemes and the degree condition is vacuous.
-/
theorem IsGroupoidScheme.existsUnique_invariantOpen_restriction_degree
    {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) (hG : IsGroupoidScheme s t e i c)
    (W : U.Opens) (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    ∃ (sW tW : (s ⁻¹ᵁ W).toScheme ⟶ W.toScheme) (eW : W.toScheme ⟶ (s ⁻¹ᵁ W).toScheme)
      (iW : (s ⁻¹ᵁ W).toScheme ⟶ (s ⁻¹ᵁ W).toScheme)
      (cW : pullback sW tW ⟶ (s ⁻¹ᵁ W).toScheme)
      (hs : sW ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ s) (ht : tW ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ t),
      (∀ sW' : (s ⁻¹ᵁ W).toScheme ⟶ W.toScheme, sW' ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ s ↔ sW' = sW) ∧
      (∀ tW' : (s ⁻¹ᵁ W).toScheme ⟶ W.toScheme, tW' ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ t ↔ tW' = tW) ∧
      (∀ eW' : W.toScheme ⟶ (s ⁻¹ᵁ W).toScheme, eW' ≫ (s ⁻¹ᵁ W).ι = W.ι ≫ e ↔ eW' = eW) ∧
      (∀ iW' : (s ⁻¹ᵁ W).toScheme ⟶ (s ⁻¹ᵁ W).toScheme,
        iW' ≫ (s ⁻¹ᵁ W).ι = (s ⁻¹ᵁ W).ι ≫ i ↔ iW' = iW) ∧
      (∀ cW' : pullback sW tW ⟶ (s ⁻¹ᵁ W).toScheme,
        cW' ≫ (s ⁻¹ᵁ W).ι =
            pullback.map sW tW s t (s ⁻¹ᵁ W).ι (s ⁻¹ᵁ W).ι W.ι hs ht ≫ c ↔ cW' = cW) ∧
      IsGroupoidScheme sW tW eW iW cW ∧
      IsIso iW ∧ iW ≫ iW = 𝟙 (s ⁻¹ᵁ W).toScheme ∧ iW ≫ sW = tW ∧
      ∀ r : ℕ, sW.IsFiniteLocallyFreeOfDegree r →
        tW.IsFiniteLocallyFreeOfDegree r := by
  let V := s ⁻¹ᵁ W
  let sW := s.resLE W V le_rfl
  let tW := t.resLE W V (le_of_eq hW)
  have hs : sW ≫ W.ι = V.ι ≫ s := s.resLE_comp_ι _
  have ht : tW ≫ W.ι = V.ι ≫ t := t.resLE_comp_ι _
  obtain ⟨eW, he⟩ := factor_preimage s W (W.ι ≫ e) (𝟙 _) (by
    simp [Category.assoc, hG.identity_source])
  obtain ⟨iW, hi⟩ := factor_preimage s W (V.ι ≫ i) tW (by
    simpa [Category.assoc, hG.inverse_source] using ht.symm)
  let m := pullback.map sW tW s t V.ι V.ι W.ι hs ht
  have hm : m ≫ c ≫ s = (pullback.snd sW tW ≫ sW) ≫ W.ι := by
    simp [m, Category.assoc, hG.composition_source, hs]
  obtain ⟨cW, hc⟩ := factor_preimage s W (m ≫ c) (pullback.snd sW tW ≫ sW)
    (by simpa [Category.assoc] using hm)
  refine ⟨sW, tW, eW, iW, cW, hs, ht, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    exact ⟨fun h ↦ (cancel_mono W.ι).mp (h.trans hs.symm), fun h ↦ h ▸ hs⟩
  · intro f
    exact ⟨fun h ↦ (cancel_mono W.ι).mp (h.trans ht.symm), fun h ↦ h ▸ ht⟩
  · intro f
    exact ⟨fun h ↦ (cancel_mono V.ι).mp (h.trans he.symm), fun h ↦ h ▸ he⟩
  · intro f
    exact ⟨fun h ↦ (cancel_mono V.ι).mp (h.trans hi.symm), fun h ↦ h ▸ hi⟩
  · intro f
    exact ⟨fun h ↦ (cancel_mono V.ι).mp (h.trans hc.symm), fun h ↦ h ▸ hc⟩
  · have hGW := groupoid_of_mono s t e i c hG W.ι V.ι sW tW eW iW cW hs ht he hi hc
    have hii := inverse_involution sW tW eW iW cW hGW
    have hIso : IsIso iW := ⟨⟨iW, hii, hii⟩⟩
    exact ⟨hGW, hIso, hii, hGW.inverse_source,
      degree_transport sW tW iW hGW.inverse_source⟩

end AlgebraicGeometry
