/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q70, Y9
-/
module

public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.RingTheory.FreeRing
import Sheaf.AlgebraicGeometry.EnlargedSiteSchemeDensity
import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-! # Atlas descent and algebraic structures on enlarged étale sheaves

Source: Stacks Project, Properties of Spaces, Tags 03G1, 03H7 and the paragraph
following 03G7; Sites, Section 00YR; Modules on Sites, Tag 03CV
(blueprint: lem-trf-space-enlarged-atlas-algebraic-extension).

The site, inclusion, restriction and structure sheaves are the existing constructions.
Atlas identifications retain their restriction formula, including under refinement and
maps of sheaves. Module restriction uses the specified normalization of the ring extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

private theorem schemeInclusion_dense (X : AlgebraicSpace S) :
    (enlargedSchemeInclusion X).IsDenseSubsite X.etaleTopology X.enlargedEtaleTopology := by
  obtain ⟨_, _, _, _, _, ⟨ff⟩, _, _, atlases, special, _⟩ :=
    enlargedSite_scheme_density.{u, 0, 0} X
  let i := enlargedSchemeInclusion X
  let : i.Full := ⟨ff.map_surjective⟩
  let : i.Faithful := ⟨ff.map_injective⟩
  let : i.IsCocontinuous X.etaleTopology X.enlargedEtaleTopology := special.1
  let : i.IsCoverDense X.enlargedEtaleTopology :=
    Functor.isCoverDense_of_generate_singleton_functor_π_mem i _ (by
      intro T
      obtain ⟨U, a, _, _, ha⟩ := atlases T
      exact ⟨U, a, X.enlargedEtalePrecoverage.generate_mem_toGrothendieck ha⟩)
  refine { functorPushforward_mem_iff := ?_ }
  intro U R
  constructor
  · intro hR
    change Sieve.functorPushforward i R ∈ X.enlargedEtaleTopology _ at hR
    have h := i.cover_lift X.etaleTopology X.enlargedEtaleTopology hR
    rwa [Sieve.functorPullback_functorPushforward_eq] at h
  · exact (CoverPreserving.of_isContinuous i X.etaleTopology
      X.enlargedEtaleTopology).cover_preserve

private theorem coefficientRestriction_equivalence (X : AlgebraicSpace S)
    (A : Type v) [Category.{w} A] [HasLimitsOfSize.{0, 0} A] :
    (enlargedRestriction X A).IsEquivalence := by
  obtain ⟨_, _, _, ⟨limits⟩, _, ⟨ff⟩, _, _, atlases, _, _⟩ :=
    enlargedSite_scheme_density.{u, 0, 0} X
  let i := enlargedSchemeInclusion X
  let : i.Full := ⟨ff.map_surjective⟩
  let : i.Faithful := ⟨ff.map_injective⟩
  let : HasFiniteLimits X.EnlargedEtaleSite := limits
  let : i.IsDenseSubsite X.etaleTopology X.enlargedEtaleTopology := schemeInclusion_dense X
  let : i.IsOneHypercoverDense.{0} X.etaleTopology X.enlargedEtaleTopology :=
    Functor.IsOneHypercoverDense.of_hasPullbacks (by
      intro T
      obtain ⟨U, a, _, _, ha⟩ := atlases T
      exact ⟨Unit, fun _ ↦ U, fun _ ↦ a, by
        simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using
          X.enlargedEtalePrecoverage.generate_mem_toGrothendieck ha⟩)
  exact Functor.isEquivalence_of_isOneHypercoverDense.{0} i _ _ A

/-- Normalized set extensions exist uniquely, and maps extend uniquely with their
scheme-section formula. Restriction preserves finite products, including the empty product,
and is an equivalence for commutative-ring sheaves.
Source: Stacks 03G1, 03H7; Sites 00W2 and Section 00YR
(blueprint: lem-trf-space-enlarged-atlas-algebraic-extension).

Proof: scheme density supplies fully faithful inclusion, singleton covering scheme
atlases and finite limits. Mathlib's one-hypercover dense comparison gives restriction
equivalences for all finitely complete coefficient categories, including sets and rings.
Choose a preimage and its restriction isomorphism. Lift `e.hom ≫ d.inv` uniquely;
full faithfulness lifts it to an isomorphism. Lift a map `b` using
`e.hom ≫ b ≫ d.inv`; naturality gives the formula on each scheme chart. Uniqueness
follows from faithfulness. Equivalences preserve finite products and the terminal
object. Apply the same comparison to commutative rings for the final conjunct. -/
theorem enlargedAtlas_algebraic_extension (X : AlgebraicSpace S) :
    (∀ F : Sheaf X.etaleTopology (Type (max (u + 1) w)),
      ∃ E : Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)),
        Nonempty ((enlargedRestriction X _).obj E ≅ F)) ∧
    (∀ (F : Sheaf X.etaleTopology (Type (max (u + 1) w)))
      (E E' : Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)))
      (e : (enlargedRestriction X _).obj E ≅ F)
      (e' : (enlargedRestriction X _).obj E' ≅ F),
      ∃! a : E ≅ E', (enlargedRestriction X _).map a.hom ≫ e'.hom = e.hom) ∧
    (∀ (F G : Sheaf X.etaleTopology (Type (max (u + 1) w)))
      (E H : Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)))
      (e : (enlargedRestriction X _).obj E ≅ F)
      (d : (enlargedRestriction X _).obj H ≅ G) (b : F ⟶ G),
      ∃! a : E ⟶ H,
        (enlargedRestriction X _).map a ≫ d.hom = e.hom ≫ b ∧
        ∀ (T : X.EnlargedEtaleSite) (U : X.EtaleSite)
          (p : (enlargedSchemeInclusion X).obj U ⟶ T) (x : E.obj.obj (op T)),
          d.hom.hom.app (op U) (H.obj.map p.op (a.hom.app (op T) x)) =
            b.hom.app (op U) (e.hom.hom.app (op U) (E.obj.map p.op x))) ∧
    PreservesFiniteProducts (enlargedRestriction X (Type (max (u + 1) w))) ∧
    (enlargedRestriction X CommRingCat.{v}).IsEquivalence := by
  let r := enlargedRestriction X (Type (max (u + 1) w))
  let : r.IsEquivalence := coefficientRestriction_equivalence X _
  refine ⟨?_, ?_, ?_, ?_, coefficientRestriction_equivalence X CommRingCat.{v}⟩
  · intro F
    exact ⟨r.objPreimage F, ⟨r.objObjPreimageIso F⟩⟩
  · intro F E E' e e'
    refine ⟨r.preimageIso (e ≪≫ e'.symm), ?_, ?_⟩
    · change r.map (r.preimage (e.hom ≫ e'.inv)) ≫ e'.hom = e.hom
      simp
    · intro a ha
      apply Iso.ext
      apply r.map_injective
      apply (cancel_mono e'.hom).mp
      simpa [Functor.preimageIso] using ha
  · intro F G E H e d b
    let a := r.preimage (e.hom ≫ b ≫ d.inv)
    have hmap : r.map a ≫ d.hom = e.hom ≫ b := by simp [a]
    refine ⟨a, ⟨hmap, ?_⟩, ?_⟩
    · intro T U p x
      have hn := ConcreteCategory.congr_hom (a.hom.naturality p.op) x
      change a.hom.app (op ((enlargedSchemeInclusion X).obj U))
          (E.obj.map p.op x) = H.obj.map p.op (a.hom.app (op T) x) at hn
      rw [← hn]
      exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (congrArg (fun k : r.obj E ⟶ G ↦ k.hom) hmap) (op U)) (E.obj.map p.op x)
    · intro a' ha'
      apply r.map_injective
      apply (cancel_mono d.hom).mp
      exact ha'.1.trans hmap.symm
  · infer_instance

private theorem schemeChart_pullback (X : AlgebraicSpace S)
    (T : X.EnlargedEtaleSite) (U U' : X.EtaleSite)
    (a : (enlargedSchemeInclusion X).obj U ⟶ T)
    (b : (enlargedSchemeInclusion X).obj U' ⟶ T)
    (ha : IsEtale a.hom.left.hom.hom) :
    ∃ (W : X.EtaleSite) (p : W ⟶ U') (q : W ⟶ U),
      IsPullback ((enlargedSchemeInclusion X).map p)
        ((enlargedSchemeInclusion X).map q) b a ∧ Etale ((etaleForget X).map p) ∧
      (IsSurjective a.hom.left.hom.hom → Surjective ((etaleForget X).map p)) := by
  obtain ⟨V, r, c, hc, hr⟩ := ha U'.obj.left b.hom.left.hom.hom
  let s := yoneda.preimage c
  have hs : yoneda.map s = c := yoneda.map_preimage c
  have aw : a.hom.left.hom.hom ≫ T.obj.hom.hom.hom = U.obj.hom :=
    congrArg (fun k ↦ k.hom.hom) a.hom.w
  have bw : b.hom.left.hom.hom ≫ T.obj.hom.hom.hom = U'.obj.hom :=
    congrArg (fun k ↦ k.hom.hom) b.hom.w
  have sw : yoneda.map s ≫ U.obj.hom = yoneda.map r ≫ U'.obj.hom := by
    rw [hs, ← aw, ← bw, ← Category.assoc, hc.w, Category.assoc]
  have re : IsEtale (yoneda.map r) :=
    (representable_etale_scheme_tests (S := S)).2.2.2.2.2.2.2.1 _ _ r |>.mpr hr
  let W : X.EtaleSite := ⟨CostructuredArrow.mk (yoneda.map r ≫ U'.obj.hom),
    isEtale_comp _ _ re U'.property⟩
  let p : W ⟶ U' := ObjectProperty.homMk (CostructuredArrow.homMk r rfl)
  let q : W ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk s sw)
  refine ⟨W, p, q, ?_, hr, ?_⟩
  · let forget : X.EnlargedEtaleSite ⥤ (Over S)ᵒᵖ ⥤ Type u :=
      ObjectProperty.ι _ ⋙ Over.forget X ⋙ ObjectProperty.ι _ ⋙ sheafToPresheaf _ _
    apply IsPullback.of_map_of_faithful forget
    change IsPullback (yoneda.map r) (yoneda.map s) b.hom.left.hom.hom
      a.hom.left.hom.hom
    rw [hs]
    exact hc.flip
  · intro ha'
    let P : MorphismProperty (Over S) :=
      MorphismProperty.inverseImage @Surjective (Over.forget S)
    have hrel : P.relative yoneda a.hom.left.hom.hom := by
      apply MorphismProperty.relative.of_exists
      intro Z z
      obtain ⟨V, r, q, hq, hr⟩ := ha' Z z
      exact ⟨V, q, r, hq, hr⟩
    exact hrel.property b.hom.left.hom.hom c r hc

-- Direct singleton-cover gluing, as in the enlarged-site equalizer construction.
private theorem normalizedChart_equalizer (X : AlgebraicSpace S)
    (F : Sheaf X.etaleTopology (Type (max (u + 1) w)))
    (G : Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)))
    (e : (enlargedRestriction X _).obj G ≅ F)
    (T : X.EnlargedEtaleSite) (T₀ T₁ : X.EtaleSite)
    (a : (enlargedSchemeInclusion X).obj T₀ ⟶ T)
    (ha : IsEtale a.hom.left.hom.hom ∧ IsSurjective a.hom.left.hom.hom)
    (p q : T₁ ⟶ T₀)
    (hsq : IsPullback ((enlargedSchemeInclusion X).map p)
      ((enlargedSchemeInclusion X).map q) a a) :
    ∃ b : G.obj.obj (op T) ≃
        {s : F.obj.obj (op T₀) // F.obj.map p.op s = F.obj.map q.op s},
      ∀ x, (b x).val = e.hom.hom.app (op T₀) (G.obj.map a.op x) := by
  classical
  let i := enlargedSchemeInclusion X
  have cover : Presieve.singleton a ∈ X.enlargedEtalePrecoverage T := by
    constructor
    · intro U b hb
      cases hb
      intro V c hc
      exact isEtale_comp _ _ hc ha.1
    · intro K _ s x
      obtain ⟨U, r, q, hq, hr⟩ := ha.2 (Over.mk s) (yonedaEquiv.symm x)
      have := hr
      obtain ⟨y, _⟩ := r.left.surjective (IsLocalRing.closedPoint K)
      let L : Type u := U.left.residueField y
      let instL : Field L := inferInstance
      let d : K →+* L := (Spec.preimage (U.left.fromSpecResidueField y ≫ r.left)).hom
      have hd : Spec.map (CommRingCat.ofHom d) =
          U.left.fromSpecResidueField y ≫ r.left := Spec.map_preimage _
      let t : Over.mk (Spec.map (CommRingCat.ofHom d) ≫ s) ⟶ U :=
        Over.homMk (U.left.fromSpecResidueField y) (by
          change U.left.fromSpecResidueField y ≫ U.hom =
            Spec.map (CommRingCat.ofHom d) ≫ s
          rw [hd, Category.assoc]
          exact congrArg (fun k ↦ U.left.fromSpecResidueField y ≫ k) (Over.w r).symm)
      have ht : t ≫ r = Over.homMk (Spec.map (CommRingCat.ofHom d)) rfl := by
        apply Over.OverMorphism.ext
        exact hd.symm
      refine ⟨⟨⟨i.obj T₀, a⟩, Presieve.singleton_self a⟩, L, instL, d,
        q.app _ t, ?_⟩
      have h := congrArg (fun k ↦ k.app
        (op (Over.mk (Spec.map (CommRingCat.ofHom d) ≫ s))) t) hq.w
      change a.hom.left.hom.hom.app _ (q.app _ t) =
        (yonedaEquiv.symm x).app _ (t ≫ r) at h
      change a.hom.left.hom.hom.app _ (q.app _ t) =
        T.obj.left.obj.obj.map (t ≫ r).op x at h
      rw [ht] at h
      exact h
  have sh : Presieve.IsSheafFor G.obj (Presieve.singleton a) :=
    ((isSheaf_iff_isSheaf_of_type X.enlargedEtaleTopology G.obj).1 G.property).isSheafFor _
      (X.enlargedEtalePrecoverage.generate_mem_toGrothendieck cover)
  have glue (s : G.obj.obj (op (i.obj T₀)))
      (hs : G.obj.map (i.map p).op s = G.obj.map (i.map q).op s) :
      ∃! x, G.obj.map a.op x = s := by
    apply (Presieve.isSheafFor_singleton.1 sh) s
    intro V b c hbc
    let l := hsq.lift b c hbc
    have hlp : l ≫ i.map p = b := hsq.lift_fst b c hbc
    have hlq : l ≫ i.map q = c := hsq.lift_snd b c hbc
    calc
      G.obj.map b.op s = G.obj.map l.op (G.obj.map (i.map p).op s) := by
        rw [← G.obj.map_comp_apply, ← op_comp, hlp]
      _ = G.obj.map l.op (G.obj.map (i.map q).op s) := congrArg (G.obj.map l.op) hs
      _ = G.obj.map c.op s := by rw [← G.obj.map_comp_apply, ← op_comp, hlq]
  have nh (b : T₁ ⟶ T₀) (s : G.obj.obj (op (i.obj T₀))) :
      e.hom.hom.app (op T₁) (G.obj.map (i.map b).op s) =
        F.obj.map b.op (e.hom.hom.app (op T₀) s) :=
    ConcreteCategory.congr_hom (e.hom.hom.naturality b.op) s
  have ni (b : T₁ ⟶ T₀) (s : F.obj.obj (op T₀)) :
      e.inv.hom.app (op T₁) (F.obj.map b.op s) =
        G.obj.map (i.map b).op (e.inv.hom.app (op T₀) s) :=
    ConcreteCategory.congr_hom (e.inv.hom.naturality b.op) s
  let b : G.obj.obj (op T) →
      {s : F.obj.obj (op T₀) // F.obj.map p.op s = F.obj.map q.op s} := fun x ↦
    ⟨e.hom.hom.app (op T₀) (G.obj.map a.op x), by
      rw [← nh, ← nh]
      congr 1
      rw [← G.obj.map_comp_apply, ← G.obj.map_comp_apply, ← op_comp, ← op_comp, hsq.w]⟩
  have hb : Function.Bijective b := by
    constructor
    · intro x y hxy
      apply (Presieve.isSeparatedFor_singleton.1 sh.isSeparatedFor)
      have h := congrArg Subtype.val hxy
      exact (((sheafToPresheaf _ _).mapIso e).app (op T₀)).toEquiv.injective h
    · intro s
      have hs : G.obj.map (i.map p).op (e.inv.hom.app (op T₀) s.val) =
          G.obj.map (i.map q).op (e.inv.hom.app (op T₀) s.val) := by
        rw [← ni, ← ni, s.property]
      obtain ⟨x, hx, _⟩ := glue (e.inv.hom.app (op T₀) s.val) hs
      refine ⟨x, Subtype.ext ?_⟩
      change e.hom.hom.app (op T₀) (G.obj.map a.op x) = s.val
      rw [hx]
      exact ConcreteCategory.congr_hom
        (((sheafToPresheaf _ _).mapIso e).inv_hom_id_app (op T₀)) s.val
  exact ⟨Equiv.ofBijective b hb, fun _ ↦ rfl⟩

/-- Every atlas has a scheme overlap; every scheme presentation of it computes the
extension by the indicated equalizer, whose map is restriction followed by normalization.
Source: Stacks 03H7
(blueprint: lem-trf-space-enlarged-atlas-algebraic-extension).

Proof: representable-etale scheme tests construct the overlap as a scheme. Etale
composition makes it an object of the small site. The chart is chartwise étale and jointly
surjective: a field point lifts after extending to
a residue field of the nonempty scheme fibre. Thus it is a singleton covering. Its
sheaf equalizer, transported along `e`, gives the bijection. Its composite into the
chart sections is exactly the displayed restriction formula and determines it uniquely.
This uses def-weil-pbc-sites-and-cohomology and
 def-trf-algebraic-space-jointly-surjective-family. -/
theorem enlargedAtlas_equalizer (X : AlgebraicSpace S)
    (F : Sheaf X.etaleTopology (Type (max (u + 1) w)))
    (E : Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)))
    (e : (enlargedRestriction X _).obj E ≅ F)
    (T : X.EnlargedEtaleSite) (U : X.EtaleSite)
    (a : (enlargedSchemeInclusion X).obj U ⟶ T)
    (ha : IsEtale a.hom.left.hom.hom ∧ IsSurjective a.hom.left.hom.hom) :
    (∃ (V : X.EtaleSite) (p q : V ⟶ U),
      IsPullback ((enlargedSchemeInclusion X).map p)
        ((enlargedSchemeInclusion X).map q) a a) ∧
    (∀ (V : X.EtaleSite) (p q : V ⟶ U),
      IsPullback ((enlargedSchemeInclusion X).map p)
        ((enlargedSchemeInclusion X).map q) a a →
      ∃! b : E.obj.obj (op T) ≃
          {s : F.obj.obj (op U) // F.obj.map p.op s = F.obj.map q.op s},
        ∀ x : E.obj.obj (op T),
          (b x).val = e.hom.hom.app (op U) (E.obj.map a.op x)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨V, p, q, hpq, _, _⟩ := schemeChart_pullback X T U U a a ha.1
    exact ⟨V, p, q, hpq⟩
  · intro V p q hpq
    obtain ⟨b, hb⟩ := normalizedChart_equalizer X F E e T U V a ha p q hpq
    refine ⟨b, hb, ?_⟩
    intro c hc
    apply Equiv.ext
    intro x
    exact Subtype.ext ((hc x).trans (hb x).symm)

/-- Common scheme refinements compare the normalized atlas coordinates under every
restriction. Taking `h` to be the identity compares two charts of the same object.
Source: Stacks 03H7, the equalizer and its refinement interpretation
(blueprint: lem-trf-space-enlarged-atlas-algebraic-extension).

Proof: represent `U' ×_T U` by a scheme, using
lem-trf-space-fibre-products-etale-covers. Chartwise permanence makes it an object
of the small site; its projection to `U'` is surjective étale. Both composites to
`T` agree by the pullback square. Naturality of `e` identifies the two displayed
sections with the restriction of the original section to that common refinement.
The sheaf condition makes restriction from `U'` to this covering injective, so the
comparison determines restrictions uniquely. With `h = 1` it gives independence
of charts, and with consecutive maps it gives composition compatibility. Together
with the normalized lift of sheaf maps in enlargedAtlas_algebraic_extension this
also proves naturality in `F`. -/
theorem enlargedAtlas_refinement (X : AlgebraicSpace S)
    (F : Sheaf X.etaleTopology (Type (max (u + 1) w)))
    (E : Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)))
    (e : (enlargedRestriction X _).obj E ≅ F)
    (T T' : X.EnlargedEtaleSite) (h : T' ⟶ T) (U U' : X.EtaleSite)
    (a : (enlargedSchemeInclusion X).obj U ⟶ T)
    (a' : (enlargedSchemeInclusion X).obj U' ⟶ T')
    (ha : IsEtale a.hom.left.hom.hom ∧ IsSurjective a.hom.left.hom.hom)
    (ha' : IsEtale a'.hom.left.hom.hom ∧ IsSurjective a'.hom.left.hom.hom) :
    ∃ (W : X.EtaleSite) (p : W ⟶ U') (q : W ⟶ U),
      Etale ((etaleForget X).map p) ∧ Surjective ((etaleForget X).map p) ∧
      (enlargedSchemeInclusion X).map p ≫ a' ≫ h =
        (enlargedSchemeInclusion X).map q ≫ a ∧
      Function.Injective (F.obj.map p.op) ∧
      ∀ x : E.obj.obj (op T),
        F.obj.map p.op (e.hom.hom.app (op U') (E.obj.map a'.op (E.obj.map h.op x))) =
          F.obj.map q.op (e.hom.hom.app (op U) (E.obj.map a.op x)) := by
  obtain ⟨_ha'e, _ha's⟩ := ha'
  obtain ⟨W, p, q, hpq, hp, hps⟩ :=
    schemeChart_pullback X T U U' a (a' ≫ h) ha.1
  have hsurj := hps ha.2
  have hcover : Presieve.singleton p ∈ X.etalePrecoverage U' := by
    refine ⟨?_, ?_⟩
    · intro V f hf
      cases hf
      exact hp
    · intro x
      obtain ⟨y, hy⟩ := hsurj.surj x
      exact ⟨W, p, ⟨⟩, y, hy⟩
  have hinj : Function.Injective (F.obj.map p.op) :=
    Presieve.isSeparatedFor_singleton.mp
      (((isSheaf_iff_isSheaf_of_type _ _).mp F.property).isSheafFor_of_mem_precoverage
        hcover).isSeparatedFor
  refine ⟨W, p, q, hp, hsurj, hpq.w, hinj, ?_⟩
  intro x
  have natural (A B : X.EtaleSite) (f : A ⟶ B)
      (z : E.obj.obj (op ((enlargedSchemeInclusion X).obj B))) :
      F.obj.map f.op (e.hom.hom.app (op B) z) =
        e.hom.hom.app (op A) (E.obj.map ((enlargedSchemeInclusion X).map f).op z) :=
    (ConcreteCategory.congr_hom (e.hom.hom.naturality f.op) z).symm
  rw [natural, natural]
  congr 1
  change (E.obj.map h.op ≫ E.obj.map a'.op ≫
      E.obj.map ((enlargedSchemeInclusion X).map p).op) x =
    (E.obj.map a.op ≫ E.obj.map ((enlargedSchemeInclusion X).map q).op) x
  rw [← E.obj.map_comp, ← E.obj.map_comp, ← E.obj.map_comp]
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ E.obj.map f.op) hpq.w) x

end AlgebraicGeometry.AlgebraicSpace

namespace SheafOfModules.EnlargedAtlasDescent

universe u₁ v₁ u₂ v₂ r
open CategoryTheory.MonoidalCategory

-- The operation-lifting argument of DenseSubsiteModuleRestriction, with the
-- scalar universe independent of the universe of module sections.
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
  [F.IsContinuous J K]
  [(F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w r} J K).IsEquivalence]
  [(F.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w r)) J K).IsEquivalence]
  (R : Sheaf K RingCat.{r})
private noncomputable def moduleLift (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w r}
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R)) :=
  (F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w r} J K).inv.obj ((toSheaf _).obj M)
private noncomputable def moduleLiftIso (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w r}
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R)) :
    (F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w r} J K).obj (moduleLift J K F R M) ≅
      (toSheaf _).obj M :=
  (F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w r} J K).asEquivalence.counitIso.app _
private instance scalarSheafCompose : K.HasSheafCompose
    (CategoryTheory.forget RingCat.{r} ⋙ uliftFunctor.{w, r}) where
  isSheaf P hP := by
    apply (isSheaf_iff_isSheaf_of_type _ _).2
    change Presieve.IsSheaf K ((P ⋙ CategoryTheory.forget RingCat.{r}) ⋙ uliftFunctor)
    apply Presieve.isSheaf_comp_uliftFunctor K
    let A := RingCat.of (FreeRing PUnit.{r + 1})
    let e (U : D) : (A ⟶ P.obj (op U)) ≃ (P.obj (op U) : Type r) :=
      { toFun := fun f ↦ f.hom (FreeRing.of PUnit.unit)
        invFun := fun x ↦ RingCat.ofHom (FreeRing.lift (fun _ ↦ x))
        left_inv := by
          intro f
          apply RingCat.hom_ext
          apply FreeRing.hom_ext
          intro x
          cases x
          exact FreeRing.lift_of _ _
        right_inv := by intro x; exact FreeRing.lift_of _ _ }
    exact Presieve.isSheaf_of_nat_equiv (fun {U} ↦ e U)
      (by intros; rfl) (hP A)

private noncomputable def restrictedAction (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w r}
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R)) :
    (F.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w r)) J K).obj (
      (sheafCompose K (CategoryTheory.forget RingCat.{r} ⋙
        uliftFunctor.{max u₁ v₁ u₂ v₂ w, r})).obj R ⊗
      (sheafCompose K (CategoryTheory.forget Ab.{max u₁ v₁ u₂ v₂ w r})).obj
        (moduleLift J K F R M)) ⟶
      (F.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w r)) J K).obj
        ((sheafCompose K (CategoryTheory.forget Ab.{max u₁ v₁ u₂ v₂ w r})).obj
          (moduleLift J K F R M)) := by
  let e := moduleLiftIso J K F R M
  refine ⟨{ app := fun U ↦ ↾fun x ↦ e.inv.hom.app U
              (x.1.down • (show M.val.obj U from e.hom.hom.app U x.2))
            naturality := ?_ }⟩
  intro U V f
  ext x
  symm
  change (moduleLift J K F R M).obj.map (F.op.map f)
      (e.inv.hom.app U (x.1.down • (show M.val.obj U from e.hom.hom.app U x.2))) =
    e.inv.hom.app V (R.obj.map (F.op.map f) x.1.down •
      (show M.val.obj V from
      e.hom.hom.app V ((moduleLift J K F R M).obj.map (F.op.map f) x.2)))
  have hi := congrArg (fun t ↦ t
    (x.1.down • (show M.val.obj U from e.hom.hom.app U x.2))) (e.inv.hom.naturality f)
  have hh := congrArg (fun t ↦ t x.2) (e.hom.hom.naturality f)
  change _ = (moduleLift J K F R M).obj.map (F.op.map f)
    (e.inv.hom.app U (x.1.down • (show M.val.obj U from e.hom.hom.app U x.2))) at hi
  rw [← hi]
  change e.hom.hom.app V ((moduleLift J K F R M).obj.map (F.op.map f) x.2) =
    M.val.map f (e.hom.hom.app U x.2) at hh
  exact congrArg (fun m : M.val.obj V ↦ e.inv.hom.app V m)
    ((M.val.map_smul f x.1.down (e.hom.hom.app U x.2)).trans
      (congrArg (fun m : M.val.obj V ↦ R.obj.map (F.op.map f) x.1.down • m) hh.symm))
private noncomputable def liftAction (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w r}
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R)) :=
  (F.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w r)) J K).preimage
    (restrictedAction J K F R M)

private noncomputable def liftSmul (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w r}
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R))
    (U : Dᵒᵖ) (r : R.obj.obj U) (m : (moduleLift J K F R M).obj.obj U) :
    (moduleLift J K F R M).obj.obj U :=
  (liftAction J K F R M).hom.app U (ULift.up r, m)

private theorem liftSmul_naturality (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w r}
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R))
    {U V : Dᵒᵖ} (f : U ⟶ V) (r : R.obj.obj U)
    (m : (moduleLift J K F R M).obj.obj U) :
    (moduleLift J K F R M).obj.map f (liftSmul J K F R M U r m) =
      liftSmul J K F R M V (R.obj.map f r) ((moduleLift J K F R M).obj.map f m) := by
  exact (congrArg (fun t ↦ t (ULift.up r, m)) ((liftAction J K F R M).hom.naturality f)).symm

private theorem liftSmul_apply (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w r}
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R))
    (U : Cᵒᵖ) (r : R.obj.obj (F.op.obj U))
    (m : (moduleLift J K F R M).obj.obj (F.op.obj U)) :
    (moduleLiftIso J K F R M).hom.hom.app U (liftSmul J K F R M (F.op.obj U) r m) =
      r • (show M.val.obj U from (moduleLiftIso J K F R M).hom.hom.app U m) := by
  have h := congrArg (fun t ↦ t.hom.app U (ULift.up r, m))
    ((F.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w r)) J K).map_preimage
      (restrictedAction J K F R M))
  change liftSmul J K F R M (F.op.obj U) r m = _ at h
  rw [h]
  dsimp only [restrictedAction]
  exact congrArg (fun t ↦ t.hom.app U
    (r • (show M.val.obj U from (moduleLiftIso J K F R M).hom.hom.app U m)))
      (moduleLiftIso J K F R M).inv_hom_id
variable [F.IsCoverDense K]

omit [(F.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w r)) J K).IsEquivalence] in
private theorem lift_ext (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w r}
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R))
    (U : Dᵒᵖ) (x y : (moduleLift J K F R M).obj.obj U)
    (h : ∀ (V : C) (f : F.obj V ⟶ U.unop),
      (moduleLiftIso J K F R M).hom.hom.app (op V)
        ((moduleLift J K F R M).obj.map f.op x) =
      (moduleLiftIso J K F R M).hom.hom.app (op V)
        ((moduleLift J K F R M).obj.map f.op y)) : x = y := by
  apply Functor.IsCoverDense.ext F
    ((sheafCompose K (CategoryTheory.forget Ab.{max u₁ v₁ u₂ v₂ w r})).obj
      (moduleLift J K F R M)) U.unop
  intro V f
  exact (ConcreteCategory.bijective_of_isIso
    ((moduleLiftIso J K F R M).hom.hom.app (op V))).1 (h V f)

@[instance_reducible]
private noncomputable def liftModule (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w r}
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R))
    (U : Dᵒᵖ) : Module (R.obj.obj U) ((moduleLift J K F R M).obj.obj U) where
  smul := liftSmul J K F R M U
  one_smul m := by
    apply lift_ext J K F R M U
    intro V f
    erw [liftSmul_naturality, liftSmul_apply]
    simp only [map_one, one_smul]
  mul_smul r s m := by
    apply lift_ext J K F R M U
    intro V f
    erw [liftSmul_naturality, liftSmul_apply, liftSmul_naturality,
      liftSmul_apply, liftSmul_naturality, liftSmul_apply]
    simp only [map_mul, mul_smul]
  smul_zero r := by
    apply lift_ext J K F R M U
    intro V f
    erw [liftSmul_naturality, liftSmul_apply]
    simp only [map_zero, smul_zero]
  smul_add r m n := by
    apply lift_ext J K F R M U
    intro V f
    erw [liftSmul_naturality, liftSmul_apply]
    simp only [map_add, smul_add]
    erw [liftSmul_naturality, liftSmul_apply, liftSmul_naturality, liftSmul_apply]
  add_smul r s m := by
    apply lift_ext J K F R M U
    intro V f
    erw [liftSmul_naturality, liftSmul_apply]
    simp only [map_add, add_smul]
    erw [liftSmul_naturality, liftSmul_apply, liftSmul_naturality, liftSmul_apply]
  zero_smul m := by
    apply lift_ext J K F R M U
    intro V f
    erw [liftSmul_naturality, liftSmul_apply]
    simp only [map_zero, zero_smul]
private noncomputable def liftedModule (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w r}
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R)) :
    SheafOfModules.{max u₁ v₁ u₂ v₂ w r} R := by
  let (U : Dᵒᵖ) := liftModule J K F R M U
  exact ⟨PresheafOfModules.ofPresheaf (moduleLift J K F R M).obj
    (fun {_ _} f r m ↦ liftSmul_naturality J K F R M f r m),
      (moduleLift J K F R M).property⟩

private noncomputable def liftedModuleIso (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w r}
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R)) :
    (pushforward.{max u₁ v₁ u₂ v₂ w r} (F := F) (J := J) (𝟙
      ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R))).obj
        (liftedModule J K F R M) ≅ M := by
  let α : (pushforward.{max u₁ v₁ u₂ v₂ w r} (F := F) (J := J) (𝟙
      ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R))).obj
        (liftedModule J K F R M) ⟶ M :=
    ⟨PresheafOfModules.homMk (moduleLiftIso J K F R M).hom.hom
      (fun U r m ↦ liftSmul_apply J K F R M U r m)⟩
  have : IsIso ((toSheaf _).map α) := by
    change IsIso (moduleLiftIso J K F R M).hom
    infer_instance
  have : IsIso α := isIso_of_reflects_iso α (toSheaf _)
  exact asIso α
/-- Dense restriction equivalences on sets and abelian groups lift to arbitrary
ring-sheaf modules.

Source: Bhatt--Scholze, Example 4.2.11, transport of coefficient structures
Adapted privately from Sheaf.CategoryTheory.DenseSubsiteModuleRestriction;
the scalar universe is independent of the section universe here.

Proof: Lift the underlying abelian sheaf through the restriction equivalence.
Conjugate the scalar action by its counit isomorphism on the smaller site and lift
this map of set sheaves using fullness of restriction. Check each module law on
covering test objects, where it is the original module law. Naturality gives a
presheaf of modules and its abelian sheaf property gives a sheaf of modules.
The counit isomorphism is linear, proving essential surjectivity. A map lifts by
fullness on abelian sheaves; test scalar compatibility on the dense subsite to
prove it is linear. Faithfulness follows from faithfulness on abelian sheaves. -/
private theorem isEquivalence_pushforward_of_dense :
    (pushforward.{max u₁ v₁ u₂ v₂ w r} (F := F) (J := J) (𝟙
      ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R))).IsEquivalence := by
  let P := pushforward.{max u₁ v₁ u₂ v₂ w r} (F := F) (J := J) (𝟙
    ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R))
  have : P.Faithful := by
    constructor
    intro M N f g h
    apply (toSheaf R).map_injective
    apply (F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w r} J K).map_injective
    exact congrArg ((toSheaf _).map) h
  have : P.Full := by
    constructor
    intro M N f
    let α := (F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w r} J K).preimage
      (X := (toSheaf R).obj M) (Y := (toSheaf R).obj N) ((toSheaf _).map f)
    have hα := (F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w r} J K).map_preimage
      (X := (toSheaf R).obj M) (Y := (toSheaf R).obj N) ((toSheaf _).map f)
    have happ (V : Cᵒᵖ) (m : M.val.obj (F.op.obj V)) :
        α.hom.app (F.op.obj V) m = f.val.app V m := by
      exact congrArg (fun t ↦ t.hom.app V m) hα
    have hlin (U : Dᵒᵖ) (r : R.obj.obj U) (m : M.val.obj U) :
        α.hom.app U (r • m) = r • (show N.val.obj U from α.hom.app U m) := by
      apply Functor.IsCoverDense.ext F
        ((sheafCompose K (CategoryTheory.forget Ab.{max u₁ v₁ u₂ v₂ w r})).obj
          ((toSheaf R).obj N)) U.unop
      intro V g
      have hn (x : M.val.obj U) :
          N.val.map g.op (α.hom.app U x) =
            α.hom.app (op (F.obj V)) (M.val.map g.op x) :=
        (congrArg (fun t ↦ t x) (α.hom.naturality g.op)).symm
      change N.val.map g.op (α.hom.app U (r • m)) =
        N.val.map g.op (r • (show N.val.obj U from α.hom.app U m))
      rw [hn, M.val.map_smul, N.val.map_smul, hn]
      erw [happ (op V), happ (op V)]
      exact (f.val.app (op V)).hom.map_smul _ _
    refine ⟨⟨PresheafOfModules.homMk α.hom hlin⟩, ?_⟩
    apply (toSheaf _).map_injective
    exact hα
  have : P.EssSurj := ⟨fun M ↦ ⟨liftedModule J K F R M, ⟨liftedModuleIso J K F R M⟩⟩⟩
  change P.IsEquivalence
  exact {}

-- Keep transport abstract and its coefficient universes explicit.
private theorem isEquivalence_normalized_pushforward_of_dense
    (R₀ : Sheaf J RingCat.{r})
    (e : (F.sheafPushforwardContinuous RingCat.{r} J K).obj R ≅ R₀) :
    (pushforward.{max u₁ v₁ u₂ v₂ w r} (F := F) (J := J) e.inv).IsEquivalence := by
  let R₁ := (F.sheafPushforwardContinuous RingCat.{r} J K).obj R
  let P := pushforward.{max u₁ v₁ u₂ v₂ w r} (F := F) (J := J) (𝟙 R₁)
  have : P.IsEquivalence := isEquivalence_pushforward_of_dense J K F R
  let Q := pushforward.{max u₁ v₁ u₂ v₂ w r}
    (F := 𝟭 C) (J := J) (K := J) (R := R₁) (S := R₀) e.inv
  let eqv : C ≌ C :=
    { functor := 𝟭 _
      inverse := 𝟭 _
      unitIso := Iso.refl _
      counitIso := Iso.refl _ }
  let : eqv.functor.IsContinuous J J :=
    show (𝟭 C).IsContinuous J J from inferInstance
  let : eqv.inverse.IsContinuous J J :=
    show (𝟭 C).IsContinuous J J from inferInstance
  let E : SheafOfModules.{max u₁ v₁ u₂ v₂ w r} R₁ ≌
      SheafOfModules.{max u₁ v₁ u₂ v₂ w r} R₀ :=
    pushforwardPushforwardEquivalence.{max u₁ v₁ u₂ v₂ w r} (J := J) (K := J)
      (R := R₁) (S := R₀) eqv e.inv e.hom
      (by
        ext U : 2
        change R₁.obj.map (𝟙 U) = e.hom.hom.app U ≫ e.inv.hom.app U
        rw [R₁.obj.map_id]
        exact (NatTrans.congr_app (congrArg (fun f : R₁ ⟶ R₁ ↦ f.hom)
          e.hom_inv_id) U).symm)
      (by
        ext U : 2
        change e.inv.hom.app U ≫ e.hom.hom.app U ≫ R₀.obj.map (𝟙 U) = 𝟙 _
        rw [R₀.obj.map_id, Category.comp_id]
        exact NatTrans.congr_app (congrArg (fun f : R₀ ⟶ R₀ ↦ f.hom)
          e.inv_hom_id) U)
  have : Q.IsEquivalence := E.isEquivalence_functor
  let : ((𝟭 C) ⋙ F).IsContinuous J K := Functor.isContinuous_comp _ _ J J K
  have h : e.inv ≫ ((𝟭 C).sheafPushforwardContinuous RingCat.{r} J J).map
      (𝟙 R₁) = e.inv := by
    change e.inv ≫ 𝟙 R₁ = e.inv
    exact Category.comp_id _
  let iso₀ := pushforwardComp.{max u₁ v₁ u₂ v₂ w r} (F := 𝟭 C) (G := F)
    (J := J) (K := J) (K' := K) (S := R₀) (R := R₁) (R' := R) e.inv (𝟙 R₁)
  have iso : P ⋙ Q ≅ pushforward.{max u₁ v₁ u₂ v₂ w r}
      (F := F) (J := J) (K := K) e.inv :=
    iso₀ ≪≫ pushforwardCongr.{max u₁ v₁ u₂ v₂ w r}
      (F := (𝟭 C) ⋙ F) (J := J) (K := K) (R := R) (S := R₀) h
  exact Functor.isEquivalence_of_iso iso

end SheafOfModules.EnlargedAtlasDescent

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Restriction of module sheaves for the *given* normalized ring extension.
Source: Stacks 03H7 and Modules on Sites 03CV
(blueprint: lem-trf-space-enlarged-atlas-algebraic-extension).
The scalar map is `e.inv`, so on scheme sections a scalar `r` acts as `e.inv(r)`. -/
def normalizedEnlargedModuleRestriction (X : AlgebraicSpace S)
    (R : Sheaf X.etaleTopology RingCat.{v})
    (R' : Sheaf X.enlargedEtaleTopology RingCat.{v})
    (e : (enlargedRestriction X RingCat.{v}).obj R' ≅ R) :
    ringedSiteModules.{max (u + 1) v w} R' ⥤ ringedSiteModules.{max (u + 1) v w} R :=
  SheafOfModules.pushforward (F := enlargedSchemeInclusion X) e.inv

/-- The section identification for normalized module restriction is the identity on
underlying additive groups; no extension object or action is chosen here.
Source: Stacks 03H7, Modules on Sites 03CV
(blueprint: lem-trf-space-enlarged-atlas-algebraic-extension). -/
def normalizedEnlargedModuleSection (X : AlgebraicSpace S)
    (R : Sheaf X.etaleTopology RingCat.{v})
    (R' : Sheaf X.enlargedEtaleTopology RingCat.{v})
    (e : (enlargedRestriction X RingCat.{v}).obj R' ≅ R)
    (M : ringedSiteModules.{max (u + 1) v w} R') (U : X.EtaleSite) :
    ((normalizedEnlargedModuleRestriction X R R' e).obj M).val.obj (op U) ≃+
      M.val.obj (op ((enlargedSchemeInclusion X).obj U)) :=
  AddEquiv.refl _

private theorem normalizedModuleRestriction_isEquivalence (X : AlgebraicSpace S)
    (R : Sheaf X.etaleTopology RingCat.{v})
    (R' : Sheaf X.enlargedEtaleTopology RingCat.{v})
    (e : (enlargedRestriction X RingCat.{v}).obj R' ≅ R) :
    (normalizedEnlargedModuleRestriction.{u, v, w} X R R' e).IsEquivalence := by
  let i := enlargedSchemeInclusion X
  let J := X.etaleTopology
  let K := X.enlargedEtaleTopology
  let : i.IsDenseSubsite J K := schemeInclusion_dense X
  let : i.IsCoverDense K := Functor.IsDenseSubsite.isCoverDense J K i
  let : (i.sheafPushforwardContinuous Ab.{max (u + 1) v w} J K).IsEquivalence :=
    coefficientRestriction_equivalence X Ab.{max (u + 1) v w}
  let : (i.sheafPushforwardContinuous (Type (max (u + 1) v w)) J K).IsEquivalence :=
    coefficientRestriction_equivalence X (Type (max (u + 1) v w))
  exact SheafOfModules.EnlargedAtlasDescent.isEquivalence_normalized_pushforward_of_dense
    J K i R' R e

/-- Module equivalence for each normalized ring extension, with its addition, zero,
inverse, scalar action, restriction semilinearity and linearity of morphisms specified
on scheme sections. Full faithfulness detects and uniquely lifts these operations.
Source: Stacks 03H7; Sites Section 00YR; Modules on Sites 03CV
(blueprint: lem-trf-space-enlarged-atlas-algebraic-extension).

Proof: extend an underlying set sheaf by scheme density. Lift addition, zero and inverse
through full faithfulness and preservation of finite products. Lift the action using
the specified ring normalization, namely `e_N⁻¹ μ_N (e_R × e_N)`. Every abelian-group
and module law is an equation on finite products and follows by faithfulness from its
restriction. Naturality of the lifted action is restriction semilinearity. A morphism
is linear exactly when it respects addition and the action, so faithfulness detects
linearity and fullness uniquely lifts each linear map. Thus the specified restriction
is fully faithful and essentially surjective. Choose these normalized extensions and
unique lifts as an inverse; faithfulness gives the natural unit, counit and triangles.
The section formulas follow from the actual pushforward construction. Uniqueness of
all operation lifts follows from the hom-set bijection in the last conjunct, applied
to the finite products and terminal object preserved above. -/
theorem normalizedEnlargedModuleRestriction_equivalence (X : AlgebraicSpace S)
    (R : Sheaf X.etaleTopology RingCat.{v})
    (R' : Sheaf X.enlargedEtaleTopology RingCat.{v})
    (e : (enlargedRestriction X RingCat.{v}).obj R' ≅ R) :
    (normalizedEnlargedModuleRestriction.{u, v, w} X R R' e).IsEquivalence ∧
    (∀ (M : ringedSiteModules.{max (u + 1) v w} R') (U : X.EtaleSite),
      (∀ x y : ((normalizedEnlargedModuleRestriction X R R' e).obj M).val.obj (op U),
        normalizedEnlargedModuleSection X R R' e M U (x + y) =
          normalizedEnlargedModuleSection X R R' e M U x +
            normalizedEnlargedModuleSection X R R' e M U y) ∧
      normalizedEnlargedModuleSection X R R' e M U 0 = 0 ∧
      (∀ x : ((normalizedEnlargedModuleRestriction X R R' e).obj M).val.obj (op U),
        normalizedEnlargedModuleSection X R R' e M U (-x) =
          -normalizedEnlargedModuleSection X R R' e M U x) ∧
      (∀ (r : R.obj.obj (op U))
        (x : ((normalizedEnlargedModuleRestriction X R R' e).obj M).val.obj (op U)),
        normalizedEnlargedModuleSection X R R' e M U (r • x) =
          e.inv.hom.app (op U) r • normalizedEnlargedModuleSection X R R' e M U x)) ∧
    (∀ (M : ringedSiteModules.{max (u + 1) v w} R') (U V : X.EtaleSite)
      (f : V ⟶ U)
      (x : ((normalizedEnlargedModuleRestriction X R R' e).obj M).val.obj (op U)),
      normalizedEnlargedModuleSection X R R' e M V
          (((normalizedEnlargedModuleRestriction X R R' e).obj M).val.map f.op x) =
        M.val.map ((enlargedSchemeInclusion X).map f).op
          (normalizedEnlargedModuleSection X R R' e M U x)) ∧
    (∀ (M : ringedSiteModules.{max (u + 1) v w} R') (U V : X.EnlargedEtaleSite)
      (f : V ⟶ U) (r : R'.obj.obj (op U)) (x : M.val.obj (op U)),
      M.val.map f.op (r • x) = R'.obj.map f.op r • M.val.map f.op x) ∧
    (∀ (M N : ringedSiteModules.{max (u + 1) v w} R') (g : M ⟶ N)
      (U : X.EtaleSite)
      (x : ((normalizedEnlargedModuleRestriction X R R' e).obj M).val.obj (op U)),
      normalizedEnlargedModuleSection X R R' e N U
          (((normalizedEnlargedModuleRestriction X R R' e).map g).val.app (op U) x) =
        g.val.app (op ((enlargedSchemeInclusion X).obj U))
          (normalizedEnlargedModuleSection X R R' e M U x)) ∧
    (∀ (P Q : Sheaf X.enlargedEtaleTopology (Type (max (u + 1) v w)))
      (f : (enlargedRestriction X _).obj P ⟶ (enlargedRestriction X _).obj Q),
      ∃! g : P ⟶ Q, (enlargedRestriction X _).map g = f) := by
  refine ⟨normalizedModuleRestriction_isEquivalence X R R' e, ?_, ?_, ?_, ?_, ?_⟩
  · intro M U
    exact ⟨fun _ _ ↦ rfl, rfl, fun _ ↦ rfl, fun _ _ ↦ rfl⟩
  · intro M U V f x
    rfl
  · intro M U V f r x
    exact M.val.map_smul f.op r x
  · intro M N g U x
    rfl
  · intro P Q f
    let r := enlargedRestriction X (Type (max (u + 1) v w))
    let : r.IsEquivalence := coefficientRestriction_equivalence X _
    refine ⟨r.preimage f, r.map_preimage f, ?_⟩
    intro g hg
    exact r.map_injective (hg.trans (r.map_preimage f).symm)


/-- The same normalized atlas formula is an isomorphism of commutative rings, in
particular for the existing normalized extension of the structure sheaf.
Source: Stacks 03G7, 03H7
(blueprint: lem-trf-space-enlarged-atlas-algebraic-extension).

Proof: the compatible sections form the equalizer subring of the chart ring. Restriction
and the normalization are ring maps. The set equalizer proves that this map is bijective,
hence it is a ring isomorphism. Apply this to the existing commutative structure sheaf,
whose scheme sections are the actual rings of regular functions. This is exactly the
extension of the structure sheaf furnished by the commutative-ring equivalence. -/
theorem enlargedAtlas_ring_equalizer (X : AlgebraicSpace S) :
    (∀ (R : Sheaf X.etaleTopology CommRingCat.{v})
      (E : Sheaf X.enlargedEtaleTopology CommRingCat.{v})
      (e : (enlargedRestriction X CommRingCat.{v}).obj E ≅ R)
      (T : X.EnlargedEtaleSite) (U V : X.EtaleSite)
      (a : (enlargedSchemeInclusion X).obj U ⟶ T),
      IsEtale a.hom.left.hom.hom ∧ IsSurjective a.hom.left.hom.hom →
      ∀ p q : V ⟶ U,
        IsPullback ((enlargedSchemeInclusion X).map p)
          ((enlargedSchemeInclusion X).map q) a a →
        ∃ b : E.obj.obj (op T) ≃+*
            (RingHom.eqLocus (R.obj.map p.op).hom (R.obj.map q.op).hom),
          ∀ x : E.obj.obj (op T),
            (b x).val = e.hom.hom.app (op U) (E.obj.map a.op x)) ∧
    Nonempty ((enlargedRestriction X CommRingCat.{u}).obj X.enlargedCotangentStructure ≅
      X.commStructureSheaf) := by
  refine ⟨?_, ⟨enlargedCotangentRestriction X⟩⟩
  intro R E e T U V a ha p q hpq
  let lift := forget CommRingCat.{v} ⋙ uliftFunctor.{u + 1, v}
  let Fset := (sheafCompose X.etaleTopology lift).obj R
  let Eset := (sheafCompose X.enlargedEtaleTopology lift).obj E
  let eset : (enlargedRestriction X _).obj Eset ≅ Fset :=
    (sheafCompose X.etaleTopology lift).mapIso e
  obtain ⟨b, hb⟩ := normalizedChart_equalizer X Fset Eset eset T U V a ha p q hpq
  let r : E.obj.obj (op T) →+* R.obj.obj (op U) :=
    (e.hom.hom.app (op U)).hom.comp (E.obj.map a.op).hom
  have hb' (x : E.obj.obj (op T)) : (b (ULift.up x)).val.down = r x :=
    congrArg ULift.down (hb (ULift.up x))
  have hr (x : E.obj.obj (op T)) :
      r x ∈ RingHom.eqLocus (R.obj.map p.op).hom (R.obj.map q.op).hom := by
    have h := congrArg ULift.down (b (ULift.up x)).property
    change R.obj.map p.op ((b (ULift.up x)).val.down) =
      R.obj.map q.op ((b (ULift.up x)).val.down) at h
    change (R.obj.map p.op).hom (r x) = (R.obj.map q.op).hom (r x)
    simpa only [hb'] using h
  let f := r.codRestrict
    (RingHom.eqLocus (R.obj.map p.op).hom (R.obj.map q.op).hom) hr
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hh : r x = r y := congrArg Subtype.val hxy
      have he : b (ULift.up x) = b (ULift.up y) := by
        apply Subtype.ext
        apply ULift.ext
        exact (hb' x).trans (hh.trans (hb' y).symm)
      exact congrArg ULift.down (b.injective he)
    · intro y
      let z : {s : Fset.obj.obj (op U) //
          Fset.obj.map p.op s = Fset.obj.map q.op s} :=
        ⟨ULift.up y.val, congrArg ULift.up y.property⟩
      refine ⟨(b.symm z).down, ?_⟩
      apply Subtype.ext
      change r (b.symm z).down = y.val
      rw [← hb']
      have hh : ULift.up (b.symm z).down = b.symm z := ULift.up_down _
      rw [hh, b.apply_symm_apply]
  exact ⟨RingEquiv.ofBijective f hf, fun _ ↦ rfl⟩

end AlgebraicGeometry.AlgebraicSpace
