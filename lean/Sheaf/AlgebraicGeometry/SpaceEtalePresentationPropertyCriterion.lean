module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Étale presentation criterion for properties of algebraic-space morphisms

Source: Stacks Project, Spaces, Tag 02X1; Morphisms of Spaces, Tag 03MJ;
Descent, Tags 04QZ, 04R0 and 04R1
(blueprint: lem-sfb-space-etale-presentation-property-criterion).

The locality predicate and presentation structure package the data explicitly introduced
in the node. The extended property is defined by existence of a surjective source chart.
The target chart is never required to be surjective.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The three clauses of étale locality on source-and-target: precomposition, étale
base change, and pointwise local detection in étale commutative squares.
Source: Stacks, Descent, Tag 04QZ
(blueprint: lem-sfb-space-etale-presentation-property-criterion). -/
def IsEtaleLocalOnSourceAndTarget (P : MorphismProperty Scheme.{u}) : Prop :=
  (∀ (X Y Z : Scheme.{u}) (a : X ⟶ Y) (f : Y ⟶ Z),
    Etale a → P f → P (a ≫ f)) ∧
  (∀ (X Y V : Scheme.{u}) (f : X ⟶ Y) (b : V ⟶ Y),
    P f → Etale b → P (Limits.pullback.snd f b)) ∧
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    P f ↔ ∀ x : X, ∃ (U V : Scheme.{u}) (a : U ⟶ X) (b : V ⟶ Y)
      (h : U ⟶ V) (u : U),
      Etale a ∧ Etale b ∧ a.base u = x ∧ a ≫ f = h ≫ b ∧ P h

namespace AlgebraicSpace

/-- An étale presentation diagram has two scheme charts and a commuting horizontal map.
`IsEtale` includes representability by the dependency's scheme-test definition.
Surjectivity is separate, and is imposed only on the source chart when needed.
Source: Stacks, Morphisms of Spaces, Tag 03MJ
(blueprint: lem-sfb-space-etale-presentation-property-criterion). -/
structure EtalePresentation {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) where
  U : Over S
  V : Over S
  a : yoneda.obj U ⟶ F
  b : yoneda.obj V ⟶ G
  h : U ⟶ V
  source_etale : IsEtale a
  target_etale : IsEtale b
  comm : a ≫ f = yoneda.map h ≫ b

/-- The property extended to space maps: a presentation with surjective source chart
whose scheme map has `P`. This is real propositional data, with no chosen atlas.
Source: Stacks, Morphisms of Spaces, Tag 03MJ and the following definition
(blueprint: lem-sfb-space-etale-presentation-property-criterion). -/
def HasEtalePresentationProperty {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Prop :=
  ∃ D : EtalePresentation f, IsSurjective D.a ∧ P D.h.left

-- Any representing square has the same scheme property as the chosen scheme test.
private theorem property_of_scheme_test {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F G : (Over S)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsRepresentableWith (P.inverseImage (Over.forget S)) f)
    {U T : Over S} {p : U ⟶ T} {q : yoneda.obj U ⟶ F}
    {a : yoneda.obj T ⟶ G} (sq : IsPullback q (yoneda.map p) f a) :
    P p.left := by
  obtain ⟨V, r, t, ht, hr⟩ := hf T a
  let e : U ≅ V := yoneda.preimageIso (sq.isoIsPullback _ _ ht)
  have he : e.hom ≫ r = p := by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, e, Functor.preimageIso_hom, Functor.map_preimage]
      using sq.isoIsPullback_hom_snd _ _ ht
  rw [← he]
  exact (P.cancel_left_of_respectsIso e.hom.left r.left).2 hr

private theorem yoneda_property {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {U V : Over S} (r : U ⟶ V) (hr : P r.left) :
    IsRepresentableWith (P.inverseImage (Over.forget S)) (yoneda.map r) := by
  intro T a
  let b : T ⟶ V := yoneda.preimage a
  refine ⟨Limits.pullback r b, Limits.pullback.snd r b,
    yoneda.map (Limits.pullback.fst r b), ?_, ?_⟩
  · simpa only [b, Functor.map_preimage] using
      (IsPullback.of_hasPullback r b).map yoneda
  · exact MorphismProperty.of_isPullback (P := P)
      ((IsPullback.of_hasPullback r b).map (Over.forget S)) hr

private theorem property_of_yoneda {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {U V : Over S} (r : U ⟶ V)
    (hr : IsRepresentableWith (P.inverseImage (Over.forget S)) (yoneda.map r)) :
    P r.left :=
  property_of_scheme_test P hr (IsPullback.of_id_fst)

private theorem surjective_comp {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsSurjective f) (hg : IsSurjective g) : IsSurjective (f ≫ g) := by
  intro T a
  obtain ⟨V, p, q, hq, hp⟩ := hg T a
  obtain ⟨U, r, t, ht, hr⟩ := hf V q
  have : Surjective p.left := hp
  have : Surjective r.left := hr
  refine ⟨U, r ≫ p, t, ?_, (show Surjective (r.left ≫ p.left) by infer_instance)⟩
  simpa only [Functor.map_comp] using ht.paste_vert hq

-- Permanence in a possibly non-cartesian étale square, by its graph in the pullback.
private theorem property_of_etale_square
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y U V : Scheme.{u}} (f : X ⟶ Y) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V)
    (ha : Etale a) (hb : Etale b) (comm : a ≫ f = h ≫ b) (hf : P f) : P h := by
  let d := Limits.pullback.lift a h comm
  have : Etale b := hb
  have ht : Etale (Limits.pullback.fst f b) := inferInstance
  have hd : Etale d := MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale)
    d (Limits.pullback.fst f b) ht (by simpa only [d, Limits.pullback.lift_fst] using ha)
  have hp := hP.2.1 X Y V f b hf hb
  simpa only [d, Limits.pullback.lift_snd] using
    hP.1 _ _ _ d (Limits.pullback.snd f b) hd hp

private theorem exists_surjective_presentation {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃ D : EtalePresentation f.hom.hom, IsSurjective D.a := by
  obtain ⟨W, c, hc, hsc⟩ := X.property.2
  obtain ⟨V, b, hb, hsb⟩ := Y.property.2
  obtain ⟨U, p, q, hq, hp⟩ := hb W (c ≫ f.hom.hom)
  have hsp : Surjective p.left := property_of_scheme_test _ hsb hq
  refine ⟨⟨U, V, yoneda.map p ≫ c, b, yoneda.preimage q,
    isEtale_comp _ _ (yoneda_property _ p hp) hc, hb, ?_⟩,
    surjective_comp _ _ (yoneda_property _ p hsp) hsc⟩
  simpa only [Functor.map_preimage, Category.assoc] using hq.w.symm

-- Compare two presentations on the fibre products of their source and target charts.
private theorem presentation_property_of_surjective {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    {F G : (Over S)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (D D' : EtalePresentation f) (hs : IsSurjective D.a) (hh : P D.h.left) :
    P D'.h.left := by
  obtain ⟨A, q, p₀, sq₀, hq⟩ := D.source_etale D'.U D'.a
  let p : A ⟶ D.U := yoneda.preimage p₀
  have sq : IsPullback (yoneda.map p) (yoneda.map q) D.a D'.a := by
    simpa only [p, Functor.map_preimage] using sq₀
  have hp : Etale p.left := property_of_scheme_test _ D'.source_etale sq.flip
  have hsq : Surjective q.left := property_of_scheme_test _ hs sq
  obtain ⟨B, t, r₀, st₀, ht⟩ := D.target_etale D'.V D'.b
  let r : B ⟶ D.V := yoneda.preimage r₀
  have st : IsPullback (yoneda.map r) (yoneda.map t) D.b D'.b := by
    simpa only [r, Functor.map_preimage] using st₀
  have hr : Etale r.left := property_of_scheme_test _ D'.target_etale st.flip
  have comm : yoneda.map (p ≫ D.h) ≫ D.b = yoneda.map (q ≫ D'.h) ≫ D'.b := by
    simp only [Functor.map_comp, Category.assoc, ← D.comm, ← D'.comm]
    simpa only [Category.assoc] using congrArg (fun m ↦ m ≫ f) sq.w
  let k : A ⟶ B := yoneda.preimage
    (st.lift (yoneda.map (p ≫ D.h)) (yoneda.map (q ≫ D'.h)) comm)
  have hkr : k ≫ r = p ≫ D.h := by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, k, Functor.map_preimage] using
      st.lift_fst (yoneda.map (p ≫ D.h)) (yoneda.map (q ≫ D'.h)) comm
  have hkt : k ≫ t = q ≫ D'.h := by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, k, Functor.map_preimage] using
      st.lift_snd (yoneda.map (p ≫ D.h)) (yoneda.map (q ≫ D'.h)) comm
  have hk : P k.left := property_of_etale_square P hP D.h.left p.left r.left k.left
    hp hr (congrArg (fun m ↦ m.left) hkr.symm) hh
  apply (hP.2.2 _ _ D'.h.left).2
  intro x
  have : Surjective q.left := hsq
  obtain ⟨z, hz⟩ := q.left.surjective x
  exact ⟨A.left, B.left, q.left, t.left, k.left, z, hq, ht, hz,
    congrArg (fun m ↦ m.left) hkt.symm, hk⟩

/-- Every space morphism has an étale scheme presentation with surjective source, and
an étale-local property holds on every presentation iff it holds on one such presentation.
No surjectivity of the target chart occurs in either condition.

Source: Stacks, Spaces, Tag 02X1; Morphisms of Spaces, Tag 03MJ
(blueprint: lem-sfb-space-etale-presentation-property-criterion).

Proof: (1) Choose surjective étale atlases W → X and V → Y. The scheme test of
V → Y on W → Y gives U = W ×_Y V and a surjective étale U → W. Compose to get
U → X. On any scheme T → X the test is (T ×_X W) ×_W U, as follows by inserting
or forgetting the forced W component on sections. Base change and composition of
singleton étale coverings give the required representable surjective étale source map
[def-trf-algebraic-space, lem-galois-yoneda-fully-faithful, def-pc-fibre-product,
lem-weil-pbc-etale-covering-base-change, lem-weil-pbc-etale-covering-composition].
(2) Compare a good presentation U → V with an arbitrary U' → V'. The scheme tests give
D = U ×_X U' and T = V ×_Y V', with étale projections and surjective D → U'.
Their universal properties give k : D → T; Yoneda identifies the representing schemes
[def-trf-algebraic-space, lem-galois-yoneda-fully-faithful].
(3) Put E = U ×_V T. The map E → T has P by étale base change. Both D → U and
E → U are étale; cancellation makes the induced D → E étale. Precomposition gives P(k)
[def-pc-fibre-product, lem-weil-pbc-etale-scheme-base-change,
lem-weil-pbc-etale-composition-cancellation].
(4) Every point of U' lifts to D. The square k over h' gives exactly the witnesses in
locality clause (iii), so P(h'). Conversely apply the universal condition to the
surjective presentation from (1). The argument never needs surjectivity of V → Y. -/
theorem etalePresentation_property_criterion {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (∃ D : EtalePresentation f.hom.hom, IsSurjective D.a) ∧
      (MapIsLocally P f ↔ HasEtalePresentationProperty P f.hom.hom) := by
  obtain ⟨D, hs⟩ := exists_surjective_presentation f
  refine ⟨⟨D, hs⟩, ?_⟩
  constructor
  · intro h
    exact ⟨D, hs, h D.U D.V D.a D.b D.h D.source_etale D.target_etale D.comm⟩
  · rintro ⟨D₀, hs₀, hh₀⟩ U V a b h ha hb comm
    exact presentation_property_of_surjective P hP D₀ ⟨U, V, a, b, h, ha, hb, comm⟩
      hs₀ hh₀

/-- On schemes, both presentation conditions agree with the original scheme property.
The scheme morphism is viewed as its Yoneda natural transformation over the base.

Source: Stacks, Morphisms of Spaces, Tag 03MJ; Descent, Tags 04QZ, 04R0 and 04R1
(blueprint: lem-sfb-space-etale-presentation-property-criterion).

Proof: (5) If P(f), precomposing by a gives P(fa). Base change by b gives P(r) on
Z = V ×_Y U → V. The graph section s : U → Z is étale: Z → U is étale and
s is its section, so use étale cancellation with the identity. Thus P(h) = P(rs)
by precomposition [def-pc-fibre-product, def-weil-etale-morphism,
lem-weil-pbc-etale-scheme-base-change, lem-weil-pbc-etale-composition-cancellation].
Representable étale scheme maps are étale by testing on the identity scheme map.
(6) A good presentation with surjective a provides the pointwise witnesses of locality
(iii), giving P(f), even for an empty source. Conversely identity charts give a good
presentation when P(f). The universal condition implies P(f) on those same identity
charts. Hence both equivalences, with no target surjectivity assumption. -/
theorem etalePresentation_property_iff_scheme {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hP : IsEtaleLocalOnSourceAndTarget P) {X Y : Over S} (f : X ⟶ Y) :
    ((∀ D : EtalePresentation (yoneda.map f), P D.h.left) ↔ P f.left) ∧
      (HasEtalePresentationProperty P (yoneda.map f) ↔ P f.left) := by
  let I : EtalePresentation (yoneda.map f) :=
    ⟨X, Y, yoneda.map (𝟙 X), yoneda.map (𝟙 Y), f,
      yoneda_property _ (𝟙 X) (show Etale (𝟙 X.left) by infer_instance),
      yoneda_property _ (𝟙 Y) (show Etale (𝟙 Y.left) by infer_instance), by simp⟩
  have hI : IsSurjective I.a :=
    yoneda_property _ (𝟙 X) (show Surjective (𝟙 X.left) by infer_instance)
  have all_of (hf : P f.left) (D : EtalePresentation (yoneda.map f)) : P D.h.left := by
    let a : D.U ⟶ X := yoneda.preimage D.a
    let b : D.V ⟶ Y := yoneda.preimage D.b
    have ha : Etale a.left := property_of_yoneda _ a (by
      change IsEtale (yoneda.map a)
      simpa only [a, Functor.map_preimage] using D.source_etale)
    have hb : Etale b.left := property_of_yoneda _ b (by
      change IsEtale (yoneda.map b)
      simpa only [b, Functor.map_preimage] using D.target_etale)
    have comm : a ≫ f = D.h ≫ b := by
      apply yoneda.map_injective
      simpa only [Functor.map_comp, a, b, Functor.map_preimage] using D.comm
    exact property_of_etale_square P hP f.left a.left b.left D.h.left ha hb
      (congrArg (fun m ↦ m.left) comm) hf
  refine ⟨⟨fun h ↦ h I, all_of⟩, ?_⟩
  constructor
  · rintro ⟨D, hs, hh⟩
    exact presentation_property_of_surjective P hP D I hs hh
  · intro hf
    exact ⟨I, hI, hf⟩

end AlgebraicSpace

end AlgebraicGeometry
