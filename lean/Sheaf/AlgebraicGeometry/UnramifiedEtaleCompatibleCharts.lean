/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Sheaf.AlgebraicGeometry.SchemeUnramifiedEtaleLocality
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Limits.Yoneda

/-! # Compatible étale charts for unramified and étale space morphisms

Source: Stacks Project, Morphisms of Spaces, Tags 03MJ, 03ZH and 03XT(7)--(8);
Spaces, Tag 02X1; Descent, Tag 04R3(7),(9)
(blueprint: lem-sfb-unramified-etale-compatible-charts).

The chartwise property is the existing universal `MapIsLocally` test. A compatible
presentation need not have a surjective target chart for the recognition equivalence.
The second clause constructs a source atlas over any prescribed target atlas.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

-- A scheme-test property is independent of its representing pullback square.
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

private theorem scheme_map_property {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {U V : Over S} (r : U ⟶ V) (hr : P r.left) :
    IsRepresentableWith (P.inverseImage (Over.forget S)) (yoneda.map r) := by
  intro T a
  let b : T ⟶ V := yoneda.preimage a
  refine ⟨Limits.pullback r b, Limits.pullback.snd r b,
    yoneda.map (Limits.pullback.fst r b), ?_, ?_⟩
  · have hb : yoneda.map b = a := yoneda.map_preimage a
    rw [← hb]
    exact (IsPullback.of_hasPullback r b).map yoneda
  · exact MorphismProperty.of_isPullback (P := P)
      ((IsPullback.of_hasPullback r b).map (Over.forget S)) hr

private theorem surjective_comp {S : Scheme.{u}}
    {G H K : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ H) (g : H ⟶ K)
    (hf : IsSurjective f) (hg : IsSurjective g) : IsSurjective (f ≫ g) := by
  intro T a
  obtain ⟨V, p, q, hq, hp⟩ := hg T a
  obtain ⟨W, r, s, hs, hr⟩ := hf V q
  refine ⟨W, r ≫ p, s, ?_, ?_⟩
  · simpa only [Functor.map_comp] using hs.paste_vert hq
  · have := hp
    have := hr
    change Surjective (r.left ≫ p.left)
    infer_instance

/-- Unramifiedness and étaleness in all compatible scheme charts can each be checked
in any one compatible diagram with surjective source chart. Every prescribed target
atlas admits a compatible source atlas.

Source: Stacks Project, Morphisms of Spaces, Tags 03MJ, 03ZH, 03XT(7)--(8);
Spaces, Tag 02X1; Descent, Tag 04R3(7),(9)
(blueprint: lem-sfb-unramified-etale-compatible-charts).

Proof, following the node:
1. For unramifiedness, lem-sfb-scheme-unramified-etale-locality gives the three
   source-and-target locality conditions. For étaleness use
   lem-sfb-scheme-etale-source-target-properties. Both scheme properties respect
   isomorphisms, directly from def-weil-unramified-morphism and def-weil-etale-morphism.
   Apply lem-sfb-space-etale-presentation-property-criterion to each property.
   Its universal condition is MapIsLocally, and its existential condition is one
   presentation with surjective source chart. In a fixed such presentation D, P(D.h)
   witnesses the existential condition; conversely the universal condition applies to D.
   This proves the first clause without surjectivity of D.b.
2. Given the prescribed b:V → Y, choose a surjective étale scheme atlas c:W → X
   from def-trf-algebraic-space. Apply the scheme test of b to c followed by f.
   It gives a scheme U representing W ×_Y V and an étale projection p:U → W.
   Surjectivity of b gives another representing square with surjective projection;
   the unique isomorphism between the squares transports surjectivity to p.
   Yoneda full faithfulness turns the other projection into h:U → V. Set a = c p.
   The representing square gives fa = bh. The scheme map p induces a representable
   surjective étale presheaf map: its tests are scheme pullbacks, which preserve
   étaleness and surjectivity. Compose with c, using isEtale_comp and the analogous
   surjectivity proof by successive scheme tests and pullback pasting. The scheme
   projections compose by lem-weil-pbc-etale-composition-cancellation and
   lem-trf-surjective-morphism-composition.
3. No point is selected in these constructions, and the two scheme locality statements
   include empty schemes. Thus the same proof includes empty spaces and schemes.
   No separation, finiteness, quasi-compactness or Noetherian assumption is used. -/
theorem unramified_etale_compatible_charts {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (∀ P : MorphismProperty Scheme.{u}, P = @IsUnramified ∨ P = @Etale →
      ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
        (b : yoneda.obj V ⟶ Y.obj.obj) (h : U ⟶ V),
        IsEtale a → IsEtale b → a ≫ f.hom.hom = yoneda.map h ≫ b →
          IsSurjective a → (MapIsLocally P f ↔ P h.left)) ∧
    (∀ (V : Over S) (b : yoneda.obj V ⟶ Y.obj.obj),
      IsEtale b → IsSurjective b →
        ∃ (U : Over S) (a : yoneda.obj U ⟶ X.obj.obj) (h : U ⟶ V),
          IsEtale a ∧ IsSurjective a ∧ a ≫ f.hom.hom = yoneda.map h ≫ b) := by
  have hunramified : IsEtaleLocalOnSourceAndTarget (@IsUnramified) := by
    refine ⟨scheme_unramified_etale_locality.1,
      scheme_unramified_etale_locality.2.1, ?_⟩
    intro A B g
    refine (scheme_unramified_etale_locality.2.2 A B g).trans ?_
    constructor <;> intro h x
    · obtain ⟨U, V, a, b, u, k, hk⟩ := h x
      exact ⟨U, V, a, b, k, u, hk⟩
    · obtain ⟨U, V, a, b, k, u, hk⟩ := h x
      exact ⟨U, V, a, b, u, k, hk⟩
  have hunramifiedIso : MorphismProperty.RespectsIso (@IsUnramified) := by
    change MorphismProperty.RespectsIso
      ((@LocallyOfFiniteType) ⊓ MorphismProperty.diagonal (@IsOpenImmersion))
    infer_instance
  constructor
  · intro P hP U V a b h ha hb hw hs
    have hlocal : IsEtaleLocalOnSourceAndTarget P := by
      rcases hP with rfl | rfl
      · exact hunramified
      · exact
          (scheme_etale_source_target_properties.{u, u} (@Etale) (Or.inr (Or.inl rfl))).1
    have hIso : P.RespectsIso := by
      rcases hP with rfl | rfl
      · exact hunramifiedIso
      · infer_instance
    constructor
    · intro hf
      exact hf U V a b h ha hb hw
    · intro hh
      apply (etalePresentation_property_criterion P hlocal f).2.mpr
      exact ⟨⟨U, V, a, b, h, ha, hb, hw⟩, hs, hh⟩
  · intro V b hb hbs
    obtain ⟨W, c, hc, hcs⟩ := X.property.2
    obtain ⟨U, p, q, hpq, hp⟩ := hb W (c ≫ f.hom.hom)
    have hps : Surjective p.left :=
      property_of_scheme_test (@Surjective) hbs hpq
    let h : U ⟶ V := yoneda.preimage q
    have hh : yoneda.map h = q := yoneda.map_preimage q
    refine ⟨U, yoneda.map p ≫ c, h, ?_, ?_, ?_⟩
    · exact isEtale_comp _ _ (scheme_map_property (@Etale) p hp) hc
    · exact surjective_comp _ _ (scheme_map_property (@Surjective) p hps) hcs
    · rw [hh, Category.assoc]
      exact hpq.w.symm

end AlgebraicGeometry.AlgebraicSpace
