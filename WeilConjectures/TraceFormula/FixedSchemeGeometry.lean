/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Limits

/-! # The geometric fixed-scheme equalizer

This graph and its fixed scheme depend only on the scheme endomorphism.
The constructions and equalizer proof are reused with distinct helper names from TraceFixedScheme,
whose original declarations remain intact for general cohomological correspondences.
Source: latest blueprint, fixed scheme of a geometric graph
(blueprint: lem-trf-geometric-fixed-scheme-equalizer).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The geometric graph `(id_X,h)` of an endomorphism over the base. Its coefficient
map is neither needed nor requested. Source: blueprint def-trf-fixed-scheme, graph sentence
(blueprint: lem-trf-geometric-fixed-scheme-equalizer). -/
def geometricFixedGraphMap {F : FiniteFieldDatum.{u}} (X : Over (Spec (.of F.k)))
    (h : X ⟶ X) : X.left ⟶ pullback X.hom X.hom :=
  pullback.lift (𝟙 X.left) h.left ((Category.id_comp X.hom).trans h.w.symm)

/-- The fixed scheme of an endomorphism over `s`, using just its geometric graph.
The over-category condition is precisely `h ≫ a_X = a_X`.
Source: blueprint def-trf-fixed-scheme, second display
(blueprint: lem-trf-geometric-fixed-scheme-equalizer). -/
def geometricEndomorphismFixedScheme {F : FiniteFieldDatum.{u}}
    (X : Over (Spec (.of F.k))) (h : X ⟶ X) : Scheme.{u} :=
  pullback (geometricFixedGraphMap X h) (pullback.diagonal X.hom)

/-- The first projection of the fixed scheme of a geometric graph.
Source: blueprint def-trf-fixed-scheme, equalizer sentence
(blueprint: lem-trf-geometric-fixed-scheme-equalizer). -/
def geometricEndomorphismFixedInclusion {F : FiniteFieldDatum.{u}}
    (X : Over (Spec (.of F.k))) (h : X ⟶ X) : geometricEndomorphismFixedScheme X h ⟶ X.left :=
  pullback.fst (geometricFixedGraphMap X h) (pullback.diagonal X.hom)

/-- The first projection represents the scheme-theoretic equalizer of `h` and the identity:
composition with it is a bijection from morphisms `T → Fix(h)` onto morphisms `t : T → X`
with `t ≫ h = t`. The first conjunct says every such composite is fixed; the second says
a morphism `t` has exactly one lift if and only if it is fixed.
Source: blueprint def-trf-fixed-scheme, equalizer sentence
(blueprint: lem-trf-geometric-fixed-scheme-equalizer).

Proof: a map into the pullback is a pair `(t,d)` with `(t,h t) = (d,d)` in the
fibre product `X ×_s X`. Projecting with the two projections of `X ×_s X`, by
`pullback.lift_fst`, `pullback.lift_snd`, `pullback.diagonal_fst` and
`pullback.diagonal_snd`, gives `t=d` and `t ≫ h=t`; this proves the first conjunct
and the forward implication. Conversely, from the latter equality use `(t,t)` and the
two fibre-product universal properties to construct the map. Any such map has both
projections `t`, so pullback uniqueness proves uniqueness. This applies to every test
scheme, including empty ones. -/
theorem geometricEndomorphismFixedScheme_equalizer {F : FiniteFieldDatum.{u}}
    (X : Over (Spec (.of F.k))) (h : X ⟶ X) (T : Scheme.{u}) (t : T ⟶ X.left) :
    (∀ g : T ⟶ geometricEndomorphismFixedScheme X h,
        (g ≫ geometricEndomorphismFixedInclusion X h) ≫ h.left =
          g ≫ geometricEndomorphismFixedInclusion X h) ∧
      ((∃! g : T ⟶ geometricEndomorphismFixedScheme X h,
        g ≫ geometricEndomorphismFixedInclusion X h = t) ↔ t ≫ h.left = t) := by
  have hproj (g : T ⟶ geometricEndomorphismFixedScheme X h) :
      g ≫ geometricEndomorphismFixedInclusion X h =
        g ≫ pullback.snd (geometricFixedGraphMap X h) (pullback.diagonal X.hom) := by
    have hc := congrArg (fun f ↦ g ≫ f ≫ pullback.fst X.hom X.hom)
      (pullback.condition (f := geometricFixedGraphMap X h) (g := pullback.diagonal X.hom))
    simpa [geometricEndomorphismFixedInclusion, geometricFixedGraphMap, Category.assoc] using hc
  have hfixed (g : T ⟶ geometricEndomorphismFixedScheme X h) :
      (g ≫ geometricEndomorphismFixedInclusion X h) ≫ h.left =
        g ≫ geometricEndomorphismFixedInclusion X h := by
    have hc := congrArg (fun f ↦ g ≫ f ≫ pullback.snd X.hom X.hom)
      (pullback.condition (f := geometricFixedGraphMap X h) (g := pullback.diagonal X.hom))
    simp only [Category.assoc, geometricFixedGraphMap, pullback.lift_snd,
      pullback.diagonal_snd, Category.comp_id] at hc
    simpa only [geometricEndomorphismFixedInclusion, geometricFixedGraphMap, Category.assoc] using
      hc.trans (hproj g).symm
  refine ⟨hfixed, ?_⟩
  constructor
  · rintro ⟨g, hg, _⟩
    simpa [hg] using hfixed g
  · intro ht
    have hc : t ≫ geometricFixedGraphMap X h = t ≫ pullback.diagonal X.hom := by
      apply pullback.hom_ext
      · simp [geometricFixedGraphMap, Category.assoc]
      · simpa [geometricFixedGraphMap, Category.assoc] using ht
    refine ⟨pullback.lift t t hc, ?_, ?_⟩
    · exact pullback.lift_fst _ _ _
    · intro g hg
      apply pullback.hom_ext
      · simpa [geometricEndomorphismFixedInclusion] using hg
      · simpa using (hproj g).symm.trans hg


end WeilConjectures
