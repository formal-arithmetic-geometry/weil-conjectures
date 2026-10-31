/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import WeilConjectures.AlgebraicGeometry.EtaleDescentThroughSourceCover
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-!
# Detection of etaleness through a representable source cover

Source: Stacks Project, Properties of Spaces, Tags 03EC(3) and 03FS(1)-(2);
Descent, Tag 036W (blueprint: lem-trf-space-etale-source-atlas-detection).

Chartwise etaleness is written as its scheme-chart condition. This is exactly
`IsChartwiseEtale` in the enlarged-site module, without importing the downstream site.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

-- Scheme-test properties do not depend on the chosen representing pullback square.
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

-- A represented pullback transports scheme-test properties without choosing a sheaf pullback.
private theorem scheme_tests_base_change {S : Scheme.{u}}
    (P : MorphismProperty (Over S))
    {G F H K : (Over S)ᵒᵖ ⥤ Type u}
    {b : K ⟶ G} {d : K ⟶ H} {f : G ⟶ F} {a : H ⟶ F}
    (h : IsPullback b d f a) (hf : IsRepresentableWith P f) :
    IsRepresentableWith P d := by
  intro T t
  obtain ⟨U, r, c, hc, hr⟩ := hf T (t ≫ a)
  exact ⟨U, r, h.lift c (yoneda.map r ≫ t) (by simpa [Category.assoc] using hc.w),
    hc.of_right' h, hr⟩

/-- Scheme-source descent, descent through an arbitrary representable surjective etale
source cover, the criterion at every scheme atlas, and existence of such an atlas.
There are no separation, quasi-compactness, or Noetherian hypotheses.
Source: Stacks Project, Properties of Spaces, Tags 03EC(3), 03FS(1)-(2), and the
source-pullback argument proving 03FS(4) implies (1); Spaces, Tag 025Y for atlas existence;
Descent, Tag 036W (blueprint: lem-trf-space-etale-source-atlas-detection).

Proof:
1. By lem-trf-space-representable-etale-scheme-tests, every scheme-source map to an
   algebraic space is representable. For a test scheme T mapping to Y, represent
   T x_Y W and T x_Y V by schemes A and B. Pullback pasting identifies B -> A with
   the base change of V -> W. It is surjective etale by def-trf-algebraic-space.
   The map B -> T is etale by the hypothesis on the composite. Apply
   lem-trf-etale-descent-through-source-cover to B -> A -> T. Since T is arbitrary,
   q is representable etale.
2. Given a scheme chart a : h_W -> X, pull the cover R -> X back to h_W.
   By lem-trf-space-fibre-products-etale-covers and representability of the cover,
   it is h_V -> h_W for a surjective etale scheme map d : V -> W. Its other
   projection b : h_V -> R is the base change of a, hence representable etale by
   lem-trf-space-representable-etale-scheme-tests. That node also gives etaleness
   of b followed by p followed by f. The pullback equality identifies this with
   h_d followed by a followed by f. Apply step 1 to deduce etaleness of a followed
   by f. This proves the chartwise condition without assuming R is a scheme.
3. At every scheme atlas, chartwise etaleness gives etaleness of the composite by
   its definition. Conversely apply step 2 with the scheme atlas as the cover.
   The existence of a representable surjective etale atlas is the atlas clause
   of def-trf-algebraic-space. Empty schemes and spaces need no separate hypothesis. -/
theorem etale_source_atlas_detection {S : Scheme.{u}} :
    (∀ (Y : AlgebraicSpace S) (W V : Over S)
      (q : yoneda.obj W ⟶ Y.obj.obj) (p : V ⟶ W),
      Etale p.left → Surjective p.left → IsEtale (yoneda.map p ≫ q) → IsEtale q) ∧
    (∀ (X Y R : AlgebraicSpace S) (f : X ⟶ Y) (p : R ⟶ X),
      IsEtale p.hom.hom → IsSurjective p.hom.hom →
      IsEtale (p.hom.hom ≫ f.hom.hom) →
      ∀ (W : Over S) (a : yoneda.obj W ⟶ X.obj.obj),
        IsEtale a → IsEtale (a ≫ f.hom.hom)) ∧
    (∀ (X Y : AlgebraicSpace S) (f : X ⟶ Y) (U : Over S)
      (p : yoneda.obj U ⟶ X.obj.obj), IsEtale p → IsSurjective p →
      ((∀ (W : Over S) (a : yoneda.obj W ⟶ X.obj.obj),
        IsEtale a → IsEtale (a ≫ f.hom.hom)) ↔ IsEtale (p ≫ f.hom.hom))) ∧
    (∀ X : AlgebraicSpace S, ∃ (U : Over S) (p : yoneda.obj U ⟶ X.obj.obj),
      IsEtale p ∧ IsSurjective p) := by
  have hscheme : ∀ (Y : AlgebraicSpace S) (W V : Over S)
      (q : yoneda.obj W ⟶ Y.obj.obj) (p : V ⟶ W),
      Etale p.left → Surjective p.left → IsEtale (yoneda.map p ≫ q) → IsEtale q := by
    intro Y W V q p hp hs hcomp T t
    obtain ⟨A, r, a, ha, _⟩ := (representable_etale_scheme_tests.1 Y W q) T t
    have hpe := (representable_etale_scheme_tests.2.2.2.2.2.2.2.2.1 V W p hp hs).1
    have hps := (representable_etale_scheme_tests.2.2.2.2.2.2.2.2.1 V W p hp hs).2
    obtain ⟨B, d, b, hb, hd⟩ := hpe A a
    have hds : Surjective d.left := property_of_scheme_test
      (fun _ _ f ↦ Surjective f) hps hb
    have hde : Etale (d.left ≫ r.left) := property_of_scheme_test
      (fun _ _ f ↦ Etale f) hcomp (p := d ≫ r) (q := b) (a := t) (by
        simpa only [Functor.map_comp] using hb.paste_vert ha)
    exact ⟨A, r, a, ha,
      @Etale.of_comp_of_surjective_etale _ _ _ r.left d.left hds hd hde⟩
  have hcover : ∀ (G H : (Over S)ᵒᵖ ⥤ Type u) (Y : AlgebraicSpace S)
      (f : G ⟶ Y.obj.obj) (p : H ⟶ G),
      IsEtale p → IsSurjective p → IsEtale (p ≫ f) →
      ∀ (W : Over S) (a : yoneda.obj W ⟶ G), IsEtale a → IsEtale (a ≫ f) := by
    intro G H Y f p hp hs hcomp W a ha
    obtain ⟨V, d, b, hb, hd⟩ := hp W a
    have hds : Surjective d.left := property_of_scheme_test
      (fun _ _ f ↦ Surjective f) hs hb
    have hbe : IsEtale b := scheme_tests_base_change _ hb.flip ha
    apply hscheme Y W V (a ≫ f) d hd hds
    have he := isEtale_comp b (p ≫ f) hbe hcomp
    simpa only [← Category.assoc, hb.w] using he
  refine ⟨hscheme, ?_, ?_, ?_⟩
  · intro X Y R f p hp hs hcomp
    exact hcover X.obj.obj R.obj.obj Y f.hom.hom p.hom.hom hp hs hcomp
  · intro X Y f U p hp hs
    exact ⟨fun h ↦ h U p hp, fun h ↦
      hcover X.obj.obj (yoneda.obj U) Y f.hom.hom p hp hs h⟩
  · intro X
    exact X.property.2

end AlgebraicGeometry.AlgebraicSpace
