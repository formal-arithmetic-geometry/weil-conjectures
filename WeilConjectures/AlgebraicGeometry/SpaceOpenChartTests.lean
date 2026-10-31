/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Open scheme tests and composites with étale charts

Source: Stacks Project, Spaces, Tag 02WK and the discussion following
`definition-immersion`; Schemes, Tag 01L7; Morphisms, Tags 02GP and 02GN
(blueprint: lem-a1-space-open-chart-tests).

The scheme-test hypothesis uses the existing `IsRepresentableWith` interface.
The pullback comparison is characterized by its inverse's two projections, so it is
canonical. The scheme representing its right side has the stated étale projection,
and its map to the original test scheme is the composite of the two scheme maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Open scheme tests imply section injectivity and sheaf monomorphy, and every
representable étale scheme chart remains representable étale after composition.
The final clause applies to every representing square for the open scheme test.
The equations for `e.inv` characterize the canonical comparison uniquely; `d`
represents its right side, and `d.hom ≫ e.inv` represents its left side.

Source: Stacks Project, Spaces, Tag 02WK and discussion following
`definition-immersion`; Schemes, Tag 01L7; Morphisms, Tags 02GP and 02GN
(blueprint: lem-a1-space-open-chart-tests).

Proof:
1. Given two sections over `H` with common image `c`, Yoneda turns them into maps
   from `h_H`. The representing square for the open scheme test turns them into
   sections of its projection `p : U → H`. Open immersions are monomorphisms by
   lem-weil-pbc-open-immersion-monomorphism, so these sections agree. Evaluating
   their maps to `O` at the identity of `H` proves section injectivity.
2. For maps from any sheaf to `O` whose composites with `j` agree, apply step 1 to
   each section on each scheme. Equality of components gives equality of sheaf maps.
3. The open scheme projections are étale by lem-weil-pbc-open-immersion-etale.
   Any other representing square is uniquely isomorphic to the chosen square, so
   its projection is also étale.
4. Fix a representable étale chart `v : h_V → O` and a test `c : h_H → Y`.
   Let `U` represent the open test, with projections `p : U → H` and `r : h_U → O`.
   Apply the scheme-test definition in def-trf-algebraic-space to `v` and `r`.
   It gives a scheme `W` representing `h_V ×_O h_U` with étale map `q : W → U`.
   The canonical comparison sends `(x,t)` to `(x,(t,v(x)))`; its inverse forgets
   the `O` component. Both formulas commute with restriction, and their projections
   characterize them uniquely. Compatible pairs glue componentwise, so these
   presheaf pullbacks are the sheaf pullbacks of
   lem-trf-space-fibre-products-etale-covers.
5. The scheme projection to `H` is `q ≫ p`. It is étale by step 3 and clause (2)
   of lem-weil-pbc-etale-composition-cancellation. Thus `W` represents every test
   of the composite with étale projection, proving its representable étaleness. -/
theorem space_open_chart_tests {S : Scheme.{u}} (O Y : AlgebraicSpace S)
    (j : O ⟶ Y)
    (hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom) :
    (∀ H : Over S, Function.Injective (j.hom.hom.app (op H))) ∧
    Mono j.hom ∧
    (∀ (H U : Over S) (c : yoneda.obj H ⟶ Y.obj.obj) (p : U ⟶ H)
      (r : yoneda.obj U ⟶ O.obj.obj),
      IsPullback r (yoneda.map p) j.hom.hom c → Etale p.left) ∧
    ∀ (V : Over S) (v : yoneda.obj V ⟶ O.obj.obj), IsEtale v →
      IsEtale (v ≫ j.hom.hom) ∧
      ∀ (H U : Over S) (c : yoneda.obj H ⟶ Y.obj.obj) (p : U ⟶ H)
        (r : yoneda.obj U ⟶ O.obj.obj),
        IsPullback r (yoneda.map p) j.hom.hom c →
        ∃ e : Limits.pullback (v ≫ j.hom.hom) c ≅ Limits.pullback v r,
          e.inv ≫ Limits.pullback.fst (v ≫ j.hom.hom) c = Limits.pullback.fst v r ∧
          e.inv ≫ Limits.pullback.snd (v ≫ j.hom.hom) c =
            Limits.pullback.snd v r ≫ yoneda.map p ∧
          ∃ (W : Over S) (q : W ⟶ U) (d : yoneda.obj W ≅ Limits.pullback v r),
            d.hom ≫ Limits.pullback.snd v r = yoneda.map q ∧
            Etale q.left ∧ Etale (q ≫ p).left ∧
            (d.hom ≫ e.inv) ≫ Limits.pullback.snd (v ≫ j.hom.hom) c =
              yoneda.map (q ≫ p) := by
  have hinj : ∀ H : Over S, Function.Injective (j.hom.hom.app (op H)) := by
    intro H x y hxy
    obtain ⟨U, p, r, hp, hopen⟩ := hj H (yonedaEquiv.symm (j.hom.hom.app (op H) x))
    have : IsOpenImmersion p.left := hopen
    have : Mono p := Over.mono_of_mono_left p
    have hx : j.hom.hom.app (op H) x =
        (yonedaEquiv.symm (j.hom.hom.app (op H) x)).app (op H) (𝟙 H) := by simp
    obtain ⟨a, ha, hpa⟩ := Types.exists_of_isPullback (hp.app (op H)) x (𝟙 H) hx
    obtain ⟨b, hb, hpb⟩ := Types.exists_of_isPullback (hp.app (op H)) y (𝟙 H)
      (hxy.symm.trans hx)
    have hab : a = b := (cancel_mono p).1 (hpa.trans hpb.symm)
    exact ha.symm.trans (hab ▸ hb)
  have hmono : Mono j.hom.hom := (NatTrans.mono_iff_mono_app _).2
    (fun H ↦ (CategoryTheory.mono_iff_injective _).2 (hinj H.unop))
  have hjE : IsEtale j.hom.hom := by
    intro H c
    obtain ⟨U, p, r, hp, hopen⟩ := hj H c
    have : IsOpenImmersion p.left := hopen
    exact ⟨U, p, r, hp, inferInstance⟩
  have hrel : (MorphismProperty.inverseImage @Etale (Over.forget S)).relative yoneda
      j.hom.hom := by
    apply MorphismProperty.relative.of_exists
    intro H c
    obtain ⟨U, p, r, hp, he⟩ := hjE H c
    exact ⟨U, r, p, hp, he⟩
  have htest : ∀ (H U : Over S) (c : yoneda.obj H ⟶ Y.obj.obj) (p : U ⟶ H)
      (r : yoneda.obj U ⟶ O.obj.obj),
      IsPullback r (yoneda.map p) j.hom.hom c → Etale p.left := by
    intro H U c p r hp
    exact hrel.property c r p hp
  refine ⟨hinj, ?_, htest, ?_⟩
  · exact (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).mono_of_mono_map hmono
  · intro V v hv
    refine ⟨isEtale_comp v j.hom.hom hv hjE, ?_⟩
    intro H U c p r hp
    have hcomp := (IsPullback.of_hasPullback v r).paste_vert hp
    let e := hcomp.isoPullback.symm
    have he₁ : e.inv ≫ Limits.pullback.fst (v ≫ j.hom.hom) c =
        Limits.pullback.fst v r := hcomp.isoPullback_hom_fst
    have he₂ : e.inv ≫ Limits.pullback.snd (v ≫ j.hom.hom) c =
        Limits.pullback.snd v r ≫ yoneda.map p := hcomp.isoPullback_hom_snd
    obtain ⟨W, q, s, hs, hq⟩ := hv U r
    have : Etale q.left := hq
    have : Etale p.left := htest H U c p r hp
    have hqp : Etale (q ≫ p).left := inferInstanceAs (Etale (q.left ≫ p.left))
    refine ⟨e, he₁, he₂, W, q, hs.isoPullback, hs.isoPullback_hom_snd, hq, hqp, ?_⟩
    rw [Category.assoc, he₂, ← Category.assoc, hs.isoPullback_hom_snd, ← Functor.map_comp]

end AlgebraicGeometry.AlgebraicSpace
