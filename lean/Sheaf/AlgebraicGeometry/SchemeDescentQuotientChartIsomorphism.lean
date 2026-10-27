/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Sheaf.AlgebraicGeometry.SchemeCoproductKernelPairComponents
import Sheaf.AlgebraicGeometry.SchemeDescentChartSectionLifting
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Recovering the charts of a scheme descent quotient

Source: Stacks Project, Spaces, Tags 0262, 02WV and 02WW; Descent, Tag 023Q
(blueprint: lem-trf-scheme-descent-quotient-chart-isomorphism).

Products in `Over S` are fibre products over `S`. Overlap schemes and coproducts are
specified by their universal properties, retaining all their structure maps. The transition
claim is stated on arbitrary test schemes with the same switched overlap coordinates.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private theorem section_eq_iff {S : Scheme.{u}} {T X Y : Over S}
    {G : (Over S)ᵒᵖ ⥤ Type u} (a : yoneda.obj X ⟶ G) (b : yoneda.obj Y ⟶ G)
    (x : T ⟶ X) (y : T ⟶ Y) :
    a.app (op T) x = b.app (op T) y ↔ yoneda.map x ≫ a = yoneda.map y ≫ b := by
  constructor
  · intro h
    apply (yonedaEquiv (X := T) (F := G)).injective
    change a.app (op T) (𝟙 T ≫ x) = b.app (op T) (𝟙 T ≫ y)
    simpa using h
  · intro h
    have he := congrArg (fun z ↦ z.app (op T) (𝟙 T)) h
    simpa using he

private theorem chart_test_pullback {S : Scheme.{u}} {X U T : Over S}
    {G : (Over S)ᵒᵖ ⥤ Type u} (q : yoneda.obj X ⟶ G) (f : X ⟶ U)
    (h : IsIso (Limits.prod.lift q (yoneda.map f))) (a : yoneda.obj T ⟶ G) :
    ∃ x : T ⨯ U ⟶ X,
      IsPullback (yoneda.map x) (yoneda.map Limits.prod.fst) q a := by
  let A := Limits.prod.lift q (yoneda.map f)
  have : IsIso A := h
  let e := prodComparison yoneda T U
  let d := Limits.prod.map a (𝟙 (yoneda.obj U))
  let r := e ≫ d ≫ inv A
  let x : T ⨯ U ⟶ X := yoneda.preimage r
  have hx : yoneda.map x = r := yoneda.map_preimage r
  refine ⟨x, ?_⟩
  apply (IsPullback.of_prod_fst_with_id a (yoneda.obj U)).flip.of_iso
    (asIso e).symm (asIso A).symm (Iso.refl _) (Iso.refl _)
  · simp [hx, r, d]
  · change Limits.prod.fst ≫ 𝟙 _ = inv e ≫ yoneda.map Limits.prod.fst
    rw [← prodComparison_fst]
    simp [e]
  · change Limits.prod.fst ≫ 𝟙 _ = inv A ≫ q
    rw [← Limits.prod.lift_fst q (yoneda.map f)]
    simp [A]
  · simp

-- The presentation kernel pair makes the retained cocycle hypothesis redundant.
set_option linter.unusedVariables false in
/-- Each original chart is the pullback of the quotient to its base chart, with the given
transition, kernel pair and jointly surjective étale atlas.
Source: Stacks Project, Spaces, Tags 0262, 02WV and 02WW; Descent, Tag 023Q
(blueprint: lem-trf-scheme-descent-quotient-chart-isomorphism).

Proof:
1. Restrict the assumed presentation kernel pair to the two coproduct components `i,j`.
   Disjointness and openness of scheme coproduct components
   (lem-weil-pbc-scheme-coproduct-family and def-weil-open-immersion) force its lift to
   factor uniquely through `R i j`. This gives the displayed individual pullback square,
   including for the empty test scheme.
2. Two sections of `X i` with the same quotient section and the same `U i` coordinate
   give a section of `R i i` above the diagonal. The normalization makes their two
   projections equal. Thus the map `(q_i,f_i)` is injective on all test schemes.
3. By lem-a1-representable-etale-fppf-local-lifting, a section of `F` lifts étale locally
   to `V`. Pulling back its coproduct cover produces local lifts to `X j`. Combine each
   with the specified `U i` coordinate to get a section of `R j i`, and transport by
   `theta j i` to `X i`. Base compatibility preserves the required base coordinate and
   the presentation equation preserves the quotient section. The open inclusions and
   their composites are étale by lem-weil-pbc-etale-composition-cancellation, hence this
   is an fppf cover by def-weil-etale-morphism and def-pc-fppf-site.
4. Step 2 makes these lifts agree on all overlaps. The cover is fpqc by
   lem-trf-fppf-covering-is-fpqc. Representable descent
   (lem-weil-pbc-fpqc-representable-descent) glues a unique scheme map to `X i`.
   Descent uniqueness gives its base coordinate, and the sheaf equalizer condition
   (def-weil-pbc-sites-and-cohomology) gives its quotient section. The unique inverse
   commutes with restriction, proving the asserted natural map is an isomorphism.
5. On an overlap the two chart identifications have the same quotient section and
   switched base coordinates. Step 2 identifies their transition with `theta i j`;
   equivalently, the testwise equivalence below holds. Step 1 supplies its kernel pair.
6. For any scheme test into `F`, represent its pullback with `V` by a scheme `P`.
   The inverse images `P i` of the open coproduct components cover `P` and represent
   the pullbacks with `X i`. Their maps to the test scheme are étale by composition,
   and their images jointly cover it because `P` maps surjectively. This proves precisely
   the final scheme-test covering assertion; no individual chart is required surjective. -/
theorem scheme_descent_quotient_chart_isomorphism
    {S : Scheme.{u}} {I : Type v} (U X : I → Over S) (f : ∀ i, X i ⟶ U i)
    (hU : ∀ i, Etale (U i).hom)
    (hcover : ∀ x : S, ∃ (i : I) (y : (U i).left), (U i).hom.base y = x)
    (R : I → I → Over S) (p : ∀ i j, R i j ⟶ X i)
    (b : ∀ i j, R i j ⟶ U i ⨯ U j)
    (hR : ∀ i j, IsPullback (p i j) (b i j) (f i) Limits.prod.fst)
    (theta : ∀ i j, R i j ≅ R j i)
    (hleft : ∀ i j, (theta i j).hom ≫ b j i ≫ Limits.prod.fst =
      b i j ≫ Limits.prod.snd)
    (hright : ∀ i j, (theta i j).hom ≫ b j i ≫ Limits.prod.snd =
      b i j ≫ Limits.prod.fst)
    (hnormal : ∀ (i : I) (T : Over S) (r : T ⟶ R i i),
      r ≫ b i i ≫ Limits.prod.fst = r ≫ b i i ≫ Limits.prod.snd →
      r ≫ (theta i i).hom = r)
    (hcocycle : ∀ (i j k : I) (T : Over S)
      (a : T ⟶ R i j) (a' : T ⟶ R j k) (c : T ⟶ R i k) (d : T ⟶ R k i),
      a ≫ (theta i j).hom ≫ p j i = a' ≫ p j k →
      c ≫ p i k = a ≫ p i j →
      c ≫ b i k ≫ Limits.prod.snd = a' ≫ b j k ≫ Limits.prod.snd →
      d ≫ p k i = a' ≫ (theta j k).hom ≫ p k j →
      d ≫ b k i ≫ Limits.prod.snd = a ≫ b i j ≫ Limits.prod.fst →
      c ≫ (theta i k).hom = d)
    (V W : Over S) (ι : ∀ i, X i ⟶ V) (κ : ∀ ij : I × I, R ij.1 ij.2 ⟶ W)
    (hV : IsColimit (Cofan.mk V ι)) (hW : IsColimit (Cofan.mk W κ))
    (s t : W ⟶ V)
    (hs : ∀ i j, κ (i, j) ≫ s = p i j ≫ ι i)
    (ht : ∀ i j, κ (i, j) ≫ t = (theta i j).hom ≫ p j i ≫ ι j)
    (F : AlgebraicSpace S) (q : yoneda.obj V ⟶ F.obj.obj)
    (hqet : IsEtale q) (hqsurj : IsSurjective q)
    (hq : yoneda.map s ≫ q = yoneda.map t ≫ q)
    (hkernel : IsPullback (yoneda.map s) (yoneda.map t) q q) :
    (∀ i, IsIso (Limits.prod.lift (yoneda.map (ι i) ≫ q) (yoneda.map (f i)))) ∧
    (∀ (i j : I) (T : Over S) (r : T ⟶ R i j) (r' : T ⟶ R j i),
      r ≫ b i j ≫ Limits.prod.fst = r' ≫ b j i ≫ Limits.prod.snd →
      r ≫ b i j ≫ Limits.prod.snd = r' ≫ b j i ≫ Limits.prod.fst →
      (r ≫ (theta i j).hom = r' ↔
        (yoneda.map (ι i) ≫ q).app (op T) (r ≫ p i j) =
          (yoneda.map (ι j) ≫ q).app (op T) (r' ≫ p j i))) ∧
    (∀ i j, IsPullback (yoneda.map (p i j)) (yoneda.map ((theta i j).hom ≫ p j i))
      (yoneda.map (ι i) ≫ q) (yoneda.map (ι j) ≫ q)) ∧
    (∀ i, IsEtale (yoneda.map (ι i) ≫ q)) ∧
    (∀ (T : Over S) (a : yoneda.obj T ⟶ F.obj.obj),
      ∃ (P : I → Over S) (v : ∀ i, P i ⟶ T) (x : ∀ i, P i ⟶ X i),
        (∀ i, IsPullback (yoneda.map (x i)) (yoneda.map (v i))
          (yoneda.map (ι i) ≫ q) a) ∧
        (∀ i, Etale (v i).left) ∧
        ∀ z : T.left, ∃ (i : I) (y : (P i).left), (v i).left.base y = z) := by
  have hk := scheme_coproduct_kernel_pair_components X R p
    (fun i j ↦ (theta i j).hom ≫ p j i) V W ι κ hV hW s t hs ht q hkernel
  have hrel (i j : I) : yoneda.map (p i j ≫ ι i) ≫ q =
      yoneda.map ((theta i j).hom ≫ p j i ≫ ι j) ≫ q := by
    rw [← hs, ← ht, Functor.map_comp, Functor.map_comp, Category.assoc,
      Category.assoc, hq]
  have hinj (i : I) (T : Over S) (x y : T ⟶ X i)
      (hxy : (yoneda.map (ι i) ≫ q).app (op T) x =
        (yoneda.map (ι i) ≫ q).app (op T) y)
      (hf : x ≫ f i = y ≫ f i) : x = y := by
    obtain ⟨r, hr, hr'⟩ := Types.exists_of_isPullback ((hk i i).app (op T)) x y hxy
    change r ≫ p i i = x at hr
    change r ≫ (theta i i).hom ≫ p i i = y at hr'
    have hb : r ≫ b i i ≫ Limits.prod.fst = r ≫ b i i ≫ Limits.prod.snd := by
      calc
        r ≫ b i i ≫ Limits.prod.fst = x ≫ f i := by
          rw [← hr, Category.assoc, (hR i i).w]
        _ = y ≫ f i := hf
        _ = r ≫ (theta i i).hom ≫ b i i ≫ Limits.prod.fst := by
          rw [← hr', Category.assoc, Category.assoc, (hR i i).w]
        _ = r ≫ b i i ≫ Limits.prod.snd := by rw [hleft]
    have he := hnormal i T r hb
    calc
      x = r ≫ p i i := hr.symm
      _ = r ≫ (theta i i).hom ≫ p i i := by rw [← Category.assoc, he]
      _ = y := hr'
  have hsurj := scheme_descent_chart_section_lifting U X f R p b hR theta hleft
    V ι hV F.obj q hqet hqsurj hrel hinj
  have hiso (i : I) :
      IsIso (Limits.prod.lift (yoneda.map (ι i) ≫ q) (yoneda.map (f i))) := by
    let A := Limits.prod.lift (yoneda.map (ι i) ≫ q) (yoneda.map (f i))
    suffices ∀ T, IsIso (A.app T) from NatIso.isIso_of_isIso_app A
    intro ⟨T⟩
    apply (isIso_iff_bijective _).2
    constructor
    · intro x y hxy
      apply hinj i T x y
      · have he := congrArg ((Limits.prod.fst :
            F.obj.obj ⨯ yoneda.obj (U i) ⟶ F.obj.obj).app (op T)) hxy
        change ((A ≫ Limits.prod.fst).app (op T)) x =
          ((A ≫ Limits.prod.fst).app (op T)) y at he
        simpa only [A, Limits.prod.lift_fst] using he
      · have he := congrArg ((Limits.prod.snd :
            F.obj.obj ⨯ yoneda.obj (U i) ⟶ yoneda.obj (U i)).app (op T)) hxy
        change ((A ≫ Limits.prod.snd).app (op T)) x =
          ((A ≫ Limits.prod.snd).app (op T)) y at he
        simpa [A] using he
    · intro y
      obtain ⟨x, hx, hf⟩ := hsurj i T
        ((Limits.prod.fst : F.obj.obj ⨯ yoneda.obj (U i) ⟶ F.obj.obj).app (op T) y)
        ((Limits.prod.snd : F.obj.obj ⨯ yoneda.obj (U i) ⟶ yoneda.obj (U i)).app (op T) y)
      refine ⟨x, ?_⟩
      apply yonedaEquiv.symm.injective
      apply Limits.prod.hom_ext
      · apply yonedaEquiv.injective
        simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
        change ((A ≫ Limits.prod.fst).app (op T)) x = _
        simpa only [A, Limits.prod.lift_fst] using hx
      · apply yonedaEquiv.injective
        simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
        change ((A ≫ Limits.prod.snd).app (op T)) x = _
        simpa [A] using hf
  have htrans (i j : I) (T : Over S) (r : T ⟶ R i j) (r' : T ⟶ R j i)
      (hl : r ≫ b i j ≫ Limits.prod.fst = r' ≫ b j i ≫ Limits.prod.snd)
      (hr : r ≫ b i j ≫ Limits.prod.snd = r' ≫ b j i ≫ Limits.prod.fst) :
      r ≫ (theta i j).hom = r' ↔
        (yoneda.map (ι i) ≫ q).app (op T) (r ≫ p i j) =
          (yoneda.map (ι j) ≫ q).app (op T) (r' ≫ p j i) := by
    have he : (yoneda.map (ι i) ≫ q).app (op T) (r ≫ p i j) =
        (yoneda.map (ι j) ≫ q).app (op T) (r ≫ (theta i j).hom ≫ p j i) := by
      apply (section_eq_iff _ _ _ _).2
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ yoneda.map r ≫ z) (hrel i j)
    constructor
    · intro h
      simpa only [← Category.assoc, h] using he
    · intro h
      apply (hR j i).hom_ext
      · apply hinj j T
        · exact he.symm.trans h
        · calc
            (r ≫ (theta i j).hom ≫ p j i) ≫ f j =
                r ≫ (theta i j).hom ≫ b j i ≫ Limits.prod.fst := by
              simp only [Category.assoc, (hR j i).w]
            _ = r ≫ b i j ≫ Limits.prod.snd := by rw [hleft]
            _ = r' ≫ b j i ≫ Limits.prod.fst := hr
            _ = (r' ≫ p j i) ≫ f j := by rw [Category.assoc, (hR j i).w]
      · apply Limits.prod.hom_ext
        · simpa only [Category.assoc, hleft] using hr
        · simpa only [Category.assoc, hright] using hl
  have htest (i : I) (T : Over S) (a : yoneda.obj T ⟶ F.obj.obj) :=
    chart_test_pullback (yoneda.map (ι i) ≫ q) (f i) (hiso i) a
  have het (i : I) (T : Over S) :
      Etale (Limits.prod.fst : T ⨯ U i ⟶ T).left := by
    exact MorphismProperty.of_isPullback
      (Over.isPullback_of_binaryFan_isLimit _ (Limits.prodIsProd T (U i))).flip (hU i)
  refine ⟨hiso, htrans, hk, ?_, ?_⟩
  · intro i T a
    obtain ⟨x, hx⟩ := htest i T a
    exact ⟨T ⨯ U i, Limits.prod.fst, yoneda.map x, hx, het i T⟩
  · intro T a
    choose x hx using fun i ↦ htest i T a
    refine ⟨fun i ↦ T ⨯ U i, fun _ ↦ Limits.prod.fst, x, hx, fun i ↦ het i T, ?_⟩
    intro z
    obtain ⟨i, y, hy⟩ := hcover (T.hom.base z)
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
      (Over.isPullback_of_binaryFan_isLimit _ (Limits.prodIsProd T (U i))) z y hy.symm
    exact ⟨i, w, hw⟩

end AlgebraicGeometry.AlgebraicSpace
