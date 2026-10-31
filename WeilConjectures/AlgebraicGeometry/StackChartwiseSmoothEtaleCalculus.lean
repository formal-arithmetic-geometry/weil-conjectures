/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AlgebraicModuliStack
public import WeilConjectures.AlgebraicGeometry.DmStackMorphismProperties
public import WeilConjectures.AlgebraicGeometry.OpenModuliSubstack
public import WeilConjectures.AlgebraicGeometry.ModuliChartNormalization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.StackCompositeChartRefinement
import WeilConjectures.AlgebraicGeometry.SchemeEtaleSourceTargetProperties

/-! # Chartwise smooth and étale calculus for representable stack morphisms

Source: Stacks, stacks-properties.tex, Section 04XB, Tags 04XC, 04ZT, 04ZU and 04XI;
algebraic.tex, Tags 045B, 045C and 045G
(blueprint: lem-sfb-stack-chartwise-smooth-etale-calculus).

The existing algebraic-stack, full-open-substack and algebraic-space-test definitions
are used throughout. Field-extension lifting and inverse-image open covering below
spell out the two conventions explicitly introduced in this node.

## Main definitions

- `IsSurjectiveModuliMap`: field-extension local lifting, with its actual 2-isomorphism.
- `IsOpenModuliCover`: covering on every scheme inverse image.

## Main statements

- `stack_chartwise_smooth_etale_calculus`, `stack_chartwise_comp`,
  `stack_chartwise_openCover`: the five properties under base change, composition and locality.
- `stack_chartwise_implications`: the four implications between the properties.
- `surjective_moduli_baseChange`, `surjective_moduli_comp`,
  `surjective_moduli_iff_chartwise`: surjectivity and the scheme-chart comparison.
- `etale_moduli_scheme_coproduct`: descent of the disjoint-source maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃ v₄ w₄ z

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- Surjectivity means lifting every field-valued object after a field extension.
The displayed 2-isomorphism compares the actual composite with the restriction of the
original object. A unital map between fields is automatically injective.
Source: Stacks, stacks-properties.tex, Tag 04XI
(blueprint: lem-sfb-stack-chartwise-smooth-etale-calculus). -/
def IsSurjectiveModuliMap {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ S)
      (y : BasedFunctor (discreteModuli (yoneda.obj (Over.mk b))) G),
    ∃ (L : Type u) (_ : Field L) (i : K →+* L)
      (x : BasedFunctor
        (discreteModuli (yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom i) ≫ b)))) F),
      Nonempty (ModuliTwoIso (x.comp f)
        ((discreteModuliMap (yoneda.map
          (Over.homMk (Spec.map (CommRingCat.ofHom i))))).comp y))

/-- An open family covers when its open inverse images cover every scheme test.
Each witness retains the representing equivalence and the actual projection to the
scheme, so this is covering by the inverse images of these particular full substacks.
Source: Stacks, stacks-properties.tex, Tag 04YM; descent.tex, Tag 04R1(f)
(blueprint: lem-sfb-stack-chartwise-smooth-etale-calculus). -/
def IsOpenModuliCover {S : Scheme.{u}} {F : BasedCategory.{v₁, w₁} (Over S)}
    {I : Type z} (U : I → OpenModuliSubstack F) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F) (x : T.left),
    ∃ (i : I) (W : Over S) (j : W ⟶ T), IsOpenImmersion j.left ∧
      ∃ e : BasedFunctor (discreteModuli (yoneda.obj W))
          (moduliTwoFiberProduct t (fullModuliInclusion F (U i).property)),
        IsSchemeModuliBaseChange e j ∧ ∃ w : W.left, j.left w = x

/-- Insert the repeated factor and its identity comparison in a scheme test. -/
private def baseChangeInsert
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)} {W : BasedCategory.{v₄, w₄} (Over S)}
    (f : BasedFunctor F G) (g : BasedFunctor H G) (t : BasedFunctor W H) :
    BasedFunctor (moduliTwoFiberProduct (t.comp g) f)
      (moduliTwoFiberProduct t (moduliTwoFiberFst g f)) where
  obj x :=
    ⟨⟨x.obj.left,
      ⟨⟨t.obj x.obj.left, x.obj.right, x.obj.hom⟩,
        ⟨x.property.1, (t.w_obj x.obj.left).symm ▸ x.property.2⟩⟩,
      𝟙 (t.obj x.obj.left)⟩, ⟨inferInstance, inferInstance⟩⟩
  map a := ObjectProperty.homMk
    { left := a.hom.left
      right := ObjectProperty.homMk
        { left := t.map a.hom.left
          right := a.hom.right
          w := a.hom.w }
      w := by
        change t.map a.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ t.map a.hom.left
        simp only [Category.comp_id, Category.id_comp] }
  map_id x := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · rfl
    · apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · exact t.map_id _
      · rfl
  map_comp a b := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · rfl
    · apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · exact t.map_comp _ _
      · rfl
  w := rfl

private theorem baseChangeInsert_isEquivalence
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)} {W : BasedCategory.{v₄, w₄} (Over S)}
    (f : BasedFunctor F G) (g : BasedFunctor H G) (t : BasedFunctor W H) :
    (baseChangeInsert f g t).toFunctor.IsEquivalence := by
  let e := baseChangeInsert f g t
  have hff : e.toFunctor.FullyFaithful :=
    { preimage := fun a ↦ ObjectProperty.homMk
        { left := a.hom.left
          right := a.hom.right.hom.right
          w := by
            have h := a.hom.w
            change t.map a.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ a.hom.right.hom.left at h
            simp only [Category.comp_id, Category.id_comp] at h
            change g.map (t.map a.hom.left) ≫ _ = _
            rw [h]
            exact a.hom.right.hom.w }
      map_preimage := fun a ↦ by
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext
        · rfl
        · apply ObjectProperty.hom_ext
          apply Comma.hom_ext
          · have h := a.hom.w
            change t.map a.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ a.hom.right.hom.left at h
            change t.map a.hom.left = a.hom.right.hom.left
            simpa only [Category.comp_id, Category.id_comp] using h
          · rfl
      preimage_map := fun a ↦ rfl }
  have := hff.full
  have := hff.faithful
  have : e.toFunctor.EssSurj := by
    constructor
    intro y
    have : IsIso y.obj.hom := y.property.1
    have : G.p.IsHomLift (𝟙 (W.p.obj y.obj.left)) (g.map y.obj.hom) := by
      have := y.property.2
      infer_instance
    have := y.obj.right.property.1
    have := y.obj.right.property.2
    let x : (moduliTwoFiberProduct (t.comp g) f).obj :=
      ⟨⟨y.obj.left, y.obj.right.obj.right, g.map y.obj.hom ≫ y.obj.right.obj.hom⟩,
        ⟨inferInstance, IsHomLift.comp_lift_id_right' G.p
          (𝟙 (W.p.obj y.obj.left)) (g.map y.obj.hom)
          (H.p.obj y.obj.right.obj.left) y.obj.right.obj.hom⟩⟩
    refine ⟨x, ⟨ObjectProperty.isoMk _ (Comma.isoMk (Iso.refl _) ?_ ?_)⟩⟩
    · exact ObjectProperty.isoMk _ (Comma.isoMk (asIso y.obj.hom) (Iso.refl _)
        (by simp [e, baseChangeInsert, x]))
    · change t.map (𝟙 y.obj.left) ≫ y.obj.hom = 𝟙 _ ≫ y.obj.hom
      simp only [t.map_id, Category.id_comp]
  exact {}

private theorem hasSpaceBaseChange_baseChange
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)}
    (f : BasedFunctor F G) (g : BasedFunctor H G) (T : Over S)
    (t : BasedFunctor (discreteModuli (yoneda.obj T)) H)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T)
    (h : HasSpaceBaseChange f T (t.comp g) Z p) :
    HasSpaceBaseChange (moduliTwoFiberFst g f) T t Z p := by
  obtain ⟨e, he, hp⟩ := h
  have := baseChangeInsert_isEquivalence f g t
  refine ⟨e.comp (baseChangeInsert f g t), ?_, hp⟩
  exact Functor.isEquivalence_trans e.toFunctor (baseChangeInsert f g t).toFunctor

/-- Arbitrary base change preserves each of the five properties and representability.
Source: Stacks, algebraic.tex, Tag 045C; stacks-properties.tex, Section 04XB.
(blueprint: lem-sfb-stack-chartwise-smooth-etale-calculus).

Proof: For a scheme test `t : T → H`, insert the repeated H factor and its identity
comparison to obtain a functor from `T ×_G F` to `T ×_H (H ×_G F)`. This functor
is fully faithful: the outer comma square forces the middle component of an arrow
to be the image of its T component. It is essentially surjective: for an object
`(a, (h, x, β), α)`, compose `g(α)` with β and use α to compare with the inserted
object. Its projection to T is unchanged on objects and arrows. Compose the original
space-test equivalence with this functor. The same space, projection and chart
property therefore witness the base-changed test, for any scheme property P.
Forgetting the chart-property clause gives representability. -/
theorem stack_chartwise_smooth_etale_calculus
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)}
    (P : MorphismProperty Scheme.{u})
    (hP : P = @Smooth ∨ P = @Etale ∨ P = @Flat ∨
      P = @LocallyOfFinitePresentation ∨ P = @LocallyOfFiniteType)
    (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G)
    (hH : IsAlgebraicModuliStack H) (f : BasedFunctor F G) (g : BasedFunctor H G)
    (hf : IsRepresentableByAlgebraicSpaces f) (hPf : ModuliSpaceTest P f) :
    IsRepresentableByAlgebraicSpaces (moduliTwoFiberFst g f) ∧
      ModuliSpaceTest P (moduliTwoFiberFst g f) := by
  have _ := hP
  have _ := hF
  have _ := hG
  have _ := hH
  have _ := hf
  have hp : ModuliSpaceTest P (moduliTwoFiberFst g f) := by
    intro T t
    obtain ⟨Z, p, hZ, hp⟩ := hPf T (t.comp g)
    exact ⟨Z, p, hasSpaceBaseChange_baseChange f g T t Z p hZ, hp⟩
  refine ⟨?_, hp⟩
  intro T t
  obtain ⟨Z, p, hZ, _⟩ := hp T t
  exact ⟨Z, p, hZ⟩

/-- Composition preserves each of the five properties and representability.
Source: Section 04XB (section-properties-morphisms), including Tag 04XC
(lemma-property-spaces-too).
(blueprint: lem-sfb-stack-chartwise-smooth-etale-calculus).

Proof:
1. Fix $P$ from the five properties. On schemes its composition laws are respectively
[lem-trf-smooth-composition], [lem-weil-pbc-etale-composition-cancellation](2),
[lem-pc-flat-compose], [lem-sbc-locally-finite-presentation-composition], and
[lem-weil-pbc-proper-fp-permanence](e). The chart operations also use arbitrary scheme
base change for etaleness [lem-weil-pbc-etale-scheme-base-change]. These laws concern
arbitrary schemes; no Noetherian or quasi-compact condition on charts is needed.
Uses: lem-trf-smooth-composition, lem-weil-pbc-etale-composition-cancellation,
lem-pc-flat-compose, lem-sbc-locally-finite-presentation-composition,
lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-etale-scheme-base-change.
2. By [lem-sfb-scheme-etale-source-target-properties], this $P$ is etale local on
source-and-target. Apply [lem-sfb-space-etale-presentation-property-criterion] to interpret it on
algebraic spaces: it holds on every etale scheme presentation exactly when it holds on one
presentation covering the source. We will use both directions, and the scheme comparison, below.
This supplies chart independence; it is not an assumption that a chosen smooth stack atlas is
etale.
Uses: lem-sfb-scheme-etale-source-target-properties,
lem-sfb-space-etale-presentation-property-criterion.
3. Here are the fibre-product identifications and chart operations used below. Fibre products of
algebraic spaces exist by [lem-trf-space-fibre-products-etale-covers]. A map from a scheme $U$ to
a space $F$ is representable: for another scheme $T\to F$, $U\times_F T$ is the pullback of the
representable diagonal of $F$ along $U\times_S T\to F\times_S F$, so is a scheme by
[def-trf-algebraic-space]. For the chart operations we use only representable etale maps
(scheme-valued tests). For such $a:A\to B$ and $b:B\to C$, a scheme test $T\to C$ factors their
composite as the etale scheme maps $A_T\to B_T\to T$; step 1 gives etaleness of the composite. If
the two maps are surjective, these scheme maps are surjective and
[lem-trf-surjective-morphism-composition] applies. Arbitrary base change retains exactly the same
scheme tests; base changes of an etale surjective scheme map are etale by step 1 and surjective by
[lem-weil-pbc-surjective-base-change]. Hence these operations preserve representable etale charts
and their covering property. In all ensuing 2-pullback reassociations the functor keeps the maps
to the factors and composes the displayed isomorphisms between their images; its inverse inserts
the identity isomorphism at the repeated factor. Thus these reassociations are equivalences of the
explicit groupoids of [def-sfb-stable-pointed-moduli-groupoids], compatible with all projections.
Uses: lem-trf-space-fibre-products-etale-covers, def-trf-algebraic-space,
lem-trf-surjective-morphism-composition, lem-weil-pbc-surjective-base-change,
def-sfb-stable-pointed-moduli-groupoids.
5. Let $X\xrightarrow{f}Y\xrightarrow{g}Z$ be maps of spaces with $P$. Choose an etale scheme
atlas $W\to Z$, then one $V\to Y\times_Z W$, then one $U\to X\times_Y V$, all surjective. Step 3
shows that $V\to Y$ and $U\to X$ are surjective etale. The presentation criterion
[lem-sfb-space-etale-presentation-property-criterion] gives $P$ for both scheme maps $U\to V$ and
$V\to W$. Their composite has $P$ by step 1; its square with $X\to Z$ is an etale presentation
covering the source. Applying the criterion in the other direction proves $P(gf)$. The scheme
composition law from step 1 is applied to these two scheme maps; the desired stack composition
statement has not been used.
Uses: def-trf-algebraic-space, lem-sfb-space-etale-presentation-property-criterion.
6. Let $f:\mathcal X\to\mathcal Y$ be representable by spaces and let $B\to\mathcal Y$ be a map
from an algebraic space. The pullback $A=\mathcal X\times_{\mathcal Y}B$ is a space by
[lem-sfb-representable-pullback-over-space]. If all scheme tests of $f$ have $P$, choose an etale
scheme atlas $V\to B$ and then an etale scheme atlas $U\to A\times_B V$. The map $A\times_B
V=\mathcal X\times_{\mathcal Y}V\to V$ has $P$ by hypothesis, so the criterion of step 2 gives
$P(U\to V)$. Step 3 makes $U\to A$ surjective etale. Hence
[lem-sfb-space-etale-presentation-property-criterion] gives $P(A\to B)$. Conversely, testing on
all spaces includes schemes. Thus scheme tests may be replaced by space tests, with the assertion
about representability supplied separately by Tag 0300.
Uses: lem-sfb-representable-pullback-over-space, def-trf-algebraic-space,
lem-sfb-space-etale-presentation-property-criterion.
7. For any $\mathcal Y'\to\mathcal Y$ and scheme $T\to\mathcal Y'$, the scheme test of the base
change of $f$ identifies with $\mathcal X\times_{\mathcal Y}T\to T$. It is a space and has $P$ by
the defining scheme test of $f$; this proves representability and $P$ for arbitrary stack base
change. For composition $\mathcal X\xrightarrow{f}\mathcal Y\xrightarrow{g}\mathcal Z$ and
$T\to\mathcal Z$, put $B=\mathcal Y\times_{\mathcal Z}T$. Representability of $g$ makes $B$ a
space, while [lem-sfb-representable-pullback-over-space] makes $A=\mathcal X\times_{\mathcal Y}B$
a space. This $A$ identifies with $\mathcal X\times_{\mathcal Z}T$ by the tuple reassociation of
step 3. If $f,g$ have $P$, step 6 gives $P(A\to B)$ and the scheme test of $g$ gives $P(B\to T)$.
Apply the space composition calculation of step 5. Every scheme test of $gf$ therefore has $P$,
proving the composition assertion as well as its representability.
Uses: lem-sfb-representable-pullback-over-space, def-sfb-stable-pointed-moduli-groupoids.
-/
theorem stack_chartwise_comp
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)}
    (P : MorphismProperty Scheme.{u})
    (hP : P = @Smooth ∨ P = @Etale ∨ P = @Flat ∨
      P = @LocallyOfFinitePresentation ∨ P = @LocallyOfFiniteType)
    (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G)
    (hH : IsAlgebraicModuliStack H) (f : BasedFunctor F G) (g : BasedFunctor G H)
    (hf : IsRepresentableByAlgebraicSpaces f) (hg : IsRepresentableByAlgebraicSpaces g)
    (hPf : ModuliSpaceTest P f) (hPg : ModuliSpaceTest P g) :
    IsRepresentableByAlgebraicSpaces (f.comp g) ∧ ModuliSpaceTest P (f.comp g) := by
  have _ := hg
  have hlocal := (scheme_etale_source_target_properties.{u, u} P hP).1
  have hcomp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
      (ha : P a) (hb : P b) : P (a ≫ b) := by
    rcases hP with rfl | rfl | rfl | rfl | rfl <;>
      have := ha <;> have := hb <;> infer_instance
  have hp : ModuliSpaceTest P (f.comp g) := by
    intro T t
    obtain ⟨ZB, pB, hB, hpB⟩ := hPg T t
    obtain ⟨ZA, pA, hA, hrefine⟩ := stack_composite_chart_refinement
      hF.1.1 hG.1.1 hH.1.1 f g hf T t ZB pB hB
    refine ⟨ZA, pA, hA, ?_⟩
    intro U a ha
    apply (hlocal.2.2 U.left T.left (yoneda.preimage (a ≫ pA)).left).2
    intro x
    obtain ⟨W, c, hc, tW, hW⟩ := hrefine U a ha x
    obtain ⟨M, q, hM, hpM⟩ := hPf W tW
    obtain ⟨V, r, b, v, hr, hb, hv, heq⟩ := hW M q hM
    refine ⟨V.left, T.left, r.left, 𝟙 _,
      (yoneda.preimage (b ≫ q)).left ≫ (yoneda.preimage (c ≫ pB)).left,
      v, hr, inferInstance, hv, ?_, hcomp _ _ (hpM V b hb) (hpB W c hc)⟩
    simpa only [Category.comp_id, Over.comp_left] using congrArg (fun k ↦ k.left) heq
  refine ⟨?_, hp⟩
  intro T t
  obtain ⟨Z, p, hZ, _⟩ := hp T t
  exact ⟨Z, p, hZ⟩

/-- Each of the five properties is detected on any open cover of the source.
Source: Section 04XB (section-properties-morphisms), including Tag 04XC
(lemma-property-spaces-too).
(blueprint: lem-sfb-stack-chartwise-smooth-etale-calculus).

Proof:
1. Fix $P$ from the five properties. On schemes its composition laws are respectively
[lem-trf-smooth-composition], [lem-weil-pbc-etale-composition-cancellation](2),
[lem-pc-flat-compose], [lem-sbc-locally-finite-presentation-composition], and
[lem-weil-pbc-proper-fp-permanence](e). The chart operations also use arbitrary scheme
base change for etaleness [lem-weil-pbc-etale-scheme-base-change]. These laws concern
arbitrary schemes; no Noetherian or quasi-compact condition on charts is needed.
Uses: lem-trf-smooth-composition, lem-weil-pbc-etale-composition-cancellation,
lem-pc-flat-compose, lem-sbc-locally-finite-presentation-composition,
lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-etale-scheme-base-change.
2. By [lem-sfb-scheme-etale-source-target-properties], this $P$ is etale local on
source-and-target. Apply [lem-sfb-space-etale-presentation-property-criterion] to interpret it on
algebraic spaces: it holds on every etale scheme presentation exactly when it holds on one
presentation covering the source. We will use both directions, and the scheme comparison, below.
This supplies chart independence; it is not an assumption that a chosen smooth stack atlas is
etale.
Uses: lem-sfb-scheme-etale-source-target-properties,
lem-sfb-space-etale-presentation-property-criterion.
3. Here are the fibre-product identifications and chart operations used below. Fibre products of
algebraic spaces exist by [lem-trf-space-fibre-products-etale-covers]. A map from a scheme $U$ to
a space $F$ is representable: for another scheme $T\to F$, $U\times_F T$ is the pullback of the
representable diagonal of $F$ along $U\times_S T\to F\times_S F$, so is a scheme by
[def-trf-algebraic-space]. For the chart operations we use only representable etale maps
(scheme-valued tests). For such $a:A\to B$ and $b:B\to C$, a scheme test $T\to C$ factors their
composite as the etale scheme maps $A_T\to B_T\to T$; step 1 gives etaleness of the composite. If
the two maps are surjective, these scheme maps are surjective and
[lem-trf-surjective-morphism-composition] applies. Arbitrary base change retains exactly the same
scheme tests; base changes of an etale surjective scheme map are etale by step 1 and surjective by
[lem-weil-pbc-surjective-base-change]. Hence these operations preserve representable etale charts
and their covering property. In all ensuing 2-pullback reassociations the functor keeps the maps
to the factors and composes the displayed isomorphisms between their images; its inverse inserts
the identity isomorphism at the repeated factor. Thus these reassociations are equivalences of the
explicit groupoids of [def-sfb-stable-pointed-moduli-groupoids], compatible with all projections.
Uses: lem-trf-space-fibre-products-etale-covers, def-trf-algebraic-space,
lem-trf-surjective-morphism-composition, lem-weil-pbc-surjective-base-change,
def-sfb-stable-pointed-moduli-groupoids.
8. Let $\{\mathcal X_i\subset\mathcal X\}$ be an open cover and keep $f$ representable by spaces.
For a scheme $T\to\mathcal Y$, write $A=\mathcal X\times_{\mathcal Y}T$ and choose an etale scheme
atlas $U\to A$. Its inverse images $U_i$ of the open substacks are open subschemes covering $U$,
by the meaning of open substack and [def-weil-open-immersion]. The maps $U_i\to A_i=\mathcal
X_i\times_{\mathcal Y}T$ are etale charts by step 3. If all $f|_{\mathcal X_i}$ have $P$, their
scheme tests and step 2 give $P(U_i\to T)$. Open immersions are etale by
[lem-weil-pbc-etale-composition-cancellation](1). The source-cover clause of
[lem-sfb-scheme-etale-source-target-properties] gives $P(U\to T)$, and step 2 gives $P(A\to T)$.
Conversely if $f$ has $P$, any chart of $A_i$ composed with $A_i\to A$ is an etale chart (the
latter map pulls back to open subschemes, hence etale by the same scheme lemma). Step 2 gives $P$
on that chart, hence on $A_i\to T$. To justify representability here before using the tests,
$\mathcal X_i\to\mathcal X$ is representable by schemes by the definition of open substack;
[lem-sfb-representable-pullback-over-space] applied over $A$ makes $A_i=\mathcal
X_i\times_{\mathcal X}A$ a space. Thus $P$ is local on an open cover of the source.
Uses: def-trf-algebraic-space, def-weil-open-immersion,
lem-weil-pbc-etale-composition-cancellation, lem-sfb-scheme-etale-source-target-properties,
lem-sfb-representable-pullback-over-space.
-/
theorem stack_chartwise_openCover
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (P : MorphismProperty Scheme.{u})
    (hP : P = @Smooth ∨ P = @Etale ∨ P = @Flat ∨
      P = @LocallyOfFinitePresentation ∨ P = @LocallyOfFiniteType)
    (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G)
    (f : BasedFunctor F G) (hf : IsRepresentableByAlgebraicSpaces f)
    (I : Type z) (U : I → OpenModuliSubstack F) (hcover : IsOpenModuliCover U) :
    ModuliSpaceTest P f ↔
      ∀ i : I, ModuliSpaceTest P ((fullModuliInclusion F (U i).property).comp f) := by
  sorry

private theorem moduliSpaceTest_mono
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {P Q : MorphismProperty Scheme.{u}} {f : BasedFunctor F G}
    (hPQ : ∀ {X Y : Scheme.{u}} (a : X ⟶ Y), P a → Q a)
    (hf : ModuliSpaceTest P f) : ModuliSpaceTest Q f := by
  intro T t
  obtain ⟨Z, p, hZ, hp⟩ := hf T t
  exact ⟨Z, p, hZ, fun U a ha ↦ hPQ _ (hp U a ha)⟩

/-- Étale implies smooth, smooth implies flat and locally finitely presented, and local
finite presentation implies local finite type, with the original scheme definitions.
Source: Stacks, stacks-properties.tex, Section 04XB; Mathlib scheme-property instances.
(blueprint: lem-sfb-stack-chartwise-smooth-etale-calculus).

Proof: Retain the space witness, its projection, and its equivalence with the
2-fibre product for every scheme test. On each étale scheme chart apply the existing
Mathlib instances Etale → Smooth, Smooth → Flat, Smooth → LocallyOfFinitePresentation,
and LocallyOfFinitePresentation → LocallyOfFiniteType. For the two conclusions from
smoothness use the same witnesses separately. No change of charts is required. -/
theorem stack_chartwise_implications
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G)
    (f : BasedFunctor F G) (hf : IsRepresentableByAlgebraicSpaces f) :
    (IsEtaleModuliMap f → ModuliSpaceTest @Smooth f) ∧
      (ModuliSpaceTest @Smooth f →
        ModuliSpaceTest @Flat f ∧ ModuliSpaceTest @LocallyOfFinitePresentation f) ∧
      (ModuliSpaceTest @LocallyOfFinitePresentation f →
        ModuliSpaceTest @LocallyOfFiniteType f) := by
  have _ := hF
  have _ := hG
  have _ := hf
  refine ⟨?_, ?_, ?_⟩
  · intro he T t
    obtain ⟨Z, p, hZ, hp⟩ := he T t
    refine ⟨Z, p, hZ, ?_⟩
    intro U a ha
    have := hp U a ha
    infer_instance
  · intro hs
    constructor
    · exact moduliSpaceTest_mono (fun a ha ↦ by
        have := ha
        infer_instance) hs
    · exact moduliSpaceTest_mono (fun a ha ↦ by
        have := ha
        infer_instance) hs
  · exact moduliSpaceTest_mono (fun a ha ↦ by
      have := ha
      infer_instance)

/-- Surjectivity is stable under arbitrary base change, including nonrepresentable maps.
Source: Section 04XB (section-properties-morphisms), including Tag 04XC
(lemma-property-spaces-too).
(blueprint: lem-sfb-stack-chartwise-smooth-etale-calculus).

Proof:
10. Use the field-extension lifting meaning of surjectivity. This argument applies to arbitrary
stack morphisms, whether or not representable. If $f:\mathcal X\to\mathcal Y$ is surjective and
$x'$ is an object of $\mathcal Y'$ over a field $K$, lift its image in $\mathcal Y$ after
$K\hookrightarrow L$ to an object $x$ of $\mathcal X$ and an isomorphism $f(x)\simeq x'|_L$. The
triple $(x'|_L,x,\phi)$ is an object of $\mathcal Y'\times_{\mathcal Y}\mathcal X$ over $L$
lifting $x'$. For two surjective composable maps, lift first over $K\hookrightarrow L$ through the
second map, then over $L\hookrightarrow M$ through the first. Restriction and composition of the
two isomorphisms gives a lift of the original object over $M$. These constructions use exactly the
2-fibre product of [def-sfb-stable-pointed-moduli-groupoids] and prove surjectivity under
arbitrary base change and composition. The assertions include empty targets: there is then no
field-valued object to lift.
Uses: def-sfb-stable-pointed-moduli-groupoids.
-/
theorem surjective_moduli_baseChange
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)}
    (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G)
    (hH : IsAlgebraicModuliStack H) (f : BasedFunctor F G) (g : BasedFunctor H G)
    (hf : IsSurjectiveModuliMap f) :
    IsSurjectiveModuliMap (moduliTwoFiberFst g f) := by
  have _ := hF
  have _ := hG
  have _ := hH
  intro K _ b y
  obtain ⟨L, hL, i, x, ⟨e⟩⟩ := hf K b (y.comp g)
  let ri : Over.mk (Spec.map (CommRingCat.ofHom i) ≫ b) ⟶ Over.mk b :=
    Over.homMk (Spec.map (CommRingCat.ofHom i)) rfl
  let d := discreteModuliMap (yoneda.map ri)
  let a := moduliTwoFiberLift (d.comp y) x (BasedNatIso.mkNatIso e.val e.property).symm
  refine ⟨L, hL, i, a, ?_⟩
  refine ⟨⟨Iso.refl _, fun z ↦ ?_⟩⟩
  exact IsHomLift.id ((d.comp y).w_obj z)

private def twoIsoWhiskerRight
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)}
    {p q : BasedFunctor F G} (α : ModuliTwoIso p q) (g : BasedFunctor G H) :
    ModuliTwoIso (p.comp g) (q.comp g) := by
  refine ⟨Functor.isoWhiskerRight α.val g.toFunctor, fun x ↦ ?_⟩
  have := α.property x
  exact g.preserves_isHomLift _ _

private def twoIsoWhiskerLeft
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)}
    (g : BasedFunctor F G) {p q : BasedFunctor G H} (α : ModuliTwoIso p q) :
    ModuliTwoIso (g.comp p) (g.comp q) :=
  ⟨Functor.isoWhiskerLeft g.toFunctor α.val,
    fun x ↦ (g.w_obj x) ▸ α.property (g.obj x)⟩

private def twoIsoTrans
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {p q r : BasedFunctor F G} (α : ModuliTwoIso p q) (β : ModuliTwoIso q r) :
    ModuliTwoIso p r := by
  refine ⟨α.val ≪≫ β.val, fun x ↦ ?_⟩
  have := α.property x
  have := β.property x
  exact IsHomLift.comp_of_lift_id _ _ _ _

private theorem discreteModuliMap_comp
    {S : Scheme.{u}} {P Q R : (Over S)ᵒᵖ ⥤ Type u}
    (a : P ⟶ Q) (b : Q ⟶ R) :
    (discreteModuliMap a).comp (discreteModuliMap b) = discreteModuliMap (a ≫ b) := by
  rfl

/-- Surjectivity is stable under composition, including nonrepresentable maps.
Source: Section 04XB (section-properties-morphisms), including Tag 04XC
(lemma-property-spaces-too).
(blueprint: lem-sfb-stack-chartwise-smooth-etale-calculus).

Proof:
10. Use the field-extension lifting meaning of surjectivity. This argument applies to arbitrary
stack morphisms, whether or not representable. If $f:\mathcal X\to\mathcal Y$ is surjective and
$x'$ is an object of $\mathcal Y'$ over a field $K$, lift its image in $\mathcal Y$ after
$K\hookrightarrow L$ to an object $x$ of $\mathcal X$ and an isomorphism $f(x)\simeq x'|_L$. The
triple $(x'|_L,x,\phi)$ is an object of $\mathcal Y'\times_{\mathcal Y}\mathcal X$ over $L$
lifting $x'$. For two surjective composable maps, lift first over $K\hookrightarrow L$ through the
second map, then over $L\hookrightarrow M$ through the first. Restriction and composition of the
two isomorphisms gives a lift of the original object over $M$. These constructions use exactly the
2-fibre product of [def-sfb-stable-pointed-moduli-groupoids] and prove surjectivity under
arbitrary base change and composition. The assertions include empty targets: there is then no
field-valued object to lift.
Uses: def-sfb-stable-pointed-moduli-groupoids.
-/
theorem surjective_moduli_comp
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)}
    (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G)
    (hH : IsAlgebraicModuliStack H) (f : BasedFunctor F G) (g : BasedFunctor G H)
    (hf : IsSurjectiveModuliMap f) (hg : IsSurjectiveModuliMap g) :
    IsSurjectiveModuliMap (f.comp g) := by
  have _ := hF
  have _ := hG
  have _ := hH
  intro K _ b y
  obtain ⟨L, hL, i, z, ⟨e⟩⟩ := hg K b y
  obtain ⟨M, hM, j, x, ⟨d⟩⟩ := hf L (Spec.map (CommRingCat.ofHom i) ≫ b) z
  let ri : Over.mk (Spec.map (CommRingCat.ofHom i) ≫ b) ⟶ Over.mk b :=
    Over.homMk (Spec.map (CommRingCat.ofHom i)) rfl
  let rj : Over.mk (Spec.map (CommRingCat.ofHom j) ≫
      (Spec.map (CommRingCat.ofHom i) ≫ b)) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom i) ≫ b) :=
    Over.homMk (Spec.map (CommRingCat.ofHom j)) rfl
  let dj := discreteModuliMap (yoneda.map rj)
  have hε : ModuliTwoIso (x.comp (f.comp g))
      (dj.comp ((discreteModuliMap (yoneda.map ri)).comp y)) :=
    twoIsoTrans (twoIsoWhiskerRight d g) (twoIsoWhiskerLeft dj e)
  have hd : dj.comp ((discreteModuliMap (yoneda.map ri)).comp y) =
      (discreteModuliMap (yoneda.map rj ≫ yoneda.map ri)).comp y := by
    rw [← BasedFunctor.comp_assoc, discreteModuliMap_comp]
  rw [hd] at hε
  have hij : Spec.map (CommRingCat.ofHom (j.comp i)) =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom i) :=
    Spec.map_comp (CommRingCat.ofHom i) (CommRingCat.ofHom j)
  let r : Over.mk (Spec.map (CommRingCat.ofHom (j.comp i)) ≫ b) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom j) ≫
        (Spec.map (CommRingCat.ofHom i) ≫ b)) :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom j) ≫
        (Spec.map (CommRingCat.ofHom i) ≫ b)) =
          Spec.map (CommRingCat.ofHom (j.comp i)) ≫ b
      rw [Category.id_comp, hij, Category.assoc])
  let rk : Over.mk (Spec.map (CommRingCat.ofHom (j.comp i)) ≫ b) ⟶ Over.mk b :=
    Over.homMk (Spec.map (CommRingCat.ofHom (j.comp i))) rfl
  have hr : r ≫ rj ≫ ri = rk := by
    apply Over.OverMorphism.ext
    change 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom j) ≫
      Spec.map (CommRingCat.ofHom i)) = Spec.map (CommRingCat.ofHom (j.comp i))
    exact (Category.id_comp _).trans hij.symm
  have hn : yoneda.map r ≫ (yoneda.map rj ≫ yoneda.map ri) = yoneda.map rk := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, hr]
  let dk := discreteModuliMap (yoneda.map r)
  refine ⟨M, hM, j.comp i, dk.comp x, ?_⟩
  have h := twoIsoWhiskerLeft dk hε
  have hd' : dk.comp ((discreteModuliMap (yoneda.map rj ≫ yoneda.map ri)).comp y) =
      (discreteModuliMap (yoneda.map r ≫ (yoneda.map rj ≫ yoneda.map ri))).comp y := by
    rw [← BasedFunctor.comp_assoc, discreteModuliMap_comp]
  rw [hd', hn] at h
  exact ⟨h⟩

/-- For representable maps, field-extension lifting is equivalent to surjectivity of
every surjective étale scheme chart of every scheme base change.
Source: Section 04XB (section-properties-morphisms), including Tag 04XC
(lemma-property-spaces-too).
(blueprint: lem-sfb-stack-chartwise-smooth-etale-calculus).

Proof:
3. Here are the fibre-product identifications and chart operations used below. Fibre products of
algebraic spaces exist by [lem-trf-space-fibre-products-etale-covers]. A map from a scheme $U$ to
a space $F$ is representable: for another scheme $T\to F$, $U\times_F T$ is the pullback of the
representable diagonal of $F$ along $U\times_S T\to F\times_S F$, so is a scheme by
[def-trf-algebraic-space]. For the chart operations we use only representable etale maps
(scheme-valued tests). For such $a:A\to B$ and $b:B\to C$, a scheme test $T\to C$ factors their
composite as the etale scheme maps $A_T\to B_T\to T$; step 1 gives etaleness of the composite. If
the two maps are surjective, these scheme maps are surjective and
[lem-trf-surjective-morphism-composition] applies. Arbitrary base change retains exactly the same
scheme tests; base changes of an etale surjective scheme map are etale by step 1 and surjective by
[lem-weil-pbc-surjective-base-change]. Hence these operations preserve representable etale charts
and their covering property. In all ensuing 2-pullback reassociations the functor keeps the maps
to the factors and composes the displayed isomorphisms between their images; its inverse inserts
the identity isomorphism at the repeated factor. Thus these reassociations are equivalences of the
explicit groupoids of [def-sfb-stable-pointed-moduli-groupoids], compatible with all projections.
Uses: lem-trf-space-fibre-products-etale-covers, def-trf-algebraic-space,
lem-trf-surjective-morphism-composition, lem-weil-pbc-surjective-base-change,
def-sfb-stable-pointed-moduli-groupoids.
13. Here is the comparison of the two surjectivity conventions for $f:\mathcal X\to\mathcal Y$
representable by algebraic spaces. For a scheme $T\to\mathcal Y$ put $A=\mathcal X\times_{\mathcal
Y}T$, an algebraic space, and recall from step 3 that maps from schemes to $A$ are representable.
Suppose $f$ is surjective in the field-lifting sense, and let $U\to A$ be any surjective etale
scheme chart and $t\in T$. Restrict the object of $\mathcal Y$ over $T$ to $y$ over
$\operatorname{Spec}\kappa(t)$; lifting gives $\kappa(t)\hookrightarrow L$, an object $x$ of
$\mathcal X$ over $L$ and $\phi:f(x)\simeq y|_L$. By the tuple description of
[def-sfb-stable-pointed-moduli-groupoids], $(x,\operatorname{Spec}L\to T,\phi)$ is a map
$s:\operatorname{Spec}L\to A$ whose composite to $T$ has image $t$. The scheme
$U\times_{A,s}\operatorname{Spec}L$ maps surjectively onto $\operatorname{Spec}L$ by the
definition of a surjective representable map in [def-trf-algebraic-space], so it has a point; its
image $u\in U$ maps to $t$. Hence $U\to T$ is surjective [def-weil-surjective-morphism].
Conversely suppose that for each scheme $T\to\mathcal Y$ some surjective etale scheme chart $U\to
A$ has $U\to T$ surjective. For an object $y$ of $\mathcal Y$ over $\operatorname{Spec}K$ take
$T=\operatorname{Spec}K$ and such a chart $U$ (a chart exists by [def-trf-algebraic-space]). As
$U\to\operatorname{Spec}K$ is surjective, $U$ has a point $u$; put $L=\kappa(u)\supseteq K$. The
composite $\operatorname{Spec}L\to U\to A$ is, by the same tuple description, an object $x$ of
$\mathcal X$ over $L$, the map $\operatorname{Spec}L\to\operatorname{Spec}K$ and an isomorphism
$f(x)\simeq y|_L$: the required lift. Thus the field-lifting condition, the chart test for every
chart and the chart test for one chart per $T$ are equivalent, and step 10 applies in either
reading; empty $T$ and empty $\mathcal Y$ are included.
Uses: def-sfb-stable-pointed-moduli-groupoids, def-trf-algebraic-space,
def-weil-surjective-morphism.
-/
theorem surjective_moduli_iff_chartwise
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G)
    (f : BasedFunctor F G) (hf : IsRepresentableByAlgebraicSpaces f) :
    IsSurjectiveModuliMap f ↔
      ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G)
        (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange f T t Z p →
          ∀ (U : Over S) (a : yoneda.obj U ⟶ Z.obj.obj),
            AlgebraicSpace.IsEtale a → AlgebraicSpace.IsSurjective a →
              Surjective (yoneda.preimage (a ≫ p)).left := by
  sorry

/-- Maps from scheme summands glue over their coproduct to an étale representable map.
The coproduct is assumed to exist in the chosen scheme category; the index universe
is independent, and no smallness assumption on the index set is imposed.
Source: Section 04XB (section-properties-morphisms), including Tag 04XC
(lemma-property-spaces-too).
(blueprint: lem-sfb-stack-chartwise-smooth-etale-calculus).

Proof:
11. Let $U=\coprod_iU_i$ be the scheme supplied by [lem-weil-pbc-scheme-coproduct-family], in the
universe required by [def-weil-size-convention]. Its summands give a disjoint open cover. The maps
$q_i$ are objects of $\mathcal X(U_i)$ by [def-sfb-stable-pointed-moduli-groupoids]. On distinct
overlaps the base is empty, and stack descent for the empty cover identifies the fibre over the
empty scheme with the terminal groupoid; hence the restrictions have a unique overlap isomorphism,
satisfying the cocycle equation. Effective descent on the disjoint open cover gives an object over
$U$ restricting to these objects. It defines $q:U\to\mathcal X$, with specified 2-isomorphisms
$q|_{U_i}\simeq q_i$. This is a descent construction of the map to a stack; the ordinary scheme
coproduct universal property is used only to construct the source.
Uses: lem-weil-pbc-scheme-coproduct-family, def-weil-size-convention,
def-sfb-stable-pointed-moduli-groupoids.
12. For a scheme $T\to\mathcal X$, the 2-fibre product $U\times_{\mathcal X}T$ is the pullback of
$\Delta_{\mathcal X/S}$ along the scheme $U\times_ST\to\mathcal X\times_S\mathcal X$. Indeed both
groupoids consist of maps to $U,T$ with an isomorphism between their images; this is the tuple
description of [def-sfb-stable-pointed-moduli-groupoids]. Since the diagonal of the algebraic
stack is representable by spaces, its scheme pullback is a space. Thus $q$ is representable by
spaces without any assertion that an arbitrary disjoint union of spaces is already constructed.
Apply the source-locality result of step 8 to the open cover $U=\bigcup_iU_i$: each restriction is
the given etale $q_i$, so $q$ is etale. For the empty index set, descent gives the unique object
over the empty scheme and the same empty-cover argument in step 8 applies.
Uses: def-sfb-stable-pointed-moduli-groupoids, def-trf-algebraic-space.
-/
theorem etale_moduli_scheme_coproduct
    {S : Scheme.{u}} {F : BasedCategory.{v₁, w₁} (Over S)}
    (hF : IsAlgebraicModuliStack F) (I : Type z) (U : I → Over S) [HasCoproduct U]
    (q : ∀ i : I, BasedFunctor (discreteModuli (yoneda.obj (U i))) F)
    (hq : ∀ i : I, IsEtaleModuliMap (q i)) :
    ∃ a : BasedFunctor (discreteModuli (yoneda.obj (∐ U))) F,
      (∀ i : I, Nonempty (ModuliTwoIso
        ((discreteModuliMap (yoneda.map (Sigma.ι U i))).comp a) (q i))) ∧
      IsEtaleModuliMap a ∧ IsRepresentableByAlgebraicSpaces a := by
  sorry

end CategoryTheory
