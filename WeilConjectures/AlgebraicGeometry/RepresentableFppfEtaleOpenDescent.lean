/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.AlgebraicModuliStack
public import WeilConjectures.AlgebraicGeometry.DmStackMorphismProperties
public import WeilConjectures.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.FppfAffineRefinement
import WeilConjectures.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import WeilConjectures.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import WeilConjectures.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationFppfSource
import WeilConjectures.AlgebraicGeometry.ChartwiseEtalePermanence
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent

/-! # Fppf testing of representable morphism properties

Source: Stacks Project, stacks-properties.tex, Tag 04XD; spaces-descent.tex,
Tags 041W, 041T, 041X, 042B, 06ET and 06EV
(blueprint: lem-sfb-representable-fppf-etale-open-descent).

The first two statements concern representable stack maps. The next two state the
algebraic-space versions, and the last states source-and-target locality of flatness
and local finite presentation. A cartesian square permits any model of the space
fibre product, retaining its actual projection. Open immersions use representable
scheme tests, rather than the source-local chart predicate.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Flatness, local finite presentation and étaleness of a representable stack map
are independently detected on a surjective flat locally finitely presented space cover.
Source: Stacks, Tag 04XD; spaces-descent.tex, Tags 041W, 041T and 042B
(blueprint: lem-sfb-representable-fppf-etale-open-descent).

Proof:
1. The forward direction is base-change stability from
   lem-sfb-stack-chartwise-smooth-etale-calculus. For the reverse direction and a
   scheme T → G put Z = F ×_G T and A = V ×_G T; these are spaces by
   lem-sfb-representable-pullback-over-space. The triple description of 2-pullbacks
   identifies Z ×_T A with (F ×_G V) ×_V A, respecting projections.
2. Choose a surjective étale scheme atlas U → A (def-trf-algebraic-space).
   The chartwise calculus makes U → T surjective, flat and locally finitely presented.
   This singleton fppf cover is fpqc in the family sense: on each affine open of T,
   base change by lem-trf-fppf-covering-base-change and use
   lem-pc-fppf-affine-refinement to find finitely many affine opens covering it.
   This is exactly def-weil-pbc-fpqc-covering; no quasi-compactness of U → T is needed.
3. Choose a surjective étale scheme atlas E → Z. Its pullback E_U → Z_U is such
   an atlas by lem-trf-space-fibre-products-etale-covers. By
   lem-sfb-scheme-etale-source-target-properties and
   lem-sfb-space-etale-presentation-property-criterion, the assumed property gives
   P(E_U → U). Descend along {U → T}, using respectively
   lem-weil-pbc-fpqc-descend-flat,
   lem-weil-pbc-fpqc-descend-locally-finite-presentation, or
   lem-galois-fpqc-descend-etale. The presentation criterion gives P(Z → T).
4. This works for every T → G and hence gives the defining ModuliSpaceTest.
   Each choice of P is independent of the other two properties. -/
theorem representable_fppf_target_property {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G)
    (f : BasedFunctor F G) (hf : IsRepresentableByAlgebraicSpaces f)
    (V : AlgebraicSpace S) (q : BasedFunctor (discreteModuli V.obj.obj) G)
    (hq : IsRepresentableByAlgebraicSpaces q) (hs : IsSurjectiveModuliMap q)
    (hflat : ModuliSpaceTest @Flat q)
    (hlfp : ModuliSpaceTest @LocallyOfFinitePresentation q)
    (P : MorphismProperty Scheme.{u})
    (hP : P = @Flat ∨ P = @LocallyOfFinitePresentation ∨ P = @Etale) :
    ModuliSpaceTest P f ↔ ModuliSpaceTest P (moduliTwoFiberFst q f) := by
  sorry

/-- Open immersion of a representable stack map is detected on the same fppf cover.
Source: Stacks, Tag 04XD; spaces-descent.tex, Tag 041X
(blueprint: lem-sfb-representable-fppf-etale-open-descent).

Proof:
1. Forward base change follows directly from the scheme-test definition: the test
   T → V yields the same F ×_G T with the same projection.
2. Conversely, for T → G put Z = F ×_G T and A = V ×_G T. They are spaces by
   lem-sfb-representable-pullback-over-space. Choose an étale surjective scheme atlas
   U → A. The chartwise calculus makes U → T surjective, flat and locally finitely
   presented. By lem-trf-fppf-covering-base-change and
   lem-pc-fppf-affine-refinement its singleton is an fpqc family in the sense of
   def-weil-pbc-fpqc-covering, without quasi-compactness of the map.
3. Associativity identifies Z_U with (F ×_G V) ×_V U over U. The hypothesis makes
   Z_U a scheme open in U. Apply lem-sfb-space-fpqc-open-immersion-descent to Z → T
   and {U → T}, obtaining a scheme open immersion Z → T. These are exactly the
   tests in ModuliSchemeTest; no source-locality assertion is used. -/
theorem representable_fppf_target_openImmersion {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G)
    (f : BasedFunctor F G) (hf : IsRepresentableByAlgebraicSpaces f)
    (V : AlgebraicSpace S) (q : BasedFunctor (discreteModuli V.obj.obj) G)
    (hq : IsRepresentableByAlgebraicSpaces q) (hs : IsSurjectiveModuliMap q)
    (hflat : ModuliSpaceTest @Flat q)
    (hlfp : ModuliSpaceTest @LocallyOfFinitePresentation q) :
    ModuliSchemeTest @IsOpenImmersion f ↔
      ModuliSchemeTest @IsOpenImmersion (moduliTwoFiberFst q f) := by
  sorry

end CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The flat, locally finitely presented and étale equivalences for space maps.
The square identifies Xv with X ×_Y V, and p with its projection to V.
Source: Stacks, spaces-descent.tex, Tags 041W, 041T and 042B
(blueprint: lem-sfb-representable-fppf-etale-open-descent).

Proof: Apply the scheme-chart argument of representable_fppf_target_property to the
actual sheaf fibre product. The discrete fibred groupoids have these same pullbacks.
The criterion lem-sfb-space-etale-presentation-property-criterion and
lem-sfb-scheme-etale-source-target-properties identify the space chart predicates
with the scheme tests. Equivalently fix a scheme test T → Y, choose a surjective
étale scheme atlas U of V ×_Y T and an atlas E of X ×_Y T, and descend the property
of E_U → U along the singleton fpqc family {U → T}. The three scheme descent
inputs are lem-weil-pbc-fpqc-descend-flat,
lem-weil-pbc-fpqc-descend-locally-finite-presentation and
lem-galois-fpqc-descend-etale, independently. The family is fpqc by affine refinement
(lem-trf-fppf-covering-base-change, lem-pc-fppf-affine-refinement,
def-weil-pbc-fpqc-covering). The forward direction is base change. -/
theorem fppf_target_property {S : Scheme.{u}} {X Y V Xv : AlgebraicSpace S}
    (f : X ⟶ Y) (q : V ⟶ Y) (r : Xv ⟶ X) (p : Xv ⟶ V)
    (hpb : IsPullback r.hom p.hom f.hom q.hom)
    (hs : IsJointlySurjective (fun _ : Unit ↦ q.hom.hom))
    (hflat : MapIsFlat q) (hlfp : MapIsLocallyOfFinitePresentation q)
    (P : MorphismProperty Scheme.{u})
    (hP : P = @Flat ∨ P = @LocallyOfFinitePresentation ∨ P = @Etale) :
    MapIsLocally P f ↔ MapIsLocally P p := by
  sorry

/-- The open-immersion equivalence for algebraic spaces, using scheme tests.
Source: Stacks, spaces-descent.tex, Tag 041X
(blueprint: lem-sfb-representable-fppf-etale-open-descent).

Proof: Base change proves the forward direction. Conversely fix a scheme T → Y
and choose an étale surjective scheme atlas U of V ×_Y T. The calculus
lem-sfb-stack-chartwise-smooth-etale-calculus makes U → T flat, locally finitely
presented and surjective. Base change and finite affine refinement
(lem-trf-fppf-covering-base-change, lem-pc-fppf-affine-refinement) make its singleton
an fpqc family (def-weil-pbc-fpqc-covering). The pullback of X to U is a scheme
open in U by the hypothesis and the specified cartesian square. Then
lem-sfb-space-fpqc-open-immersion-descent makes X ×_Y T an open subscheme of T.
For every T this is precisely the representable-with-open-immersions predicate. -/
theorem fppf_target_openImmersion {S : Scheme.{u}} {X Y V Xv : AlgebraicSpace S}
    (f : X ⟶ Y) (q : V ⟶ Y) (r : Xv ⟶ X) (p : Xv ⟶ V)
    (hpb : IsPullback r.hom p.hom f.hom q.hom)
    (hs : IsJointlySurjective (fun _ : Unit ↦ q.hom.hom))
    (hflat : MapIsFlat q) (hlfp : MapIsLocallyOfFinitePresentation q) :
    IsRepresentableWith (fun _ _ a ↦ IsOpenImmersion a.left) f.hom.hom ↔
      IsRepresentableWith (fun _ _ a ↦ IsOpenImmersion a.left) p.hom.hom := by
  sorry

/-- Flatness and local finite presentation are local on both source and target
for surjective flat locally finitely presented space covers. There is no such
source-local claim for étaleness or open immersions.
Source: Stacks, spaces-descent.tex, Tags 06ET, 06EV; descent.tex, Tags 036K, 036N
(blueprint: lem-sfb-representable-fppf-etale-open-descent).

Proof:
1. Put X0 = X ×_Y V. Forward base change followed by composition with h proves
   P(W → V), by lem-sfb-stack-chartwise-smooth-etale-calculus.
2. Conversely choose surjective étale scheme charts T → V, E → X0 ×_V T,
   D → W ×_X0 E (def-trf-algebraic-space,
   lem-trf-space-fibre-products-etale-covers). Then D → E is surjective, flat and
   locally finitely presented by base change and composition in the chartwise calculus.
3. D → W ×_V T is étale, since the intermediate map is the base change of E → X_T
   (lem-trf-space-chartwise-etale-permanence). Thus P(W → V) gives P(D → T), by
   lem-sfb-scheme-etale-source-target-properties and
   lem-sfb-space-etale-presentation-property-criterion. Surjectivity of this chart
   over W_T is unnecessary for this implication.
4. If P is flat use lem-pc-flat-source-descent on D → E → T. If P is local finite
   presentation use lem-trf-lfp-fppf-source-locality on the singleton {D → E}.
   Each gives P(E → T) without assuming the other property on W → V.
5. The presentation criterion first gives P(X_T → T), then P(X0 → V), since
   E → X0 is a surjective étale chart by the étale-permanence node. Target locality
   fppf_target_property then gives P(f). No quasi-compactness is assumed. -/
theorem fppf_source_target_property {S : Scheme.{u}}
    {X Y V Xv W : AlgebraicSpace S}
    (f : X ⟶ Y) (q : V ⟶ Y) (r : Xv ⟶ X) (p : Xv ⟶ V)
    (hpb : IsPullback r.hom p.hom f.hom q.hom) (h : W ⟶ Xv)
    (hqs : IsJointlySurjective (fun _ : Unit ↦ q.hom.hom))
    (hqflat : MapIsFlat q) (hqlfp : MapIsLocallyOfFinitePresentation q)
    (hhs : IsJointlySurjective (fun _ : Unit ↦ h.hom.hom))
    (hhflat : MapIsFlat h) (hhlfp : MapIsLocallyOfFinitePresentation h)
    (P : MorphismProperty Scheme.{u}) (hP : P = @Flat ∨ P = @LocallyOfFinitePresentation) :
    MapIsLocally P f ↔ MapIsLocally P (h ≫ p) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
