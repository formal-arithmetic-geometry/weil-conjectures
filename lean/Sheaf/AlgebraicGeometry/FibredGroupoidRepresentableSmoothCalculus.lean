/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Representable smooth and étale calculus for fibred groupoids

Source: Stacks Project, algebraic.tex, Tags 0301, 0302, 045A, 045B and 045C;
spaces-morphisms.tex, Tags 03ZD, 03ZE and 04XX; spaces-properties.tex, Tags 03FT and 03FU
(blueprint: lem-sfb-fibred-groupoid-representable-smooth-calculus).

All categories are only fibred in groupoids. Smoothness and étaleness use the existing
étale scheme-chart tests on the representing spaces. The first statement identifies
field-extension lifting with surjectivity on point classes of every space test.
No stack, diagonal or atlas hypothesis is imposed on an input category.

## Main statements

- `fibred_groupoid_surjective_iff_space_tests`: the point-class convention on scheme tests.
- `fibred_groupoid_representable_baseChange`: arbitrary 2-base-change stability.
- `fibred_groupoid_representable_comp`: composition stability.
- `fibred_groupoid_etale_smooth`: representable étale maps are smooth.
- `space_discrete_moduli_comparison`: maps of spaces and scheme-representable comparisons.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry

namespace CategoryTheory

/-- The existing field-lifting predicate is exactly point-class surjectivity on every
algebraic-space scheme test, together with representability.
Source: Stacks, algebraic.tex, Tag 045A; spaces-properties.tex, Tag 03BU
(blueprint: lem-sfb-fibred-groupoid-representable-smooth-calculus).

Proof: Fix a test `t : h_T → G` and a field-valued point of its representing space's
scheme target. A point of the 2-pullback is a triple consisting of a source object,
a point of `T` and an isomorphism of their images. Thus field-extension lifting for
`f` gives exactly a lift of this point after extension, and conversely the test with
`T = Spec K` recovers the required object and isomorphism. The equivalence in
`HasSpaceBaseChange` transports those triples to sections of the representing space.
By def-trf-algebraic-space-jointly-surjective-family this extension-lifting assertion
is surjectivity on point classes. Representability supplies the space for every test;
the reverse implication forgets its point-class condition to recover representability.
No descent of objects in either input groupoid is used. -/
theorem fibred_groupoid_surjective_iff_space_tests {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G) (f : BasedFunctor F G) :
    (IsRepresentableByAlgebraicSpaces f ∧ IsSurjectiveModuliMap f) ↔
      ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
        ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange f T t Z p ∧
            AlgebraicSpace.IsJointlySurjective (fun _ : Unit ↦ p) := by
  sorry

/-- Representability, smoothness, étaleness and representable surjectivity survive
base change by any category fibred in groupoids.
Source: Stacks, algebraic.tex, Tags 0302 and 045C
(blueprint: lem-sfb-fibred-groupoid-representable-smooth-calculus).

Proof: For `f : F → G`, `g : H → G` and a scheme `T → H`, identify
`(H ×_G F) ×_H T` with `T ×_G F`. On triples, compose the two comparison
isomorphisms, applying `g` to the comparison in `H`. The inverse inserts the object
coming from `T` and its identity comparison. The given comparison identifies the
other composite with the identity, on arrows as well as objects, and these formulas
commute with restriction (def-sfb-stable-pointed-moduli-groupoids). Hence every scheme
test of the projection is a scheme test of `f` over the same `T`. Its space witness,
smooth or étale chart property, and point-class surjectivity transport along this
equivalence. For the surjectivity clause use the preceding field-lifting comparison.
There is no stack hypothesis on `H` or either other category. -/
theorem fibred_groupoid_representable_baseChange {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (hH : IsFibredInGroupoids H) (f : BasedFunctor F G) (g : BasedFunctor H G)
    (hf : IsRepresentableByAlgebraicSpaces f) :
    IsRepresentableByAlgebraicSpaces (moduliTwoFiberFst g f) ∧
      (ModuliSpaceTest @Smooth f → ModuliSpaceTest @Smooth (moduliTwoFiberFst g f)) ∧
      (IsEtaleModuliMap f → IsEtaleModuliMap (moduliTwoFiberFst g f)) ∧
      (IsSurjectiveModuliMap f → IsSurjectiveModuliMap (moduliTwoFiberFst g f)) := by
  sorry

/-- Representability and each of smoothness, étaleness and surjectivity compose.
Source: Stacks, algebraic.tex, Tags 0301 and 045B; spaces-morphisms.tex, Tag 03ZD;
spaces-properties.tex, Tag 03FT
(blueprint: lem-sfb-fibred-groupoid-representable-smooth-calculus).

Proof: Fix `T → H`, put `B = G ×_H T`, and apply
lem-sfb-representable-pullback-over-space to `f` and `B → G` to obtain the space
`A = F ×_G B`. Reassociate triples: `(x,(y,t,γ),α)` maps to `(x,t,γ g(α))`;
the inverse inserts `y = f(x)` and the identity. This is an equivalence over `T`,
so `A` represents the composite test.
For smoothness or étaleness choose an étale surjective scheme chart `V → B`, and
then a chart `U → A ×_B V`. The scheme-locality lemma and presentation criterion
(lem-sfb-scheme-etale-source-target-properties and
lem-sfb-space-etale-presentation-property-criterion) give the property for `U → V`
and `V → T`. Scheme composition (lem-trf-smooth-composition or
lem-weil-pbc-etale-composition-cancellation) gives it for `U → T`.
The chart `U → A` is étale surjective by
lem-trf-space-fibre-products-etale-covers and
lem-trf-space-representable-etale-scheme-tests, so the criterion gives it for `A → T`.
For surjectivity, a point over `K` first lifts to `B` over an extension `L`, and then
through the test of `f` over an extension `M` of `L`. These data form an `M`-point
of `A` over the original point. Two successive field extensions prove point-class
surjectivity, by def-trf-algebraic-space-jointly-surjective-family. -/
theorem fibred_groupoid_representable_comp {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (hH : IsFibredInGroupoids H) (f : BasedFunctor F G) (g : BasedFunctor G H)
    (hf : IsRepresentableByAlgebraicSpaces f) (hg : IsRepresentableByAlgebraicSpaces g) :
    IsRepresentableByAlgebraicSpaces (f.comp g) ∧
      (ModuliSpaceTest @Smooth f → ModuliSpaceTest @Smooth g →
        ModuliSpaceTest @Smooth (f.comp g)) ∧
      (IsEtaleModuliMap f → IsEtaleModuliMap g → IsEtaleModuliMap (f.comp g)) ∧
      (IsSurjectiveModuliMap f → IsSurjectiveModuliMap g →
        IsSurjectiveModuliMap (f.comp g)) := by
  sorry

/-- Every representable étale map of fibred groupoids is smooth.
Source: Stacks, spaces-morphisms.tex, Tag 04XX
(blueprint: lem-sfb-fibred-groupoid-representable-smooth-calculus).

Proof: On each space test choose an étale scheme chart of the source. Its projection
to the test scheme is étale by `SpaceMapIsEtale`. Apply
lem-weil-pbc-etale-smooth-zero-dimensional-fibres to this scheme map to get smoothness.
Doing this for every chart gives `ModuliSpaceTest @Smooth`, with the same space
witnesses and projection comparisons. Equivalently this is the presentation criterion
and the scheme-locality lemma for étale and smooth, with étale implying smooth on
schemes. No condition on the original groupoids beyond being fibred is required. -/
theorem fibred_groupoid_etale_smooth {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G) (f : BasedFunctor F G)
    (hf : IsEtaleModuliMap f) : ModuliSpaceTest @Smooth f := by
  sorry

/-- Maps of algebraic spaces are space-representable; for scheme-representable maps
the old étale and surjective scheme tests agree with the fibred-groupoid tests.
Source: Stacks, algebraic.tex, Tag 045A and
lemma-morphism-spaces-gives-representable-by-spaces; spaces-morphisms.tex, Tag 03MJ
(blueprint: lem-sfb-fibred-groupoid-representable-smooth-calculus).

Proof: A scheme test is the sheaf fibre product of the source space with the test
scheme, hence an algebraic space by lem-trf-space-fibre-products-etale-covers.
For discrete fibres its pairs are exactly the triples of the 2-fibre product: the
comparison exists precisely for equal images and is unique. This proves representability.
If the original map is scheme-representable, every test projection is a scheme map.
The presentation criterion and scheme-locality lemma identify chartwise étaleness
with scheme étaleness, test by test. For surjectivity, a topologically surjective
scheme map stays surjective after base change (lem-weil-pbc-surjective-base-change).
Base change along `Spec K`, choose a point of the nonempty fibre, and take its residue
field to get a lift after a field extension. Conversely apply field-extension lifting
to `Spec κ(t)` for each point `t` of the target; the lift gives a source point above `t`.
Thus field-point and topological surjectivity agree, including empty schemes. A scheme
chart is scheme-representable by def-trf-algebraic-space, so the comparison includes it. -/
theorem space_discrete_moduli_comparison {S : Scheme.{u}}
    {G F : AlgebraicSpace S} (f : G ⟶ F) :
    IsRepresentableByAlgebraicSpaces (discreteModuliMap f.hom.hom) ∧
      (AlgebraicSpace.IsRepresentable f.hom.hom →
        (AlgebraicSpace.IsEtale f.hom.hom ↔
          IsEtaleModuliMap (discreteModuliMap f.hom.hom)) ∧
        (AlgebraicSpace.IsSurjective f.hom.hom ↔
          IsSurjectiveModuliMap (discreteModuliMap f.hom.hom))) := by
  sorry

end CategoryTheory
