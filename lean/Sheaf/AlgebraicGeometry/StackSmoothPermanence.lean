/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.SmoothModuliMap
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Permanence of smooth morphisms of algebraic stacks

Source: Stacks Project, Morphisms of Stacks, Tags 075V and 075W
(blueprint: lem-sfb-stack-smooth-permanence).

Smoothness uses the smooth scheme presentation definition, including morphisms that
are not representable. Base change is the actual category of triples and its second
projection. No condition is imposed on the base-changing map.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry

namespace CategoryTheory

/-- Smooth morphisms of algebraic stacks over a field compose and remain smooth
under arbitrary 2-base change. Scheme and algebraic-space maps are included as
maps of their discrete fibred groupoids; representable smoothness is tested on
scheme base changes, as in Tags 06FM and 075U.
Source: Stacks Project, Morphisms of Stacks, Tags 075V and 075W
(blueprint: lem-sfb-stack-smooth-permanence).

Proof:
1. Choose compatible successive smooth scheme atlases W of Z, V of Y ×_Z W,
   and U of X ×_Y V. Algebraicity of these products is supplied by
   lem-sfb-algebraic-stack-fibre-products. The representable calculus
   lem-sfb-fibred-groupoid-representable-smooth-calculus makes their composites
   smooth surjective charts. Apply condition (A) of
   lem-sfb-stack-smooth-presentation-criterion to g and f to obtain smooth maps
   V → W and U → V. The scheme/space comparison is
   lem-sfb-space-etale-presentation-property-criterion with the smooth case of
   lem-sfb-scheme-etale-source-target-properties. Their composite is smooth by
   lem-trf-smooth-composition. Condition (B) of the presentation criterion gives
   smoothness of f.comp g.
2. For any h : Z → Y choose atlases V of Y, U of X ×_Y V and V' of Z ×_Y V.
   The same criterion makes U → V smooth. Set E = U ×_V V'. The representable
   calculus makes E → V' smooth. Reassociate the triples and their specified
   isomorphisms, using def-sfb-stable-pointed-moduli-groupoids, to identify E
   with (X ×_Y V') ×_(X ×_Y V) U and X ×_Y V' with (X ×_Y Z) ×_Z V'. Thus
   E → X ×_Y Z is smooth surjective. Condition (B) applied to E → V' proves
   smoothness of the second projection. No property of h is used.
3. The algebraic-space and representable comparisons in
   lem-sfb-stack-smooth-presentation-criterion identify these statements with
   ordinary smoothness for spaces and the scheme base-change test for
   representable maps. The scheme comparison again uses the etale presentation
   criterion and scheme-etale-source-target-properties. -/
theorem stack_smooth_permanence (k : Type u) [Field k]
    (X : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (Y : BasedCategory.{v₂, w₂} (Over (Spec (.of k))))
    (Z : BasedCategory.{v₃, w₃} (Over (Spec (.of k))))
    (hX : IsAlgebraicModuliStack X) (hY : IsAlgebraicModuliStack Y)
    (hZ : IsAlgebraicModuliStack Z) (f : BasedFunctor X Y) (hf : IsSmoothModuliMap f) :
    (∀ g : BasedFunctor Y Z, IsSmoothModuliMap g → IsSmoothModuliMap (f.comp g)) ∧
      (∀ h : BasedFunctor Z Y, IsSmoothModuliMap (moduliTwoFiberSnd f h)) := by
  sorry

/-- On algebraic spaces, stack smoothness is ordinary smoothness on compatible
etale scheme charts. Source: Stacks Project, Tags 06FM and 075U, as used in the
space clause of Tags 075V and 075W
(blueprint: lem-sfb-stack-smooth-permanence).

Proof: step 3 of the node applies the algebraic-space comparison in
lem-sfb-stack-smooth-presentation-criterion. Ordinary smoothness is
AlgebraicSpace.MapIsLocally @Smooth; its equivalence with a smooth etale
presentation is lem-sfb-space-etale-presentation-property-criterion, using
lem-sfb-scheme-etale-source-target-properties. -/
theorem smoothModuliMap_iff_space (k : Type u) [Field k]
    {A B : AlgebraicSpace (Spec (.of k))} (f : A ⟶ B) :
    IsSmoothModuliMap (discreteModuliMap f.hom.hom) ↔
      AlgebraicSpace.MapIsLocally @Smooth f := by
  sorry

/-- On schemes, stack smoothness is precisely scheme smoothness.
Source: Stacks Project, Tags 06FM and 075U, in the scheme case of 075V and 075W
(blueprint: lem-sfb-stack-smooth-permanence).

Proof: step 3 first applies the space comparison of
lem-sfb-stack-smooth-presentation-criterion. Apply
lem-sfb-space-etale-presentation-property-criterion to the smooth case of
lem-sfb-scheme-etale-source-target-properties. This identifies the chart
condition with Smooth f.left, including the empty scheme. -/
theorem smoothModuliMap_iff_scheme (k : Type u) [Field k]
    {U V : Over (Spec (.of k))} (f : U ⟶ V) :
    IsSmoothModuliMap (discreteModuliMap (yoneda.map f)) ↔ Smooth f.left := by
  sorry

/-- For representable morphisms, smooth charts give exactly smoothness of every
algebraic-space projection after a scheme base change.
Source: Stacks Project, Tags 06FM and 075U, in the representable interpretation
of Tags 075V and 075W (blueprint: lem-sfb-stack-smooth-permanence).

Proof: step 3 uses the representable comparison in
lem-sfb-stack-smooth-presentation-criterion. Smoothness is stable under arbitrary
base change and fppf local on the target, as stated in section-smooth preceding
075U. Thus the smooth-chart condition is equivalent to the scheme-test condition:
every scheme base change is an algebraic space whose actual projection
(HasSpaceBaseChange) is smooth on all etale scheme charts (SpaceMapIsSmooth). -/
theorem smoothModuliMap_iff_representable (k : Type u) [Field k]
    {X : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))}
    {Y : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))}
    (hX : IsAlgebraicModuliStack X) (hY : IsAlgebraicModuliStack Y)
    (f : BasedFunctor X Y) (hf : IsRepresentableByAlgebraicSpaces f) :
    IsSmoothModuliMap f ↔
      ∀ (T : Over (Spec (.of k))) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Y),
        ∃ (Z : AlgebraicSpace (Spec (.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange f T t Z p ∧ SpaceMapIsSmooth Z T p := by
  sorry

end CategoryTheory
