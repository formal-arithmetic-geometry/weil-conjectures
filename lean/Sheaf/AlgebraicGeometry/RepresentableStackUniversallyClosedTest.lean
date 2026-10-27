/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.StackPointTopology
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts

/-! # Scheme tests for universal closedness of representable stack morphisms

Source: Stacks Project, stacks-morphisms.tex, Tags 0512 and 0CL3;
spaces-morphisms.tex, definition-closed and Tag 03XD
(blueprint: lem-sfb-representable-stack-universally-closed-test).

The three statements give the stack/scheme-test equivalence and its two comparisons with
ordinary universal closedness of algebraic spaces. All point maps and topologies are the
existing field-object quotients with their smooth-atlas or etale-atlas topologies.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ v₃ w₁ w₂ w₃

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A representable map of DM stacks is closed after all algebraic-stack base changes
exactly when every scheme base change is universally closed as an algebraic-space map.
Universal closedness on the right is expanded into all algebraic-space base changes.
`HasSpaceBaseChange` pins the presentation to the actual projection over the test scheme;
representability guarantees such presentations exist, and every presentation is tested.
Source: Stacks Project, Tags 0512 and 0CL3
(blueprint: lem-sfb-representable-stack-universally-closed-test).

Proof, following the node's steps 1--4:
1. Algebraic spaces are algebraic stacks: their etale atlases are smooth by
lem-sfb-stack-chartwise-smooth-etale-calculus. Apply the stack test to W over T.
The triple-category equivalence W ×_T (T ×_G F) ≃ W ×_G F preserves projection to W;
lem-trf-space-fibre-products-etale-covers gives the space fibre products, and
lem-sfb-stack-point-topology turns this equivalence into a homeomorphism. This proves
universal closedness of each scheme-base-change presentation.
2. Conversely take an arbitrary algebraic stack Z over G and a smooth surjective atlas
V → Z. DM stacks are algebraic by the same smooth/etale calculus, and P = Z ×_G F is
algebraic by lem-sfb-algebraic-stack-fibre-products. Set E = V ×_G F. Its projection
E → V is closed by the hypothesis and its identity space base change. The canonical
triple equivalence V ×_Z P ≃ E preserves projections: send (v,(z,x,alpha),beta)
to (v,x,alpha composed with the image of beta); its inverse inserts z = v and beta = id.
This is functorial on arrows and commutes with pullback.
3. Equal images of field-point classes become isomorphic over a common field extension.
The resulting pair and its isomorphism define a point of E. Thus the point map
|E| → |V| ×_|Z| |P| is onto, without claiming it is a bijection. Writing r:|E| → |P|,
g:|E| → |V|, q:|V| → |Z| and h:|P| → |Z| gives q⁻¹(h(B)) = g(r⁻¹(B)) for every B.
4. For closed B, continuity of r makes r⁻¹(B) closed; closedness of g makes its image
closed. The smooth-atlas quotient criterion of lem-sfb-stack-point-topology then makes
h(B) closed. This proves closedness after every algebraic-stack base change. -/
theorem representable_stack_universally_closed_test {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsDeligneMumfordModuliStack F) (hG : IsDeligneMumfordModuliStack G)
    (f : BasedFunctor F G) (hf : IsRepresentableByAlgebraicSpaces f) :
    (∀ (Z : BasedCategory.{max u v₁ v₂ v₃, max (u + 1) w₁ w₂ w₃} (Over S)),
      IsAlgebraicModuliStack Z → ∀ z : BasedFunctor Z G,
        IsClosedMap (moduliPointMap (moduliTwoFiberFst z f))) ↔
    (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G)
        (E : AlgebraicSpace S) (a : E.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange f T t E a →
        ∀ (W : AlgebraicSpace S) (b : W.obj.obj ⟶ yoneda.obj T),
          IsClosedMap (AlgebraicSpace.mapPoint (pullback.snd a b))) := by
  sorry

/-- For algebraic spaces the all-stack-base-change condition is ordinary universal
closedness, using the usual etale-atlas topology of the field-point classes.
Source: Stacks Project, Tag 0512 and spaces-morphisms.tex, definition-closed
(blueprint: lem-sfb-representable-stack-universally-closed-test).

Proof (node step 5): restrict the stack tests to discrete groupoids of algebraic spaces.
Their 2-fibre products are ordinary sheaf fibre products, because their comparison
isomorphisms are equalities. The identifications preserve the projection and the point
topologies by lem-sfb-stack-point-topology. Conversely ordinary universal closedness
gives the scheme-test condition: W ×_T (T ×_Y X) is canonically W ×_Y X over W.
Apply representable_stack_universally_closed_test to recover all stack tests. -/
theorem space_stack_universally_closed_iff {S : Scheme.{u}}
    (X Y : AlgebraicSpace S) (f : X ⟶ Y) :
    (∀ (Z : BasedCategory.{max u v₃, max (u + 1) w₃} (Over S)),
      IsAlgebraicModuliStack Z →
        ∀ z : BasedFunctor Z (discreteModuli Y.obj.obj),
          IsClosedMap (moduliPointMap
            (moduliTwoFiberFst z (discreteModuliMap f.hom.hom)))) ↔
    (∀ (W : AlgebraicSpace S) (b : W ⟶ Y),
      IsClosedMap (AlgebraicSpace.mapPoint (pullback.snd f.hom.hom b.hom.hom))) := by
  sorry

/-- For algebraic spaces the scheme-base-change condition is also ordinary universal
closedness, including every algebraic-space base change of each test projection.
Source: Stacks Project, Tag 0512 and spaces-morphisms.tex, definition-closed
(blueprint: lem-sfb-representable-stack-universally-closed-test).

Proof (node step 5): universal closedness of X → Y makes every projection
W ×_T (T ×_Y X) → W closed through its canonical identification with W ×_Y X → W.
Every presentation in HasSpaceBaseChange is equivalent over T to this one and therefore
has the same point-map closedness by lem-sfb-stack-point-topology. In the reverse
direction the first theorem gives the all-stack test; restrict to algebraic spaces as
in space_stack_universally_closed_iff. The fibre products are algebraic spaces by
lem-trf-space-fibre-products-etale-covers. -/
theorem space_scheme_tests_universally_closed_iff {S : Scheme.{u}}
    (X Y : AlgebraicSpace S) (f : X ⟶ Y) :
    (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) (discreteModuli Y.obj.obj))
        (E : AlgebraicSpace S) (a : E.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange (discreteModuliMap f.hom.hom) T t E a →
        ∀ (W : AlgebraicSpace S) (b : W.obj.obj ⟶ yoneda.obj T),
          IsClosedMap (AlgebraicSpace.mapPoint (pullback.snd a b))) ↔
    (∀ (W : AlgebraicSpace S) (b : W ⟶ Y),
      IsClosedMap (AlgebraicSpace.mapPoint (pullback.snd f.hom.hom b.hom.hom))) := by
  sorry

end CategoryTheory
