/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.FibredGroupoidLimitPreserving
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Testing surjectivity of representable morphisms on finite presentation affines

Source: Stacks Project, Criteria for Representability, Tag 07WI,
lemma-check-property-limit-preserving, specialized to surjectivity
(blueprint: lem-sfb-limit-test-surjective-representable).
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- Surjectivity of a representable morphism of fibred groupoids can be tested on
all affine schemes locally of finite presentation over the base, provided that target
objects descend along directed affine limits. Surjectivity is on field-valued point
classes, expanded as lifting after a field extension. A based functor from `h_T` is
an object of the target fibre by the fibred Yoneda equivalence.

Source: Stacks Project, Criteria for Representability, Tag 07WI,
lemma-check-property-limit-preserving
(blueprint: lem-sfb-limit-test-surjective-representable).

Proof:
1. For a base map and an isomorphism between the pulled-back target object and another
object, identify the two base changes by composing the isomorphism in their defining
triples. This gives an isomorphism over the new test scheme, using
[def-trf-algebraic-space] and [lem-trf-space-fibre-products-etale-covers].
2. For an affine test scheme mapping into an affine open `Spec R` of the base, present
its ring as the directed colimit of the finitely presented `R`-algebras indexed by finite
sets of elements and finite sets of polynomial relations. The empty pair is an index,
and unions give upper bounds. Compatible maps out of these stages define the unique
map on every element; stages containing addition, multiplication, unit and scalar
relations verify that it is an algebra map [def-weil-pbc-category-colimit].
3. This is also a colimit of rings: compatibility and directedness make the composites
from `R` equal, so each compatible ring cocone has a single `R`-algebra structure.
4. Apply [lem-weil-pbc-spec-colimit-limit] to obtain the inverse limit of the spectra
with their actual projections, also over `S`. Every stage is locally of finite
presentation over `S` by its chart over `Spec R`
[def-sbc-locally-finite-presentation]. No compactness condition on `S` is needed.
5. Descend the given target object to one stage using `ObjectsDescend G`. The test
hypothesis makes that stage's representing space surjective. Step 1 identifies the
original representing space with its pullback. No arrow-descent hypothesis is used.
6. Lift a field-valued point through the stage space after a field extension. Combining
it with the original point gives a point in the pullback; common field extensions
express equality of point classes [lem-trf-space-fibre-products-etale-covers].
7. For arbitrary `T`, choose an affine open of `S` around the image of a given point,
then an affine open of `T` inside its inverse image
[lem-weil-pbc-affine-opens-basis]. A field-valued point factors through this open
[def-weil-open-immersion]. Apply steps 2--6 to the restricted object, and step 1 to
map its lift to the original space. If `T` is empty there are no points to lift. -/
theorem surjective_of_affine_locallyOfFinitePresentation_tests {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (f : BasedFunctor F G) (hf : IsRepresentableByAlgebraicSpaces f)
    (hLimits : FibredGroupoidLimit.ObjectsDescend G)
    (hTests : ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
      IsAffine T.left → LocallyOfFinitePresentation T.hom →
        ∀ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange f T t Z p →
            AlgebraicSpace.IsJointlySurjective (fun _ : Unit ↦ p)) :
    ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G)
      (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange f T t Z p →
        AlgebraicSpace.IsJointlySurjective (fun _ : Unit ↦ p) := by
  sorry

end CategoryTheory
