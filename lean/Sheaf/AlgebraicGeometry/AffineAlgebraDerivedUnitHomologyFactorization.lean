/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Cohomology of the affine algebra derived unit

Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof.
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

/-- Under the cohomology comparison, the derived affine algebra unit is the
underived unit applied to the cohomology module.
Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof.
(blueprint: lem-sc-affine-algebra-derived-unit-homology-factorization).

Proof: First take the tensor-derived adjunction of
RingedSpace.derivedModulePullback_adjunction. The flat stalk localizations of g
make its underived tensor pullback exact. Applying an exact functor to kernels
and images gives a natural identification H^n(Lg-star M) with g-star H^n(M).
The latter is quasi-coherent by the affine module correspondence, so Lg-star M
has quasi-coherent cohomology. Exact scalar restriction to O_Y compares Rg-star
with Rf-star: both use the same K-injective resolution and underlying pushed
complex. The affine unbounded cohomology formula, justified by affine vanishing
and the unbounded cohomological bound, identifies H^n(Rg-star Lg-star M) with
 g_* g^* H^n(M). This comparison is natural and compatible with the derived unit:
on a representative and its resolution the unit is induced by the underived
adjunction, and the comparison sends it to the ordinary unit on cohomology.
One may check this on affine opens, where the map sends a module section to
its tensor with 1. These maps agree on restrictions and hence on sheaves.
Uniqueness of left adjoints transports the comparison from tensor pullback to P
and from its derived left adjoint to L, with the adjunction-compatible natural
isomorphisms. Absorb their cohomology components in the target isomorphism e.
This gives the stated equality for a and adj even when these are not the chosen
canonical adjunctions. The argument uses all integer degrees and does not assume
boundedness. Identity morphisms, empty schemes and zero cohomology give the
identity between the respective objects, including the zero objects. -/
theorem affine_algebra_derived_unit_homology_factorization
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    [Limits.PreservesFiniteLimits P]
    (L : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) ⥤
      schemeDerivedCategory X)
    (adj : L ⊣ RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f))
    (M : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))))
    (hM : directImageAlgebraDerivedQCohProperty f M) (n : ℤ) :
    ∃ e : (DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n).obj
          ((RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)).obj
            (L.obj M)) ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj
          (P.obj ((DerivedCategory.homologyFunctor
            (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n).obj M)),
      (DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n).map
          (adj.unit.app M) ≫ e.hom =
        a.unit.app ((DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n).obj M) := by sorry

end AlgebraicGeometry
