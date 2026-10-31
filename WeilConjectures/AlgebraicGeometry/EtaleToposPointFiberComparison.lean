/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Sites.GrothendieckTopos

/-!
# Fiber-functor reconstruction for an étale topos point

This is the support and finite-fiber part of the classification of points of the
small étale topos.  The subsequent stalk reconstruction uses the comparison of
the two fiber functors.
(blueprint: lem-trf-etale-topos-point-fiber-comparison)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The set-valued functor on étale objects obtained by applying the inverse image
of a geometric morphism to sheafified representables.
(blueprint: lem-trf-etale-topos-point-fiber-comparison) -/
noncomputable def etalePointFiberFunctor (S : Scheme.{u})
    (p : GeometricMorphism (Type (u + 1))
      (Sheaf S.smallEtaleTopology (Type (u + 1)))) : S.Etale ⥤ Type (u + 1) :=
  uliftYoneda.{u + 1} ⋙
    presheafToSheaf S.smallEtaleTopology (Type (u + 1)) ⋙ p.inverse

/-- The support construction and a coherent choice on pointed neighborhoods give
a natural comparison from geometric lifts to the point's fiber functor. This
statement asserts no injectivity or surjectivity of the comparison.
Source: Stacks Project, Etale Cohomology, Tag 04HU.
(blueprint: lem-trf-etale-topos-point-fiber-comparison)

Proof: the representable/sheafification/inverse-image composite preserves finite
limits and takes covering families to jointly surjective families. On open
subschemes its values are subterminal. The union W of opens with empty value
has empty value by its open cover; its complement is nonempty and irreducible
by preservation of intersections. Sobriety gives its generic point x. An open
has nonempty value exactly when it contains x. An étale object's image is open
and the object covers its image, giving the stated support equivalence.

Choose an affine open A containing x and the algebraic closure Ω of κ(x).
Its residue-field morphism gives s over x. For an affine étale A-object U, use
the affine splitting neighborhood V: U × V is a finite disjoint union of V's
and a remainder with no point over x. The remainder has empty value; V has
nonempty value. Taking a fiber over an element of its value proves that the
value of U is finite. Values on pointed affine neighborhoods over A are also
nonempty. A small skeleton of these neighborhoods is cofiltered, so the
cofiltered finite nonempty sets theorem supplies compatible elements.

Extend to every pointed neighborhood by an affine refinement over A. Common
pointed refinements, followed by affine refinement, show independence of this
choice and compatibility with every pointed arrow. For each lift t into U,
take the compatible element at (U,t). Compatibility is precisely naturality
of the comparison. Apply ULift.up/down to express these sets in Type (u+1).
The empty scheme admits no such geometric morphism, since terminal and empty
cover values would coincide; empty fibers cause no exception. -/
theorem exists_etale_point_comparison (S : Scheme.{u})
    (p : GeometricMorphism (Type (u + 1))
      (Sheaf S.smallEtaleTopology (Type (u + 1)))) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (s : Spec (.of Ω) ⟶ S),
      ∃ c : ((pointSmallEtale s).fiber ⋙ uliftFunctor.{u + 1}) ⟶
          etalePointFiberFunctor S p,
        ∀ U : S.Etale,
          Nonempty ((etalePointFiberFunctor S p).obj U) ↔ s default ∈ Set.range U.hom := by
  sorry

end AlgebraicGeometry.Scheme
