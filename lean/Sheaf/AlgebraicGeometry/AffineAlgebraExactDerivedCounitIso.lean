/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Sheaf.AlgebraicGeometry.AffineAlgebraModuleAdjunctionIsos
import Sheaf.AlgebraicGeometry.AffineDerivedCohomology
import Sheaf.AlgebraicGeometry.AffineModuleCorrespondence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The canonical exact-derived affine algebra counit

Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof.
(blueprint: lem-sc-affine-algebra-exact-derived-counit-iso).
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

/-- The counit of the canonical derived adjunction of an exact affine algebra pullback
is invertible on complexes with quasi-coherent cohomology.
Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof;
Tag 079W, cohomology-lemma-adjoint, for the derived counit construction.
(blueprint: lem-sc-affine-algebra-exact-derived-counit-iso).

Proof: Put g : (X,O_X) -> (Y,f_*O_X). Exact restriction of algebra scalars to O_Y
identifies Rg_* followed by restriction with Rf_*. It uses the same K-injective
resolution and the identity g_* followed by restriction = f_*. On each affine open,
the unbounded affine cohomology calculation (0AVW, using the bound of 08D4)
identifies H^i(Rg_*K) with g_*H^i(K), with its f_*O_X action. These identifications
are natural in K and in open restrictions. Exact P commutes with cohomology, so
H^i(P.mapDerivedCategory(Rg_*K)) identifies with P(g_*H^i(K)).
The canonical derived adjunction is constructed from the termwise adjunction and
the right-derived comparison. Its counit equation (Adjunction.derived_counit,
or derivedε_fac_app) identifies its cohomology map with the ordinary counit under
these comparisons: represent K by its K-injective resolution, where the
right-derived comparison is invertible, and apply the termwise counit equation.
The kernel and image maps giving the homology comparisons commute with that
counit. On affine opens this is evaluation, sending a pure tensor b tensor s to
b*s. The ordinary affine module correspondence makes this evaluation invertible
for H^i(K), which is quasi-coherent. Thus the canonical derived counit induces
an isomorphism in every degree, and the derived homology criterion makes it an
isomorphism. An arbitrary underived adjunction a is transported from tensor
pullback by uniqueness of left adjoints; functoriality of the canonical derived
adjunction transports its counit, preserving invertibility. The argument uses
all integer degrees and includes empty schemes and zero cohomology. It does not
use any derived unit isomorphism or unit homology factorization. -/
theorem affine_algebra_exact_derived_counit_isIso
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K) :
    IsIso ((a.mapDerivedCategoryRightDerivedAdjunction).counit.app K) := by sorry

end AlgebraicGeometry
