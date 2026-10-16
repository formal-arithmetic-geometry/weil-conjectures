/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.Paper.CondensedQbarCoefficientConstruction
import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
import Sheaf.Paper.ProfinitePointPullback

/-! # Compatibility of bounded coefficient constructions
Source: RefactorInstruction, Section 4, coefficient realization and geometric fibers.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Bounded scalar multiplication commutes with arbitrary scheme inverse image.

Source: RefactorInstruction, Section 4, finite-matrix refinement, coefficient
realization and geometric-fiber comparison, steps 1--3
(blueprint: lem-weil-pbc-condensed-qbar-scalar-pullback).

Proof in words: base change of small pro-etale objects sends a bounded function to
its composite with the first projection. This defines a morphism from the bounded
presheaf on Y to the direct image of the bounded presheaf on Z. Compose with the
sheafification unit and use the sheafification adjunction to obtain the corresponding
morphism of abelian sheaves. Its adjoint is a ring morphism from the inverse image
of the bounded coefficient sheaf on Y to the bounded coefficient sheaf on Z.
The square with the two globalCoefficientIso maps and condensedPullbackHom commutes:
under the point adjunction, evaluate both sides on a profinite test space S and a
bounded function on S. The normalization globalCoefficientIso_test identifies both
with that function pulled back through Z[S] to S. The canonical base-change
isomorphism Y[S] times_Y Z = Z[S] makes these projections equal. Equality follows
from the adjunction bijection and extensionality on profinite spaces and sections.
Multiplication by a pulls back to multiplication by a composed with g, as is checked
on bounded presheaf sections using associativity of function composition.
Naturality of the monoidal sheafification unit transports this equation to the
bounded sheaves. Conjugate the commuting square by the global coefficient
isomorphisms. Naturality of extendScalarsIsoComapInv cancels its two components;
the remaining regular-module comparisons have underlying maps alpha and alpha^-1,
where alpha is condensedPullbackHom. This is precisely the asserted equality.
The finite-extension bound survives every precomposition. If Z is empty both
endomorphisms are the unique endomorphism of the zero coefficient object.
-/
theorem condensedQbar_scalar_pullback (ℓ : ℕ) [Fact ℓ.Prime]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y) :
    (condensedQbarRegularPullbackIso ℓ g).inv ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).map
        (condensedQbarScalar ℓ Y a) ≫ (condensedQbarRegularPullbackIso ℓ g).hom =
      condensedQbarScalar ℓ Z
        (CondensedQbarScalarConstruction.boundedComp ℓ g.base.hom a) := by sorry

end AlgebraicGeometry.ProEtale
