/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.IntegralSpaceFinitePresentationLimit
import Sheaf.AlgebraicGeometry.SpaceLimitSchematicStage

/-! # Finite finitely presented scheme covers of qcqs algebraic spaces

Source: Stacks Project, Limits of Spaces, Tag 09YC(1),
`proposition-there-is-a-scheme-finite-over`
(blueprint: lem-sfb-qcqs-space-finite-scheme-cover).

The base scheme is arbitrary. Quasi-separatedness is absolute, and the covering map
is surjective on field-valued point classes. Finite presentation retains all three
conditions: quasi-compactness, quasi-separatedness and local finite presentation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every quasi-compact, absolutely quasi-separated algebraic space over an arbitrary
scheme admits a finite, finitely presented, point-surjective cover by a scheme.

Source: Stacks Project, Limits of Spaces, Tag 09YC(1),
`proposition-there-is-a-scheme-finite-over`
(blueprint: lem-sfb-qcqs-space-finite-scheme-cover).

Proof:
1. The quasi-compact scheme atlas implies compactness of the point space, by
   `points_compactSpace_iff` (lem-a1-space-etale-open-image). Absolute
   quasi-separatedness is the affine-pair criterion of Tag 0AHR. The affine-test
   diagonal criterion extends to all scheme tests by covering each quasi-compact
   open of a test scheme by finitely many affine opens and taking the finite union
   of their quasi-compact inverse images.
2. Apply lem-sfb-qcqs-space-integral-scheme-cover to obtain a scheme Z and a
   point-surjective integral map q : Z → X. No separatedness or Noetherian
   hypothesis is used.
3. Apply `exists_finite_finitePresentation_limit_of_integral`
   (lem-sfb-integral-space-finite-presentation-limit) to express Z as a small
   nonempty directed limit over X of qcqs spaces Z_i finite and finitely presented
   over X, with affine transitions. This is also a limit over S: any compatible
   family of S-maps has a common composite to X by directedness, and its unique
   lift over X is the required unique lift over S. Nonemptiness supplies an index
   at which to check the composite to X.
4. Since Z is a scheme, `exists_scheme_stage_of_isLimit`
   (lem-sfb-affine-space-limit-schematic-stage) gives a schematic stage Z_i. Choose
   its representing S-scheme Y and transport the structure map to schemeSpace Y.
   It is finite and finitely presented. For a point class x of X, choose a
   field-valued representative above x in Z, using surjectivity of q. Composing
   it with Z → Z_i gives a point above x in Y. The factorization through Z_i
   proves point-surjectivity of Y → X; the projection Z → Z_i need not itself
   be surjective. -/
theorem exists_finite_finitePresentation_scheme_cover {S : Scheme.{u}}
    (X : AlgebraicSpace S) (hqc : IsQuasiCompact X.obj)
    (hqs : IsAbsolutelyQuasiSeparated X) :
    ∃ (Y : Over S) (p : schemeSpace Y ⟶ X),
      pointImage p.hom.hom = Set.univ ∧
      IsRepresentableWith (fun _ _ f ↦ IsFinite f.left) p.hom.hom ∧
      MapIsQuasiCompact p.hom.hom ∧
      MapIsQuasiSeparated p.hom.hom ∧
      MapIsLocallyOfFinitePresentation p := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
