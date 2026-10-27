/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData

/-!
# Ordered relative-Proj comparison on polynomial charts

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
(blueprint: lem-trf-symmetric-proj-ordered-relative-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.Modules.boundaryPullbackComparison

/-- An ordered free presentation identifies the canonical symmetric relative Proj with
relative projective space, including its affine polynomial and degree-one twist models.
This assertion does not involve a global tautological quotient or standard projective space.

Source: Stacks Project, Constructions, Tags 01OE (lemma-projective-space-bundle),
01OB (definition-projective-bundle), and 01MS (lemma-when-invertible).
(blueprint: lem-trf-symmetric-proj-ordered-relative-comparison).

Proof: On an affine V, apply the symmetric-algebra universal property to the section
isomorphism induced by b and the standard ordered basis of the free sheaf. The resulting
polynomial isomorphism beta fixes coefficients and sends X_i to iota(b(e_i)). Its inverse
sends a vector to its coordinate linear polynomial. Products of n generators span the
nth symmetric degree, so both maps preserve degree. Naturality of b and of the basis
inclusions shows that these isomorphisms commute with restriction on scalars and vectors.
The defining affinePolynomialEquiv for relative projective space gives gamma, after
reindexing the variables by ULift.down. Compose beta with gamma inverse to identify the
two affine graded algebras, and glue by relative-Proj functoriality. This constructs eRel
over S. On every affine, Proj functoriality gives eC and eR, with exactly the displayed
chart equation in AffineFreeComparison. Surjectivity of beta and gamma supplies their
irrelevant-ideal conditions. On D_+(X_i), the degree-one twists are free with frames X_i
and beta(X_i). Map these frames to one another. On intersections the transition units
are X_i/X_j and beta(X_i)/beta(X_j), hence the maps and their inverses glue. For an
arbitrary degree-one polynomial s, the local formula s/X_i times the frame shows that
its pulled section maps to beta(s)/1. This is the unitToTwist equation, with the unit
pullback comparison. The standard opens cover since the variables generate the
irrelevant ideal. All formulas hold for r=0, the zero coefficient ring, and empty charts;
no variable is cancelled in the original ring. -/
theorem exists_ordered_relative_comparison (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E) :
    ∃ eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
        RelativeProjectiveSpace.scheme S r,
      eRel.hom ≫ RelativeProjectiveSpace.π S r =
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ∧
      ∀ V : S.affineOpens, ProjectiveBundleQuotientGeometry.AffineFreeComparison r b eRel V :=
  by sorry

end AlgebraicGeometry.SymmetricProjTautologicalCharts
