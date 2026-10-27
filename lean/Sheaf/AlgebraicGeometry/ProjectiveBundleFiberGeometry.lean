/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K9
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Flatness and structure-sheaf cohomology of canonical projective bundles

Source: Stacks Project, Constructions, Tags 01OB and 01OE; Morphisms,
standard polynomial charts; Cohomology of Schemes, projective-space computation.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

/-- The projection of a positive-rank vector bundle is flat and locally of finite
presentation. Its residue-field fibres are geometrically reduced and connected,
and their structure sheaves have vanishing first cohomology.

Source: Stacks Project, Constructions, Tags 01OB and 01OE, and Cohomology of
Schemes, the projective-space structure-sheaf cohomology computation.
(blueprint: lem-sfb-projective-bundle-fiber-geometry)

Proof: Choose a Zariski frame for E around each base point. The symmetric algebra
of the framed module is the polynomial algebra in r variables, with its usual
grading. Relative Proj and its base-open compatibility identify the restricted
projection with projective (r-1)-space over that open. Its standard homogeneous
charts are polynomial affine (r-1)-spaces. Polynomial algebras in finitely many
variables are flat and finitely presented over their coefficient ring; these
properties are local on source and target, so they hold for the projection.
Base change the frame at s to its residue field. This identifies the fibre over
kappa(s), as a scheme over that field, with projective (r-1)-space. The same
identification holds after every field extension. Its standard charts are
polynomial rings over a field, hence reduced and integral, and all charts have
nonempty pairwise intersections. The charts cover and are connected, so the
fibre is geometrically reduced and geometrically connected. Finally the standard
Cech complex for O on projective space is the degree-zero part of the homogeneous
localization complex. In positive degree its monomial summands are exact: the
only possible top-degree classes require all r exponents negative, impossible
in total degree zero. Thus H1(O)=0. When r=1 the projective space is the base
itself and its positive cohomology vanishes by affine acyclicity. Transport
along the fibre isomorphism, identifying the structure sheaves, gives the
stated abelian-sheaf H1. An empty base has no fibres to check.
-/
theorem projective_bundle_fiber_geometry (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 0 < r) :
    let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
    Flat p ∧ LocallyOfFinitePresentation p ∧
      ∀ s : S, GeometricallyReduced (p.fiberToSpecResidueField s) ∧
        GeometricallyConnected (p.fiberToSpecResidueField s) ∧
        Subsingleton (Sheaf.H (Scheme.structureSheafAb (p.fiber s)) 1) := by sorry

end AlgebraicGeometry.ProjectiveBundlePicardClassification
