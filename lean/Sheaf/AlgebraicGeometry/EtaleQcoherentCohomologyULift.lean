/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherent
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.AlgebraicGeometry.TensorPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # Coefficient universe comparison for quasi-coherent étale cohomology

Source: Stacks Project, Theorem 03P2 and Proposition 03DW (2), using a finite affine
open cover of a quasi-compact separated scheme.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Lifting the coefficients of an associated quasi-coherent étale sheaf does not
change its cohomology on a quasi-compact separated scheme.
Source: Stacks Project, Theorem 03P2, separated-case Čech argument, and Proposition
03DW (2). (blueprint: lem-sc-etale-qcoherent-cohomology-ulift)

Proof: Choose a finite affine open cover of X. Every finite intersection is affine
because X is separated. Pullback of F to each intersection is quasi-coherent.
The associated étale sheaf restricted to an intersection is its tensor-section
sheaf: pullback composition and the identity pullback identify its sections and
restrictions. The same identification after ULift holds sectionwise. Both sheaves
are acyclic on these affine intersections in positive degree: the usual affine
quasi-coherent acyclicity theorem applies to the small sheaf, and its lifted version
applies to the large sheaf. For the latter, the faithfully flat Amitsur proof lifts
cocycles and their preimages; it does not claim preservation of injective sheaves.
The Čech-to-sheaf spectral sequence for this cover therefore identifies each H^q
with the degree-q homology of its Čech section complex. The larger section complex
is the coefficient lift of the smaller one: in each degree the cover indices form
a finite set, and the finite product comparison commutes with all restriction maps
and hence with the alternating differential. Exactness of ULift identifies the
homology of this lifted complex with the lift of the smaller homology. Compose the
two Čech comparisons with this homology comparison and unlift to obtain the stated
additive equivalence. Degree zero uses the same sections identification. For empty
X, use the empty affine cover, whose section complex is zero; for F=0 both complexes
are zero. No dimension bound or smoothness is used. -/
theorem nonempty_etaleTensorSectionsSheaf_cohomology_ulift
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) :
    Nonempty (Sheaf.H
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (etaleTensorSectionsSheaf F)) q ≃+
      Sheaf.H (etaleTensorSectionsSheaf F) q) := by sorry

end AlgebraicGeometry.Scheme.Modules
