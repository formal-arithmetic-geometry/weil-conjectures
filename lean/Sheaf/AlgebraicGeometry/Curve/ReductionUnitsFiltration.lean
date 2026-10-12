/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # A finite quasi-coherent filtration of infinitesimal units

Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-finite-filtration)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The reduction units kernel has a finite filtration with pulled-back additive
quasi-coherent quotients. This statement concerns sheaves, not their cohomology.
Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-finite-filtration)

Proof: Let N be the nilradical of X. Noetherianity and a finite affine cover give
N^m = 0 for some m >= 1. On an affine etale object V over X, flat pullback identifies
the reduction ideal with N O_V: its quotient is etale over the reduced scheme and
therefore reduced. The kernel of G_m,X -> i_* G_m,X_red is consequently 1+N.
Use the descending filtration 1+N^(j+1), ending at j=m-1. For j >= 0 the map
1+a to a identifies its quotient by 1+N^(j+2) with N^(j+1)/N^(j+2): the cross term
belongs to N^(2j+2), hence to N^(j+2). These are quasi-coherent modules. The map
is locally surjective since nilpotent elements give units, and flat pullback
preserves the ideal quotients. Lift the additive coefficients sectionwise to
AddCommGrpCat in universe u+1. Pull this finite filtration to X_red. Reduction
induces an exact equivalence of etale topoi. Its counit on G_m,X_red is an
isomorphism, so preservation of kernels identifies its first term with the
kernel of upperStarGmSheafToGmSheaf i. Exactness preserves each short exact
sequence and its last zero term. A reduced or empty X permits the zero-length
filtration, so no nonemptiness or positive dimension assumption is needed. -/
theorem exists_reduction_units_finite_filtration (X : Scheme.{u}) [IsNoetherian X] :
    ∃ (n : ℕ) (E : ℕ → Sheaf X.nilradical.subscheme.smallEtaleTopology
        AddCommGrpCat.{u + 1}),
      Nonempty (E 0 ≅ kernel (upperStarGmSheafToGmSheaf X.nilradical.subschemeι)) ∧
      IsZero (E n) ∧
      ∀ j, j < n → ∃ (F : X.Modules) (_ : F.IsQuasicoherent)
        (S : ShortComplex (Sheaf X.nilradical.subscheme.smallEtaleTopology
          AddCommGrpCat.{u + 1})),
        S.ShortExact ∧ Nonempty (S.X₁ ≅ E (j + 1)) ∧ Nonempty (S.X₂ ≅ E j) ∧
        Nonempty (S.X₃ ≅ (Etale.upperStar AddCommGrpCat.{u + 1} X.nilradical.subschemeι).obj
          ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
            (Modules.etaleTensorSectionsSheaf F))) := by sorry

end AlgebraicGeometry.Scheme
