/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion
import Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Paper.EtaleStandardCoverCech
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Affine quasi-coherent acyclicity with lifted coefficients

Source: Stacks Project, Tag 03P2, affine case
(blueprint: lem-sc-etale-affine-qcoherent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Affine acyclicity holds for the universe lift of the associated quasi-coherent sheaf.
Source: Stacks Project, Tag 03P2, affine case, and its Čech proof using Tag 03F9
(blueprint: lem-sc-etale-affine-qcoherent).

Proof: Use the affine basis of the small étale site. A covering of an affine admits a
finite affine refinement; its finite disjoint union is a faithfully flat affine cover.
The pullback module is quasi-coherent. On its iterated fibre products the associated
sheaf's Čech complex is the Amitsur complex of the section module, hence is exact in
positive degrees by faithfully flat descent. Applying `ULift` to each group and map
preserves this exactness: a lifted cocycle has an underlying cocycle, choose an
underlying preimage and lift it to obtain the required coboundary. The lifted Čech
complex therefore has zero positive cohomology. The affine basis is stable under
fibre products over an affine object, and finite affine covers refine every cover.
The Čech vanishing criterion now gives vanishing of sheaf cohomology at the terminal
affine object in every positive degree. This is the same proof as
`etale_affine_qcoherent`, with coefficients in the larger universe; no assertion
that universe lift preserves injective objects is required. -/
theorem etale_affine_qcoherent_ulift (X : Scheme.{u}) [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Scheme.Modules.etaleTensorSectionsSheaf F)) q) := by
  sorry

end AlgebraicGeometry.Etale
