/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.ULift
import Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit
import Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.AlgebraicGeometry.EtaleInverseImageColimits
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.KilledSheafModuleLift
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Constructible approximation for one prime and one pullback -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Bijectivity on constructible prime-field module sheaves extends to every abelian sheaf
killed by the same prime, for a fixed morphism of qcqs schemes.
Source: Stacks Project, 03SA(3), 03Q5, and the first paragraph of the proof of 03SC
(blueprint: lem-pbc-q1-prime-constructible-pullback).

Proof: Give the abelian sheaf G its canonical Z/r-module structure, and transport it to
ULift (ZMod r) coefficients. Restrictions are linear because additive maps commute with
integer and residue-class scalar multiplication. The underlying abelian sheaf is G.
By 03SA(3), this module sheaf has a filtered colimit presentation by constructible module
sheaves over the finite ring ULift (ZMod r). These are constructible in the original
Scheme.IsConstructibleSheaf convention: finite module values and finite-generation stalks
agree over this finite ring, with the same locally closed strata and trivializing covers.
Forgetting the module structure preserves this colimit. Inverse image preserves it as a
left adjoint. Cohomology on each qcqs scheme commutes with filtered colimits by 03Q5;
the natural Ext-to-derived comparison gives the same assertion for Sheaf.H. Naturality
of cohomologyMap makes the comparison on the colimit the colimit of the stagewise
comparison maps. The hypothesis makes each stage map bijective. Its inverse is compatible
with the transitions by cancelling the naturality squares, so the induced colimit map is
bijective. This gives the required comparison on G, including degree zero, the zero sheaf,
and empty schemes. No curve, properness, field-extension square or reducedness is assumed. -/
theorem bijective_cohomologyMap_of_constructible_prime
    {X Y : Scheme.{u}} (a : Y ⟶ X)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (r : ℕ) [Fact r.Prime]
    (H : ∀ (M : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Scheme.IsConstructibleSheaf M],
      ∀ q : ℕ, Function.Bijective (cohomologyMap a
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
          AddCommGrpCat.{u + 1})).obj M) q))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : r • 𝟙 G = 0) (q : ℕ) :
    Function.Bijective (cohomologyMap a G q) := by sorry

end AlgebraicGeometry.Etale
