/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalSectionCone
public import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.Locally.LocallyConstantTorsionLocalAcyclicity
import WeilConjectures.AlgebraicGeometry.Proper.ProperLocallyAcyclicSpecialization
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothLocalAcyclicity

/-!
# Prime-to-characteristic specialization for smooth proper morphisms

Source: Stacks Project, Tag 0GKD, lemma-sp-isom-proper-loc-cst-torsion.
(blueprint: lem-weil-pbc-smooth-proper-specialization-prime-to-characteristic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
