/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Sites.Pretopology

import Sheaf.Paper.ConstantCoefficientLisseTriangle
import Sheaf.Paper.ConstantCoefficientLisseRestriction
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.LocallyConstantTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # One step of the coefficient-ideal filtration

Source: Stacks Project, Cohomology on Sites, Tag 094I.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- The quotient triangle advances finite locally constant cohomology from J^n to
J^(n+1). Source: Stacks Project, Cohomology on Sites, Tag 094I
(blueprint: lem-weil-pbc-nilpotent-reduction-step).

Proof: put D = B/J^(n+1) and Q = J^n/J^(n+1). Regard the exact coefficient
sequence 0 to Q to D to B/J^n to 0 as a sequence of D-modules. A flat K-flat
representative of K tensors it to a distinguished triangle of D-module complexes.
Its middle term computes the reduction modulo J^(n+1); its last term is the
restriction of the reduction modulo J^n. Balancing identifies the first term with
the restriction to D of the tensor of the reduction modulo J and the finite
B/J-module Q. The ideal J annihilates Q; generators of the finite ideal J^n
project to generators over B/J. This quotient ring is Noetherian. The reduction
modulo J is bounded above, by a bounded-above flat
replacement of K. Tag 094H gives finite locally constant cohomology for this tensor.
The two quotient homomorphisms D to B/J and D to B/J^n are surjective, so the
scalar-restriction theorem preserves their finite constant local models. Restriction
is exact and hence commutes with cohomology. The
previous reduction supplies the other outer term. Since D is Noetherian, the
proved triangle-closure theorem over D gives the middle term's finite locally
constant cohomology over D itself. This avoids descending B-module local models
back to D-module local models. -/
theorem locallyConstantFiniteTypeModules_reduction_succ
    {C : Type u} [Category.{u} C] (T : Precoverage C)
    [T.HasIsos] [T.IsStableUnderComposition] [T.IsStableUnderBaseChange] [T.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B))]
    [∀ I : Ideal B, HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck (B ⧸ I)))]
    (K : DerivedCategory
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B)))
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (hmod : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck (Ideal.Quotient.mk J)).obj K)))
    (n : ℕ) (hn : 1 ≤ n)
    (hprevious : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J ^ n)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck
          (Ideal.Quotient.mk (J ^ n))).obj K))) :
    ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J ^ (n + 1))
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck
          (Ideal.Quotient.mk (J ^ (n + 1)))).obj K)) := by
  sorry

end SheafOfModules
