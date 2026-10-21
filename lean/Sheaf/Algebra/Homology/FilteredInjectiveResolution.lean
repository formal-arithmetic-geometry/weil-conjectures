/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredLocalization
import Sheaf.CategoryTheory.EnoughStrictFilteredInjectives
import Sheaf.Paper.FiniteFilteredGradedExactness
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-! # Bounded-below filtered-injective resolutions

Source: Stacks Project, Derived Categories, Tag 05TW
(blueprint: lem-trf-filtered-injective-resolution).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable (C : Type u) [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- Every bounded-below finite filtered complex has a filtered-injective resolution.
Source: Stacks Project, Derived Categories, Tag 05TW; the fixed interval refinement
uses the same-interval embeddings of Tag 05TS.

Proof: shift the cochain lower bound to zero. Resolve each kernel and coimage of a
source differential by successive strict embeddings into filtered injectives and
quotients, using the enough-strict-injectives theorem. Lift the coimage-to-next-kernel
maps between those resolutions by filtered injectivity. For each strict sequence
kernel-to-term-to-coimage use the horseshoe construction: its off-diagonal maps are
chosen inductively so that the square of the differential is zero. The horizontal
map is the composite of horseshoe projection, lifted map, and next inclusion; two
successive horizontal maps compose to zero. Totalize this first-quadrant double
complex. Its diagonals are finite sums, so its terms have injective graded pieces.
After each graded functor, the first-quadrant column augmentation theorem gives a
quasi-isomorphism from the original complex. Shift back. All kernels, quotients,
embeddings and finite sums retain prescribed filtration bounds. If b < a, the
bounds force every object to be zero, so the identity resolution suffices.
(blueprint: lem-trf-filtered-injective-resolution). -/
theorem filteredInjectiveResolution (B : Option (ℤ × ℤ))
    (K : CochainComplex.Plus (FiniteFilteredObjects C B false)) :
    ∃ (I : CochainComplex.Plus (FiniteFilteredObjects C B true))
      (f : K ⟶ (filteredInjectiveInclusion C B).mapCochainComplexPlus.obj I),
      finiteFilteredQuasiIso C B
        ((HomotopyCategory.Plus.quotient (FiniteFilteredObjects C B false)).map f) := by
  sorry

end CategoryTheory
