/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
/-!
# Canonical single-complex shift comparisons

These comparisons isolate the source and unit transport calculations used by
`rightDerivedFunctorPlusUnit_canonical_single_shift`.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Single-object homology comparisons commute with shift transport to degree zero.

Source: the single-functor shift and homology shift constructions in Mathlib,
`Algebra/Homology/HomotopyCategory/SingleFunctors.lean` and
`Algebra/Homology/HomotopyCategory/ShiftSequence.lean`.
(blueprint: lem-pc-single-homology-shift-comparison)

Proof: Lift the single-functor shift to the bounded-below derived category through
its fully faithful inclusion. The induced homology shift sequence transports the
result back to the homotopy category and then to cochain complexes, by the quotient
homology comparisons. Naturality cancels these quotient comparisons. In cochain
complexes, homology of the inverse single shift followed by the homology shift is
induced by a morphism of short complexes whose middle component is the identity
on Y. Compose with the epimorphic cycles-to-homology projection: naturality of
homologyπ and cyclesMap_i identifies both sides with iCycles followed by
singleObjXSelf.hom. The outer terms of the short complexes are zero, so the signs
in the shift act only on zero morphisms. Cancelling the homology projection proves
the identity. At n=0, the shift unit comparisons cancel; the same argument also
applies to a zero object. -/
theorem singleFunctor_homology_shift_comparison (Y : C) (n : ℤ) :
    let H₀ := DerivedCategory.Plus.homologyFunctor C 0
    let d := Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by simp)).symm
      (H₀.shift n) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
        (H₀.shiftIso (-n) n 0 (by ring))
    d.hom.app Y ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).hom.app Y =
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).hom.app Y := by
  sorry
