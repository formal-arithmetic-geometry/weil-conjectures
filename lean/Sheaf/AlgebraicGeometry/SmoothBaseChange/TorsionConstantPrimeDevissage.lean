/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit

/-!
# Prime-coefficient vanishing for a constant bounded torsion group

Source: Stacks Project, Tag 0F08, cyclic-coefficient step; Tag 0739, colimits.
(blueprint: lem-sbc-torsion-constant-prime-devissage)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- A constant bounded torsion group has zero higher direct image if its relevant prime
cyclic coefficients do. A prime is irrelevant if multiplication by it is injective.

Source: Stacks Project, Tag 0F08, proof's cyclic-coefficient reduction; Tag 0739,
cohomology and filtered colimits. The finite primary decomposition is
`Submodule.torsionBy_isInternal` over the integers.
(blueprint: lem-sbc-torsion-constant-prime-devissage)

Proof:
1. Factor the nonzero annihilator n into its finitely many prime powers. Bezout
idempotents give the internal direct sum of the primary subgroups. If multiplication
by r is injective on M, repeated injectivity shows that its r-primary subgroup is zero.
2. Each other primary subgroup is the filtered union of its finitely generated
subgroups. Each such subgroup is finite: it is a quotient of a finite sum of copies
of Z/r^k for a common exponent k. The finite abelian group structure theorem expresses
it as a finite direct sum of cyclic groups Z/r^j. Every prime here divides n.
3. Constant sheafification is exact, using preservesFiniteLimits_constantSheaf and
preservesFiniteColimits_constantSheaf from ConstantSheafOver (no finite-ring hypothesis).
Apply it to
0 -> Z/r^(j-1) -> Z/r^j -> Z/r -> 0. In degree q the long exact higher-direct-image
sequence is exact at the middle term. If its two outer terms vanish, the middle term
vanishes. Starting with j = 0 (the zero group), induction therefore gives vanishing
for every cyclic prime power. Finite additivity gives vanishing for each finite subgroup.
4. The constant sheaf functor preserves colimits, and higher direct image along the
qcqs map h preserves filtered colimits. Thus the image of each primary subgroup is
zero, and finite additivity gives the result for M. In negative degrees all images of
sheaves vanish. If n = 1, M is zero directly; the primary sum is empty. -/
theorem isZero_higherDirectImage_constant_of_prime_vanishing
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h]
    (q : ℤ) (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    (n : ℕ) (hn : n ≠ 0) (hM : ∀ x : M, n • x = 0)
    (hprime : ∀ r : ℕ, r.Prime → r ∣ n →
      ¬ Function.Injective (fun x : M ↦ r • x) →
      IsZero (higherDirectImage (ULift.{u + 1} ℤ) h q
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj
          (ModuleCat.of (ULift.{u + 1} ℤ) (ULift.{u + 1} (ZMod r)))))) :
    IsZero (higherDirectImage (ULift.{u + 1} ℤ) h q
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj M)) := by
  sorry

end AlgebraicGeometry.Etale
