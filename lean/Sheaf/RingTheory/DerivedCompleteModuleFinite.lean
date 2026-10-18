/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.RingTheory.DerivedCompleteModuleComplex
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
import Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.RingTheory.FiniteModuleComplete

/-!
# Finiteness of derived-complete modules with finite residue

Source: Stacks Project, More on Algebra, Tag 09BA (`lemma-derived-complete-finite`),
specialized to an `I`-adically complete Noetherian ring
(blueprint: lem-weil-derived-complete-module-finite).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace ModuleCat

/-- Over a complete Noetherian ring, a derived-complete module with finite reduction
modulo the ideal is finite, and its canonical map to its adic completion is bijective.
The completion consists of compatible residue classes, with componentwise operations.
Source: Stacks Project, More on Algebra, Tag 09BA (`lemma-derived-complete-finite`),
specialized to a complete ring (blueprint: lem-weil-derived-complete-module-finite).

Proof:
1. Products of modules are exact coordinatewise, using choice for surjectivity. By
   `lem-weil-derived-limit-existence`, products in `D(A)` are termwise products. The
   Roos triangle of `def-weil-derived-limit` for multiplication by `f` on `L[0]` has
   middle map `Δ_f((a_n)) = (a_n - f • a_(n+1))`. Its long exact cohomology sequence
   (`lem-sf-derived-homology-long-exact`) identifies the derived limit's cohomology
   with the kernel and cokernel of `Δ_f`. The cohomology criterion
   `lem-weil-pbc-unbounded-derived-iso-cohomology` therefore identifies derived
   completeness with bijectivity of `Δ_f` for every `f ∈ I`.
2. For a map between derived-complete modules, the product map intertwines both `Δ_f`
   and its inverse. Both preserve its image, so they descend to inverse maps on the
   product of the cokernel. Thus cokernels are derived complete.
3. Each finite free module `A^t` is complete by the ring-completeness hypothesis.
   For a sequence `b_n`, the residues of `sum_{j<k} f^j • b_(n+j)` define `a_n` with
   `a_n - f • a_(n+1) = b_n`. Separatedness proves uniqueness, so `A^t` is derived
   complete. This includes `t = 0`.
4. Lift finite generators of `M/IM` and form `q : A^t → M`. Step 2 makes its cokernel
   `C` derived complete, and residue generation gives `C = IC`.
5. Choose finite generators `f₁, ..., fᵣ` of `I` by Noetherianity, and successively
   quotient `C` by them. Each quotient is derived complete by step 2; the last is zero.
6. Descend through these quotients. If multiplication by `fⱼ` is surjective on the
   preceding quotient, any nonzero element lifts recursively to a nonzero sequence
   `a_n = fⱼ • a_(n+1)`, contradicting injectivity of `Δ_(fⱼ)`. Thus `C = 0`, also
   when `r = 0`. The map `q` is surjective, proving finite generation.
7. Apply `lem-weil-pbc-finite-module-complete-over-complete-noetherian` to this finite
   module over the complete Noetherian ring. Its completeness conclusion is precisely
   bijectivity of the canonical linear map `AdicCompletion.of I M`. -/
theorem finite_and_completion_bijective_of_isDerivedComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)] (I : Ideal A)
    (hA : Function.Bijective (AdicCompletion.of I A))
    (M : Type v) [AddCommGroup M] [Module A M]
    (hM : IsDerivedComplete I (ModuleCat.of A M))
    (hfinite : Module.Finite (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M))) :
    Module.Finite A M ∧ Function.Bijective (AdicCompletion.of I M) := by
  sorry

end ModuleCat
