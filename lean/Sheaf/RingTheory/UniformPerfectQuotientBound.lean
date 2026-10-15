/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalProperties.Projective
import Sheaf.RingTheory.Depth
import Sheaf.RingTheory.AuslanderBuchsbaum
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Sheaf.RingTheory.ProjectiveResolutionExtCharacterization
import Sheaf.RingTheory.ProjectiveResolutionKernelProjective
import Sheaf.RingTheory.FiniteProjectiveDimensionOfTorBound

/-!
# A uniform finite projective resolution bound for perfect ideal-power quotients

Source: Stacks Project, Algebra, Tag 090V (proposition-Auslander-Buchsbaum), assembled with
Tags 00O5 and 065R and the local-global projective-dimension criterion
(blueprint: lem-weil-pbc-uniform-perfect-quotient-bound).

Homological degree `i` of a projective resolution corresponds to cochain degree `-i`.
Thus vanishing above `r` means cochain support in `[-r, 0]`. The derived tensor with a module
is computed by tensoring this resolution; its degree `-i` cohomology is `Tor'` in degree `i`.
It has no positive cochain terms. No nonzero-quotient assumption is made.

## Main statements

- `ModuleCat.exists_uniform_finite_projective_resolution_quotient_pow`: one common resolution
  length and Tor bound for every positive ideal power.
- `ModuleCat.uniform_finite_projective_resolution_quotient_pow_iff_tor_vanishing`: equivalence
  of the two uniform bounds for the same prescribed integer.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Finite perfect ideal-power quotients have one common finite-projective resolution bound.
Source: Stacks Project, Algebra, Tag 090V and the assembly recorded in
(blueprint: lem-weil-pbc-uniform-perfect-quotient-bound).

Proof:
1. Use `def-pc-perfect-ring-complex` to choose a bounded finite projective model for each
quotient. Split off the positive tail: the last differential is surjective onto a projective
module, hence splits; delete the resulting contractible summand. The remaining augmented
nonpositive complex is a finite projective resolution. Let `r` be its length for `A / I`.
If `I` is the unit ideal use zero resolutions and `r = 0`.
2. Localize at a maximal ideal. Noetherianity, finite generation, projectivity and exactness
survive localization (`lem-weil-pbc-localization-module-exact` and
`lem-weil-pbc-localization-projective`). If the ideal does not contain `I`, all the localized
quotients are zero. Otherwise all are nonzero cyclic modules of finite projective dimension.
3. The localization of `A / I` has depth zero: for each maximal-ideal element, finiteness of
`A / I` gives two equal powers; their difference factors as a power times a unit. Hence the
element acts nilpotently and cannot be injective on this nonzero module. No regular sequence
can start with it (`def-weil-pbc-depth`).
4. Apply `lem-weil-pbc-auslander-buchsbaum` to this module to bound the local ring depth by
`r`. Apply it again to each localized quotient; nonnegative module depth bounds each local
projective dimension by `r`.
5. Use `lem-weil-pbc-finite-module-pd-local-global` and
`lem-weil-pbc-projective-dimension-ext-characterization` to obtain the global bound.
6. Shorten the chosen finite projective resolution at `r` using
`lem-weil-pbc-projective-resolution-kernel-projective`. The last kernel is projective and is
the image of a finite module, hence finite. For `r = 0` the cyclic quotient itself is finite
projective. Pad with zero terms if needed and reindex `i` as cochain degree `-i`.
7. Tensor with any module. The resulting complex has support in `[-r, 0]`, so its cohomology,
namely `Tor'` in degree `i`, vanishes for `i > r` (`def-weil-pbc-tor-modules`). -/
theorem exists_uniform_finite_projective_resolution_quotient_pow
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)] (I : Ideal A)
    (hfinite : ∀ n : ℕ, 1 ≤ n → Finite (A ⧸ I ^ n))
    (hperfect : ∀ n : ℕ, 1 ≤ n →
      DerivedCategory.IsPerfect
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ I ^ n)))) :
    ∃ r : ℕ,
      (∀ n : ℕ, 1 ≤ n →
        ∃ P : ProjectiveResolution (ModuleCat.of A (A ⧸ I ^ n)),
          (∀ i : ℕ, Module.Finite A (P.complex.X i)) ∧
          (∀ i : ℕ, r < i → IsZero (P.complex.X i))) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ (M : ModuleCat.{u} A) (i : ℕ), r < i →
        IsZero (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I ^ n))).obj M)) := by
  sorry

/-- The same bound can equivalently be expressed by derived tensor amplitude `[-r, 0]`.
Source: Stacks Project, Algebra, Tags 00LY, 00M5, 058R and 065R; the equivalence clause of
(blueprint: lem-weil-pbc-uniform-perfect-quotient-bound).

Proof: tensor a finite projective resolution of length at most `r` with an arbitrary module;
its homology is Tor, and its terms above `r` vanish. Conversely apply
`lem-pc-finite-projective-dimension-of-tor-bound` to the cyclic finite quotient over the
Noetherian ring, then `lem-weil-pbc-projective-dimension-ext-characterization` to obtain a
length bound. Perfectness gives an initial finite projective resolution by cancellation of
its positive tail, as in the preceding theorem. Shorten this resolution using
`lem-weil-pbc-projective-resolution-kernel-projective`: the last kernel is a projective image
of a finite module. For `r = 0` use the quotient itself; zero quotients use zero resolutions.
Reindex homological degree `i` as cochain degree `-i`; positive cochain cohomology vanishes
because the tensor resolution has no positive cochain terms. -/
theorem uniform_finite_projective_resolution_quotient_pow_iff_tor_vanishing
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)] (I : Ideal A)
    (hfinite : ∀ n : ℕ, 1 ≤ n → Finite (A ⧸ I ^ n))
    (hperfect : ∀ n : ℕ, 1 ≤ n →
      DerivedCategory.IsPerfect
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ I ^ n)))) (r : ℕ) :
    (∀ n : ℕ, 1 ≤ n →
      ∃ P : ProjectiveResolution (ModuleCat.of A (A ⧸ I ^ n)),
        (∀ i : ℕ, Module.Finite A (P.complex.X i)) ∧
        (∀ i : ℕ, r < i → IsZero (P.complex.X i))) ↔
    (∀ n : ℕ, 1 ≤ n → ∀ (M : ModuleCat.{u} A) (i : ℕ), r < i →
      IsZero (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I ^ n))).obj M)) := by
  sorry

end ModuleCat
