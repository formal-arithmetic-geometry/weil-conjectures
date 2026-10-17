/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages
import Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LeraySpectralSequence

/-!
# Composition for constructibility of higher direct images

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`lem-finrepair-composition-c.md`, order 1599 (blueprint: lem-finrepair-composition-c).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- If every higher direct image along `f` and along `g` preserves constructibility,
then every higher direct image along `f ≫ g` does as well, in the domain of property `C`.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-finrepair-composition-c.md`
(blueprint: lem-finrepair-composition-c); Stacks Project, Tags 0734, 015N and 03RZ.

Proof plan:
1. Fix a constructible `Λ`-module sheaf `F` on `X`. The hypotheses `C(f)` and `C(g)`
   successively make all `Rᵃg_*(Rᵇf_*F)` constructible for nonnegative `a` and `b`.
2. Apply `lem-weil-pbc-grothendieck-spectral-sequence` to `f`, `g`, and `Λ`.
   Its second page consists of these sheaves, its terms vanish outside the first
   quadrant, its differentials have bidegree `(r,1-r)`, and its abutment in degree
   `n` is `Rⁿ(f ≫ g)_*F`, with a finite filtration by stable-page graded pieces.
   No acyclicity hypothesis on `F` or uniform dimension bound is required.
3. Induct simultaneously in all bidegrees on the page number `r ≥ 2`.
   The second-page terms are constructible by step 1, including the zero terms
   outside the first quadrant. The kernel of an outgoing differential is
   constructible by `thm-constructible-serre`. The incoming differential factors
   through that kernel since its composite with the outgoing differential is zero.
   Its cokernel is constructible by the same theorem, and is the next-page term.
   This uses kernels and cokernels between constructible sheaves, not arbitrary
   subsheaves.
4. For each fixed `n` and `0 ≤ p ≤ n`, choose `r > max(p,n-p+1)`. Stabilization
   identifies the stable graded piece with the constructible term on page `r`.
   The finite filtration of the degree-`n` abutment starts with the whole sheaf and
   ends at zero in step `n+1`. Descending induction on its steps, using extension
   closure in `thm-constructible-serre`, makes the whole abutment constructible.
   Since `n` and `F` are arbitrary, this is `C(f ≫ g)` by `def-finrepair-property-c`.
   The stabilization bound depends on the bidegree; there is no uniform vanishing claim. -/
theorem hasConstructibleHigherDirectImages_comp
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hY : IsSmoothBaseChangeCoefficients N Λ Y)
    (hZ : IsSmoothBaseChangeCoefficients N Λ Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasConstructibleHigherDirectImages k N Λ hX hY f)
    (hg : HasConstructibleHigherDirectImages k N Λ hY hZ g) :
    HasConstructibleHigherDirectImages k N Λ hX hZ (f ≫ g) := by
  sorry

end AlgebraicGeometry.Etale
