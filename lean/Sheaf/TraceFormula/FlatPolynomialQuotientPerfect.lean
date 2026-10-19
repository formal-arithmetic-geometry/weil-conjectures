/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Algebra.Homology.FlatResolutionTorComparison
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.RingTheory.PolynomialTorBound
import Sheaf.CategoryTheory.DerivedCategory.BoundedFiniteTorPerfect
import Sheaf.RingTheory.FiniteFreeResolution
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.FiniteType

/-!
# Perfectness of a flat finite-type polynomial quotient

Source: Stacks Project, more-algebra.tex, Tags 067J and 068Y, and
`dualizing.tex`, Tag 0BZW (blueprint: lem-trf-flat-polynomial-quotient-perfect).
-/

@[expose] public section

universe u wR wP

open CategoryTheory

namespace DerivedCategory

/-- A flat finite-type map of Noetherian rings, together with a polynomial presentation,
produces a perfect polynomial quotient and has finite Tor dimension over the base.
Source: Stacks Project, more-algebra.tex, Tags 067J and 068Y, and
`dualizing.tex`, Tag 0BZW (blueprint: lem-trf-flat-polynomial-quotient-perfect).

Proof:
1. Apply `lem-weil-pbc-finite-type-algebra-noetherian` to the polynomial algebra
   `P = R[x₁,...,xₙ]`. The presentation makes `A` cyclic as a `P`-module: lift any
   `a : A` to `q : P` and write `a = q • 1`. Thus `A[0]` is bounded and termwise finite.
2. Flatness of the ring map makes `A[0]` a bounded-above complex of flat `R`-modules;
   its zero terms are flat as well. By `lem-pc-module-bounded-flat-kflat` it is K-flat.
   The comparison `lem-pc-source-kflat-module-tensor-model` computes its derived tensor
   with every ordinary `R`-module `M` by `(A ⊗ M)[0]`. Hence the additional Tor interval
   is `[0,0]`. Applying `lem-pc-flat-resolution-tor-comparison` to the identity-augmented
   degree-zero flat chain complex also gives ordinary first-variable Tor vanishing for
   every positive degree.
3. Apply `lem-pc-polynomial-tor-bound` with base `R`, polynomial module `A`, and `d = 0`.
   Step 2 is its first-variable Tor hypothesis. It gives vanishing of `Tor_j` over `P`
   for every `P`-module whenever `j > n`, with no regularity assumption on the base.
4. By `lem-weil-pbc-finite-free-resolution-noetherian`, the cyclic module `A` admits an
   augmented finite-free resolution. Put its degree `j` term in cochain degree `-j`;
   augmentation exactness makes it quasi-isomorphic to `A[0]`. Its terms are flat by
   `lem-sc-affine-standard-cover-finite-free-local-fp-flat`, so it is K-flat by
   `lem-pc-module-bounded-flat-kflat`. The derived tensor model from Step 2 and
   `lem-pc-flat-resolution-tor-comparison` identify degree `-j` cohomology after tensor
   with `Tor_j`. Step 3 gives vanishing below `-n`; there are no terms above zero.
   Consequently the polynomial quotient has Tor amplitude in `[-n,0]`.
5. Apply `lem-weil-bounded-finite-tor-perfect` to the bounded finite complex `A[0]`
   over the Noetherian ring `P`, using Step 4. Its finite-projective model `E` in
   `[-n,0]` proves `def-pc-perfect-ring-complex`. For the equivalent augmented-resolution
   interpretation (Tag 066Q), use `H⁰(E) ≅ A` and `E¹ = 0` to augment `E⁰` through its
   quotient `H⁰(E)`. This augmentation is surjective with kernel the image of `d⁻¹`;
   in negative degrees vanishing cohomology gives exactness, by
   `def-weil-abstract-derived-category`. When `n = 0`, only degree zero remains.
-/
theorem flat_polynomial_quotient_perfect
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [IsNoetherianRing A]
    (φ : R →+* A) (hφflat : RingHom.Flat φ) (hφfinite : RingHom.FiniteType φ)
    (n : ℕ)
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wP} (ModuleCat.{u} (MvPolynomial (Fin n) R))]
    (p : MvPolynomial (Fin n) R →+* A)
    (hp : Function.Surjective p)
    (hpc : p.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) = φ) :
    IsPerfectRingComplex
        (R := MvPolynomial (Fin n) R)
        (C := Q.obj
          ((CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj
            (@ModuleCat.of (MvPolynomial (Fin n) R) _ A _ (Module.compHom A p)))) ∧
      ∃ a b : ℤ, a ≤ b ∧
        torAmplitudeIn (ModuleCat.{u} R) a b
          (Q.obj
            ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
              (@ModuleCat.of R _ A _ (Module.compHom A φ)))) := by
  sorry

end DerivedCategory
