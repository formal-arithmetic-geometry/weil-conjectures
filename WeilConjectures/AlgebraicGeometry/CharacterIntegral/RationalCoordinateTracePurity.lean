/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CharacterIntegral.CharacterIntegralTrace
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist

/-! # Purity of the normalized rational coordinate trace

Source: the finite affine-space top trace and coefficient-passage paragraphs of
lem-fd-character-integral in the latest blueprint
(blueprint: lem-fd-rational-coordinate-trace-purity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CharacterIntegral
open DiagonalCoefficients RationalP1

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))

/-- The constant-coefficient computation with the actual projective normalization.

Source: latest blueprint, sec-fourier-transform/sk-lem-wft-character-integral/
lem-fd-character-integral.proof.md, the zero-form trace and coefficient-passage
paragraphs (blueprint: lem-fd-rational-coordinate-trace-purity).

Proof:
1. At every finite coefficient quotient apply the normalized affine-space top
trace. The comparison is the ordered composite of the open-extension counits and
the projective-line counits, with its root normalization, including the identity
in dimension zero. The etale/pro-etale and ordinary/internal comparisons retain
these exact counits and their normalizations.
2. Compact support of the integral Tate line is bounded constructible of finite
Tor amplitude and hence derived complete. Scalar comparison identifies its actual
reduction system with the finite compact-support systems. The normalized trace
commutes with the finite quotient maps, including nonflat ones, by scalar descent
of the vector trace. The whole-system diagonal references in d identify its
projective counits with these same finite counits. Thus its ordered trace is a
map of the actual reduction towers. Since every evaluated finite trace is
invertible, the system map and its derived inverse limit are invertible.
3. Apply the rationalization and, in the closure branch, finite-subextension scalar
comparisons to this same morphism. They preserve compact support on these
finite-Tor objects and preserve the fixed Tate lines and counits. This gives
invertibility of each actual one-coordinate rational trace for every d with
its recorded normalization. The iteration and sign are handled by the consumer.
4. Apply the proper and open compact-support projection formulas to the positive
Tate line, compatibly with ordered coordinate pullback and tensor powers. The
iterated trace yields the regular coefficient module after tensoring the compact
image of the regular module with the positive signed line and shifting by twice
the rank. The consumer constructs the actual signed-line evaluation, proves its
derived cancellation and cancels the shift; no inverse-line assertion is left
here. The consumer also proves rank zero from the unit and zero shift.
The finite trace is compatible with arbitrary change of Noetherian base.
All schemes here are finite type over the algebraically closed Omega, which has
finite ell-cohomological dimension; no algebraicity over a finite field is used.
-/
theorem rationalCoordinateTrace_purity (p : ℕ) [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (Ω : Type u) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] :
    (∀ r : ℕ, Nonempty
      ((((CondensedRing.derivedTensor (coefficient ℓ c).X (Spec (.of Ω))).obj
        ((compact ℓ c (Spec (.of Ω)) (r + 1)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((CondensedRing.upperStar (coefficient ℓ c).X
              (affineTraceProjection (Spec (.of Ω)) (r + 1))).obj
                (Mod.regular (condensedRingObj (coefficient ℓ c).X (Spec (.of Ω)))))))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (spInternalSignedTwist (Spec (.of Ω))
              (condensedRingObj (coefficient ℓ c).X (Spec (.of Ω)))
                (line ℓ c (Spec (.of Ω))) ((r + 1 : ℕ) : ℤ))))⟦2 * ((r + 1 : ℕ) : ℤ)⟧ ≅
        unit (coefficient ℓ c).X (Spec (.of Ω)))) ∧
    ∀ (r : ℕ) (d : TraceData ℓ c (Spec (.of Ω))),
      IsIso (coordinateTrace ℓ c (Spec (.of Ω)) d r) := by
  sorry

end AlgebraicGeometry.ProEtale.CharacterIntegral
