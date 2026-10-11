/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.RingTheory.FormalGlueingH0
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Localization of compatible sections of formal glueing data

Source: Stacks Project, More on Algebra, proof of Proposition 05ER, second paragraph,
using Lemmas 05EQ and 05EP (blueprint: lem-weil-pbc-formal-glueing-H0-localization).
-/

@[expose] public section

universe uL vL wL

namespace FormalGlueing

variable {R : Type uL} {S : Type vL} [CommRing R] [CommRing S]

/-- The projection to a chart extends uniquely across localization and is bijective.
Source: Stacks Project, More on Algebra, proof of Proposition 05ER, second paragraph,
using Lemmas 05EQ and 05EP (blueprint: lem-weil-pbc-formal-glueing-H0-localization).

Proof:
1. Write `H^0` as the kernel of the finite list of compatibility differences
   [def-weil-pbc-formal-glueing-data, def-weil-pbc-module-localization-away,
   def-weil-module-base-change].
2. Localize this kernel at `u = f i`. Localization is exact
   [lem-weil-pbc-localization-module-exact]. It commutes with the finite products:
   take a common denominator and a common power killing the finitely many errors.
3. Given `x` in `M i`, set the prime coordinate to `alpha i` inverse applied to
   `1 ⊗ x`, and the `j` coordinate to `alpha_overlap i j (x/1)`.
   The cocycle implies `alpha_overlap i i = id`, so its `i` coordinate is `x`
   [def-weil-pbc-formal-glueing-data, lem-weil-pbc-formal-glueing-canonical-maps].
4. The square condition gives the prime/chart equations for this tuple; the cocycle
   gives its overlap equations, after the canonical localization swaps and tensor
   comparisons [lem-weil-pbc-formal-glueing-canonical-maps]. Step 2 gives an element
   of the localized `H^0` projecting to `x`.
5. Conversely, the `i` prime/chart equation and the `(i,j)` overlap equations force
   every compatible tuple with `i` coordinate `x` to be the tuple of step 3.
   Thus projection and this construction are inverse. The localization universal
   property gives uniqueness [def-weil-pbc-module-localization-away]. -/
theorem exists_unique_bijective_h0_localization {t : ℕ} (φ : R →+* S)
    (hflat : φ.Flat) (f : Fin t → R) (X : Data.{uL, vL, wL} φ f) (i : Fin t) :
    ∃ π : LocalizedModule.Away (f i) (h0 φ f X) →ₗ[R] piece (f i) (X.M i),
      (∀ h : h0 φ f X, π (LocalizedModule.mk h 1) = h.val.2 i) ∧
      (∀ π' : LocalizedModule.Away (f i) (h0 φ f X) →ₗ[R] piece (f i) (X.M i),
        (∀ h : h0 φ f X, π' (LocalizedModule.mk h 1) = h.val.2 i) → π' = π) ∧
      Function.Bijective π := by
  sorry

end FormalGlueing
