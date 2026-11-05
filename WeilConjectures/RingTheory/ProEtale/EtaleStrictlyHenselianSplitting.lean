/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian
public import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction
public import Mathlib.RingTheory.Unramified.Finite

/-!
# Étale algebras over strictly henselian local rings split off copies of the base

Let `A` be a strictly henselian local ring with maximal ideal `m` and `B` an étale `A`-algebra.
Every point of the closed fibre of `Spec B` is the image of a section `σ : B →ₐ[A] A`, and a
section of an unramified algebra cuts out a copy of `A` in `B`: there is an idempotent `e` with
`b * e = σ b * e` for all `b`. Gathering finitely many of these idempotents, one obtains an
idempotent `f ∈ m B` such that `B (1 - f)` is spanned over `A` by idempotents. In other words,
`B ≅ Aⁿ × B''` with `B'' = m B''`.

## Main statements

- `Algebra.FormallyUnramified.exists_isIdempotentElem_of_algHom`: the idempotent cut out by a
  section of an unramified algebra.
- `Algebra.Etale.exists_isIdempotentElem_mem_map_maximalIdeal`: the splitting of an étale
  algebra over a strictly henselian local ring.
-/

@[expose] public section

universe u

open IsLocalRing
open scoped TensorProduct

