/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.StalkCardinality
public import WeilConjectures.ConstructibleSheaf.Pullback
public import Mathlib.Topology.NoetherianSpace

/-!
# Towers of finite locally constant sheaves are Mittag-Leffler

Let `X` be a scheme whose underlying space is noetherian and let `(Hₙ)ₙ` be a tower of finite
locally constant étale sheaves of `Λ`-modules on `X` with finite stalks (e.g. the higher direct
images `(Rᵠf_* Fₙ)ₙ` of an `ℓ`-adic tower along a smooth proper morphism). Then the tower is
Mittag-Leffler: for every `n` the images of the transition maps `H_k ⟶ Hₙ`, `k ≥ n`, stabilise
(`AlgebraicGeometry.Etale.mittagLeffler_imageSubobject_of_isFiniteLocallyConstantSheaf`).

Indeed, the images `Iₖ ⊆ Hₙ` form a decreasing chain of locally constant subsheaves
(`AlgebraicGeometry.Etale.isLocallyConstantSheaf_imageSubobject`, from the closure of locally
constant sheaves under kernels and cokernels). The cardinality of the stalk of `Iₖ` is a locally
constant function on `X`, hence constant on each of the finitely many irreducible components of
`X`; so these finitely many decreasing sequences of natural numbers stabilise simultaneously. Once
the stalk cardinalities of `I_{k} ⊆ I_N` agree everywhere, the inclusion is an isomorphism on all
geometric stalks, hence an isomorphism
(`AlgebraicGeometry.Etale.isIso_of_mono_of_natCard_sheafFiber_eq`).

This is the Mittag-Leffler input for the vanishing of `R¹lim` in the Milnor sequence of the
higher direct images of an `ℓ`-adic tower (Stacks 0CQD).
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

end AlgebraicGeometry.Etale
