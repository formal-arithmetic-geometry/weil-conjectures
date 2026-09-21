/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Algebra.Tower

/-!
# Spanning a submodule over a quotient of the scalars

Let `κ` be an `R`-algebra whose structure map `R → κ` is surjective — a quotient of `R`, up to
isomorphism — and let `N` be a submodule of an `R`-module `M` carrying a compatible `κ`-action.
By `Submodule.restrictScalars_span` the `R`-span and the `κ`-span of a subset of `N` agree, so a
`κ`-spanning set of `N` is already an `R`-spanning set; no Nakayama is needed.

## Main results

* `Submodule.span_image_coe_eq_self_of_span_eq_top`: a `κ`-spanning set of `N`, read in `M`,
  spans `N` over `R`.
-/

@[expose] public section

/-- **A `κ`-spanning set of a submodule `N`, read in the ambient module, spans `N` over `R`**, as
soon as the structure map `R → κ` is surjective. -/
theorem Submodule.span_image_coe_eq_self_of_span_eq_top {R κ M : Type*} [CommSemiring R]
    [CommSemiring κ] [Algebra R κ] [AddCommMonoid M] [Module R M] {N : Submodule R M}
    [Module κ N] [IsScalarTower R κ N] (hsur : Function.Surjective (algebraMap R κ))
    {s : Set N} (hs : Submodule.span κ s = ⊤) :
    Submodule.span R ((↑) '' s : Set M) = N := by
  have himg : ((↑) : N → M) '' s = N.subtype '' s := rfl
  rw [himg, Submodule.span_image, ← Submodule.restrictScalars_span R κ hsur, hs,
    Submodule.restrictScalars_top, Submodule.map_subtype_top]
