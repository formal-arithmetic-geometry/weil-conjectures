/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # The degree filtration from chosen algebra and module generators

Source: Stacks Project, Tags 052N and 053E (proof of (2)), explicit generator-filtration
realization of module homogenization.
(blueprint: def-trf-generator-filtration)
-/

@[expose] public section

universe u v w

namespace Module

/-- The A-span of the monomials in b of total degree at most d, acting on the chosen m.
Source: Stacks Project, Tags 052N and 053E (proof of (2)), explicit generator-filtration
realization of homogenization. This formula is defined even without generation hypotheses.
(blueprint: def-trf-generator-filtration) -/
noncomputable def generatorFiltration
    (A : Type u) [CommRing A] {B : Type v} [CommRing B]
    {M : Type w} [AddCommGroup M] [Module A M] [Module B M]
    {n r : ℕ} (b : Fin n → B) (m : Fin r → M) (d : ℕ) : Submodule A M :=
  Submodule.span A {x | ∃ (α : Fin n → ℕ) (j : Fin r),
    (∑ i, α i) ≤ d ∧ x = (∏ i, b i ^ α i) • m j}

end Module
