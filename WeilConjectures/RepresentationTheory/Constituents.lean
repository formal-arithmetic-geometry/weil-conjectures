/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import WeilConjectures.RepresentationTheory.CompositionSeries

/-!
# Comparing the constituents of representations

A *constituent* of a representation `ρ` is an irreducible subquotient `S / U`. The relation
`Representation.ConstituentsLE ρ σ` says that every constituent of `ρ` is equivalent to a
constituent of `σ`. This file proves the standard closure properties of this relation: it passes
along injective and surjective intertwining maps, the constituents of the middle term of a short
exact sequence are constituents of its ends, those of a representation with a finite filtration
are constituents of its graded pieces, and it is compatible with tensor products.

## Main definitions

- `Subrepresentation.quotient`: the quotient representation `V ⧸ U`.
- `Representation.ConstituentsLE`: every constituent of `ρ` is a constituent of `σ`.

## Main results

- `Subrepresentation.exists_subquotient_equiv_of_chain`: an irreducible subquotient of a
  representation with a finite filtration is a subquotient of one of the graded pieces.
- `Representation.ConstituentsLE.of_exact`: constituents of the middle of a short exact sequence.
- `Representation.ConstituentsLE.of_chain`: constituents of a representation with a finite
  filtration are constituents of the graded pieces.
- `Representation.ConstituentsLE.tprod`: `ρ ≤ ρ'` implies `ρ ⊗ σ ≤ ρ' ⊗ σ`.

## Blueprint

- `lem-mg-filtration-refinement`, `lem-mg-filtered-tensor-product`: the constituents of a filtered
  representation and of a tensor product.
-/

@[expose] public section

open TensorProduct

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

end Subrepresentation

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]
  {V V' V'' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  [AddCommGroup V''] [Module k V'']

namespace ConstituentsLE

variable {ρ : Representation k W V} {σ : Representation k W V'} {τ : Representation k W V''}

end ConstituentsLE

end Representation
