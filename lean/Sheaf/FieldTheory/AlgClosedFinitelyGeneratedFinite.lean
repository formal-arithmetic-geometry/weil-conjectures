/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Sheaf.FieldTheory.FieldTower

import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Minpoly.Finite

/-!
# Algebraically closed finitely generated field extensions are finite

Source: Stacks Project, Fields, Tags 030F and 09GH, with the agent-written Eisenstein
obstruction in the DAG proof (blueprint: lem-trf-algclosed-fg-field-finite).
-/

@[expose] public section

universe u v

namespace FieldExtension

/-- An algebraically closed field finitely generated as a field over `F` is finite over `F`.
No algebraic closedness is assumed of `F`.

Source: Stacks Project, Fields, Tags 030F and 09GH, and the agent-written Eisenstein
obstruction (blueprint: lem-trf-algclosed-fg-field-finite).

Proof plan:
1. The structure map `algebraMap F L` is injective, so identify `F` with its image.
   By `lem-weil-pbc-finitely-generated-field-finite-transcendence-basis`, choose a finite
   transcendence basis `t₁, ..., tᵣ`, and put `K = F(t₁, ..., tᵣ)`. The original finite
   generating family also generates `L` over `K`, and its elements are algebraic over `K`.
   By `lem-weil-pbc-algebraic-generators-finite-extension`, `L/K` is finite; put `d = [L:K]`.
2. If `r ≥ 1`, `lem-trf-rational-parameter-binomial-irreducible` makes
   `X^(d+1) - t₁` irreducible over `K`, in every characteristic. This polynomial is monic
   of degree `d+1`. Algebraic closedness of `L` supplies a root in `L`.
   By `lem-trf-irreducible-root-degree-bound`, its degree is at most `d`, a contradiction.
3. Thus `r = 0` and `K = F`: adjoining the empty family gives the base field. The finite
   extension from step 1 is therefore `L/F`, with scalars through the given structure map.
-/
theorem finiteDimensional_of_isAlgClosed_of_fg (F : Type u) (L : Type v)
    [Field F] [Field L] [Algebra F L] [IsAlgClosed L]
    (hfg : (⊤ : IntermediateField F L).FG) : FiniteDimensional F L := by
  sorry

end FieldExtension
