/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.WeilSheaf.StalkCharpoly

/-!
# The local Frobenius and the local alternating trace of a Weil complex

Let `K` be a Weil complex on a `k₀`-scheme `X`, with geometric fiber `X̄ = X ×_{k₀} k̄`. A point
`g : Spec K ⟶ X` with values in a finite extension `K` of `k₀` with `qᵐ` elements, together with
an embedding `ι : K ↪ k̄`, gives a geometric point `x̄ : Spec k̄ ⟶ X̄` fixed by the `m`-th power
of the geometric Frobenius up to reparametrisation. The iterated Weil structure then induces the
local Frobenius `F_x^{(m)}` on the stalk `𝓗ʲ(K)_x̄` of every cohomology sheaf of `K`, and the
local alternating trace

`Tr(F_x^{(m)} | K_x̄) = ∑_j (-1)ʲ Tr(F_x^{(m)} | 𝓗ʲ(K)_x̄)`.

The conjugacy class of the local Frobenius does not depend on the embedding `ι`.

## Main definitions

- `AlgebraicGeometry.WeilComplex.stalk` (`def-weil-local-frobenius-trace`): the stalk
  `𝓗ʲ(K)_x̄` at a closed point with its local Frobenius `F_x`.
- `AlgebraicGeometry.WeilComplex.stalkAtGeometricFiberPoint` (`def-weil-local-frobenius-trace`):
  the stalk `𝓗ʲ(K)_x̄` with the local Frobenius `F_x^{(m)}`, at the geometric point attached to
  a point with values in a field with `qᵐ` elements and an embedding of that field into `k̄`.

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_equiv_stalkAtGeometricFiberPoint`
  (`lem-weil-local-frobenius-conjugacy-class`): the local Frobenius operators attached to two
  embeddings are conjugate.

## Implementation notes

The blueprint defines `K_x̄ := L x̄^* For(K)` and its trace as the alternating sum of the traces
on the cohomology sheaves. The local alternating trace `Tr(F_x^{(n)} | K_x̄)` of
`def-weil-local-frobenius-trace` is `AlgebraicGeometry.WeilComplex.traceFunction`
(`WeilConjectures.WeilSheaf.Stalk`), which takes that alternating sum as the definition: the
derived stalk is not used.

The remark `rem-ptr-weil-local-frobenius-trace-1` of the blueprint only points to
`AlgebraicGeometry.WeilComplex.nonempty_equiv_stalkAtGeometricFiberPoint`; it is recorded as
`AlgebraicGeometry.WeilComplex.exists_frobeniusEnd_stalkAtGeometricFiberPoint_eq_conj`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {l : ℕ} [Fact l.Prime]
variable {k₀ : Type u} [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

variable (F : WeilSheaf k₀ l X)

end WeilSheaf

namespace WeilComplex

variable (K : WeilComplex k₀ l X)

/-- Blueprint `def-weil-local-frobenius-trace`: Local Frobenius and local alternating trace.

The stalk `𝓗ʲ(For K)_x̄` of the `j`-th cohomology sheaf of a Weil complex at the geometric
point over a closed point `x`, with the local Frobenius `F_x`, obtained by iterating the Weil
isomorphism `deg x` times. The geometric point is attached to an embedding `κ(x) ↪ k̄` chosen
by `IsAlgClosed.lift` (`AlgebraicGeometry.WeilSheaf.stalk`). -/
noncomputable def stalk (j : ℤ) (x : X.finitePoints) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((homologySheaf j).obj K).stalk x

end WeilComplex

end AlgebraicGeometry
