## What changed

Proved `AddMonoidAlgebra.positiveMonoid_adic_filtration` in
`Sheaf.RingTheory.PositiveMonoidAdicFiltration`, with its original signature.
All auxiliary declarations are private and fully proved, and the proof uses
Mathlib only. No other existing Lean module was changed.

The maximal decomposition length is an attained maximum of a bounded nonempty
set of natural numbers. Concatenation gives superadditivity. A finite generating
set with zero erased expresses every exponent as the sum of a list; bounded
weight or bounded maximal length bounds the list length. Finite sets of bounded
lists give both finiteness claims. Tuples with fixed sum lie in a finite Cartesian
power of a weight sublevel set.

For the algebraic clause, construct the actual coefficient ideals
`K_n = {F | ∀ p, F.coeff p ∈ I^(n-ν(p))}` and prove
`K_m * K_n ≤ K_(m+n)` by finite convolution and superadditivity.
The displayed mixed generators belong to `K_1`, hence `J^n ≤ K_n`.
For the converse, the constant ring map sends `I^k` into `J^k`, while a maximal
length decomposition gives `single p 1 ∈ J^(ν p)`. Their product gives each
monomial in `J^((n-ν p)+ν p) ≤ J^n`. Sum over the finite support.

Replaced the public import of `Sheaf.RingTheory.CompleteToricModel` by
`Mathlib.Algebra.MonoidAlgebra.Defs`; the statement uses the Mathlib monoid
algebra directly. Added private imports for finite indexed sums, finite sets of
lists, maxima of bounded natural sets, ideal maps and proof tactics.
Updated only `proof`, `proof_deps`, and `proof_origin` in
`lem-trf-positive-monoid-adic-filtration` to follow this proof.
There are no current direct Lean importers of the item module in the shared
source tree, so no consumer adaptations are needed.

Validation: the remote single-file compiler accepted the complete proof in
5.1 seconds with no warnings. `#print axioms` reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. The temporary axiom-print command was
removed before delivery. A source comparison confirms the original theorem
signature is byte-for-byte unchanged, and every Lean line is at most 100
characters. The delivery tool performs the final compile and preflight.

## Proved and sorry left

Closed the single original hole:
`AddMonoidAlgebra.positiveMonoid_adic_filtration`
(node `lem-trf-positive-monoid-adic-filtration`).

Holes closed: 1. Holes added: 0. Split-off statements: 0.
No `sorry` remains in the item or is added elsewhere.
No unproved project declaration is used by the proof.

## No longer needed

Removed import: `Sheaf.RingTheory.CompleteToricModel`.
Removed proof dependency: `def-trf-complete-toric-model`.
The full completed toric-model construction is unnecessary for an assertion
about the ordinary finite-support Mathlib monoid algebra. Its conceptual
statement dependency is retained in the node. No module is withdrawn, and no
claim is made that this model is unnecessary for other project items.

The proof does not need explicit finite products of arbitrary ideal generators,
a finite box of multiplicities, or a partition of a decomposition into nonempty
blocks. Finite bounded lists, coefficient ideals, ideal maps and monotonicity of
ideal powers replace these steps. All finiteness and filtration conclusions are
preserved, including the zero monoid, the zero ring, and the zero or unit ideal.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original six-step plan is mathematically sound.
The finite-list argument and coefficient-ideal argument are shorter Lean routes
to the same conclusions. The ILO reference motivates the monoid model; as the
existing node already states, the coefficient refinement is an agent argument,
not a theorem quoted verbatim from ILO. The unit route is unchanged.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
