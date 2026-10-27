## What changed

Replaced the proof hole in
`AlgebraicGeometry.Scheme.finitePerfectAdic_constant_models_reduction`, preserving
its entire signature and its public imports. The proof derives the ordinary tensor
and slice-restriction square on K-flat resolutions, applies the existing normalized
scalar-transitivity isomorphisms to the two compatible coefficient paths, inserts
the two given chart models, and reflects the resulting constant isomorphism using
`finiteConstantSlice_iso_reflects`. A canonical localization equivalence reconciles
that theorem's standard algebraic localization with this item's small localization.

Added `Sheaf.Paper.FinitePerfectAdicConstantScalarExtension`, for the genuine
coefficient-universe bridge needed by the existing large constant scalar comparison.
Its argument uses bounded projective representatives, the Mathlib tensor/ULift
linear equivalence, and the existing K-flat representative computations. The lemma
has no adic datum, completion, chart, or nonemptiness hypothesis. All auxiliary
constructions and lemmas are private. No other existing Lean module is changed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.finitePerfectAdic_constant_models_reduction`
(node `lem-weil-pbc-finite-perfect-adic-constant-models-reduction`).

New proved theorem:
`AlgebraicGeometry.Scheme.finitePerfectAdicConstant_scalarExtension`
(node `lem-weil-pbc-finite-perfect-adic-constant-scalar-extension`).

The delivery closes the one original hole and adds zero holes. The delivered Lean
files contain zero `sorry`; no hole is split off. The new scalar-extension module
compiled without diagnostics in 28.4 seconds and the complete item module compiled
without diagnostics in 8.3 seconds, both through the official remote compiler.

## No longer needed

No original public import is removed and no module is withdrawn.

The planned direct use of `lem-weil-pbc-completed-constant-sheaf-reduction`
(`Sheaf.Paper.CompletedConstantSheafReduction`) is unnecessary: the proof uses the
actual coefficient isomorphisms and derived transitivity. The planned direct uses
of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`prop-weil-pbc-geometric-stalks-exact`, and
`lem-weil-pbc-constant-sheaf-geometric-stalk` are replaced by the already stated
`finiteConstantSlice_iso_reflects` interface. The weakly etale localization node
remains a transitive dependency of its derived stalk comparison. The large constant
scalar-extension node also remains a transitive dependency of the new small
comparison. These observations do not authorize withdrawing any existing source
module or any dependency still used elsewhere.

## Where the brief, the DAG or earlier work was wrong

The planned mathematical argument is valid, but it elides the difference between
the small algebraic derived localization used in the item and the standard one
used in `finiteConstantSlice_iso_reflects`, and the coefficient-universe lift before
constant realization. The proof makes both comparisons explicit. The existing
large constant scalar-extension theorem applies after this bridge, not directly
to small algebraic coefficients. The final reflection step needs no perfectness;
only the source perfectness is needed for the representative calculation. The
unused target-perfectness hypothesis is preserved verbatim.

## New nodes

`lem-weil-pbc-finite-perfect-adic-constant-scalar-extension` records the generic
constant scalar-extension comparison including the coefficient-universe lift. Its
proof is strictly the scalar-comparison step of the item: it involves no tower,
compatible finite quotient identifications, two chart models, or stalk reflection.
The node includes three Mathlib searches and its Lean declaration verbatim.
Blueprint searches for constant/scalar extension and constant/tensor found no
existing statement of this coefficient-universe bridge. Its general K-flat and
exact-right-adjoint representative lemmas are proved tools; the unit route stays
unchanged.
The original node's proof, proof dependencies, and proof origin now follow the
implemented route. No definition or statement changes, consumer adaptations, or
change records are required.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
