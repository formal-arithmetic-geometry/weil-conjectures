## What changed

Proved `WeilConjectures.RamifiedPullback.coefficients_exists` in
`Sheaf.Paper.RamifiedCoefficientQuotientComparison`, preserving its statement.
The proof uses the existing projection-normalized completed inclusion and the proved
uniformizer-kernel and surjectivity lemmas. Private helpers prove the general quotient
base-change criterion by tensor generators, its sheafification formula, and every finite
transition square. The completed coefficient kernel equality follows by mapping the given
principal ideal equality and its powers. Updated the node to this actual proof.

Added proof-only imports of `Sheaf.Paper.CompletedCoefficientRegularQuotients` and
`Sheaf.Paper.FiniteFreeCompletedScalarComparison`; `import all` makes their proved private
projection/kernel and scalar-normalization helpers available without redeclaring them.
No existing definitions, signatures, instances, attributes, or public imports changed.

## Proved and sorry left

Closed the sole original hole: `WeilConjectures.RamifiedPullback.coefficients_exists`
(node `lem-weil-ramified-coefficient-quotient-comparison`). Added zero holes; zero remain
in the delivered module. All new helpers are private and fully proved.

Validation: the complete module passed server single-file compilation in 45.5 seconds.
Delivery preflight recompiles the final file after omitting unused section variables.

## No longer needed

No original import was removed: `RamifiedPullbackTowerData` defines the statement.
No module is withdrawn. The old plan's proof dependencies
`def-weil-proetale-inverse-image`, `lem-weil-pbc-constant-completion-equivalence`,
`def-weil-pbc-ringed-tensor-section-calculus`, and `def-pur-integral-derived-operations`
are not used by this proof. In particular there is no need for proof imports of
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, `ConstantCompletionEquivalence`,
`RingedTopoiTensorSections`, or
`IntegralDerivedOperationsOnSlices`: the coefficient result requires no geometric
pullback or cochain comparison. Some remain available through the statement's retained
public import; this delivery makes no claim that they leave the global target closure.
The canonical quotient clause is supplied instead by the existing proved coefficient
kernel calculation, and the needed tensor quotient argument is proved here directly.

## Where the brief, the DAG or earlier work was wrong

The original node's steps 1 and 4 discussed compatibility with scheme pullbacks and
chain maps, although this item's `Coefficients` structure asks only for coefficient
maps on one scheme. These calculations belong to the parent identification, not this
coefficient theorem. The actual transition field ranges over all a ≤ b, including equal
indices, and the proof establishes exactly that range. No mathematical statement repair
or change of the unit route was needed. No new nodes or split obligations were added.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
