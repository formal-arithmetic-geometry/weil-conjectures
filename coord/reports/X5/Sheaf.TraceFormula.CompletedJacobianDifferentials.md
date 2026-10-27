## What changed

Repaired the return of delivery `33f22ef0102`: removed the unnecessary file-level
warning-suppression option. The source hole ledger treated the option name's final
component as an unattributed hole at line 47; there was no proof hole at that location.
The completed proof and its definitions are retained, with no new holes.

Changed `completedDifferentialTarget` from an `abbrev` to a noncomputable named
wrapper around the identical tensor product, deriving its additive and local-ring
module structures explicitly. This keeps the public type unchanged while bringing
the item under the 60-second compiler limit. The change is recorded in
`coord/changes/completed-differential-target-performance.md`.

Implemented `AlgebraicGeometry.completedJacobianDifferentials` from the existing
completion/Kähler comparison and the formal-power-series continuous-differential
Jacobian presentation. Private proved helpers transport differentials along ring
and coefficient-field equivalences, shift the inverse-limit indexing, transport
finite coordinate modules and their quotients, and reverse the tensor factors.

Normalized `completedIdeal` to the maximal ideal of the localization, and removed
the resulting redundant quotient transport from `completedResidueMap`. These are
the same mathematical constructions: `IsLocalization.AtPrime.map_eq_maximalIdeal`
identifies the old ideal with the new one. No theorem signature changes. The change
record is `coord/changes/completed-jacobian-completion-normalization.md`.

Added private proof imports for completion localness, power-series invertibility,
the proved power-series coefficient criterion, and the two differential dependencies.
Private transport definitions, the universal derivation, and the tensor scalar
action use application lemmas and irreducibility to avoid expensive unfolding. The final basis calculation uses
the inverse-equivalence API instead of expanding composed transports. The item compiles through `lcompile.py` within 60 seconds.

Updated the item's DAG proof to the actual route. The unit route is preserved.
No source-library declaration is changed. The construction works for empty
variable and relation index sets; the finite-basis formulas are valid empty sums,
and the inverse-limit shift uses the zero differential module at exponent zero.

## Proved and sorry left

Closed: `AlgebraicGeometry.completedJacobianDifferentials`
(`lem-trf-completed-jacobian-differentials`), one existing hole.
Added: none. Remaining in delivered modules: none. No split statements.

The proof uses the stated comparison theorem, whose proof remains unfinished in
its own module; this delivery does not claim to discharge that dependency.

## No longer needed

The proof does not directly need `lem-trf-separable-field-differentials-vanish`:
vanishing on the coefficient field follows by injectivity of the comparison and
the relative continuous derivation's coefficient identity. Removed it from this
node's proof dependencies. It may remain needed by other nodes.

Removed the unused private import `Mathlib.RingTheory.Unramified.Field`.
No module is withdrawn. The separate topological-nilpotence argument in the old
plan is unnecessary: surjectivity between local rings identifies maximal ideals.
The continuity hypothesis remains verbatim in the theorem statement.

## Where the brief, the DAG or earlier work was wrong

The supplied mathematical plan is sufficient, but its Lean interfaces use three
different presentations: `S/p` versus the canonical localized residue field,
`Ω tensor Â` versus `Â tensor Ω`, and inverse limits indexed by all powers versus
positive powers. The private equivalences reconcile these without changing the
statement or assuming any new theorem.

The return's unattributed hole was the warning-option name, rather than an
unfinished proof. Removing that option gives zero hole rows and no lexer warnings
in the source ledger. The retained theorem signature and node statement are
unchanged; only the node's proof, proof dependencies and proof origin differ.

The original mapped-ideal definition prevented direct use of the maximal-ideal
completion comparison. The recorded normalization removes equality transports;
the two ideals are equal by the existing localization theorem. The exponent-one
power-series coefficient criterion supplies the variable-ideal/maximal-ideal
identification. The freshly run consumer scan finds three direct importers and
88 transitive importers (2026-10-24); only the item itself mentions the changed definitions.

The target-wrapper change preserves the tensor construction. All three direct
importers compile against it without source edits: FormalPlaneAdjunctionLattice
(14.3 s), SeparableClosedPointFormalPresentation (9.0 s), and
CompletedConormalDeterminantComparison (43.3 s). The item compiled in 58.4 s in
that dependency-ordered check; the subsequent tensor-transport optimization compiled
in 56.9 s with profiling enabled. Explicitly retaining the scalar-action field
gave a clean compile. Sealing the universal derivation and differential map and
using the quotient-map API earlier brought the delivery audit compile to 54.1 s
(with one redundant attribute command, removed in the final packet). No forced adaptations were needed.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
