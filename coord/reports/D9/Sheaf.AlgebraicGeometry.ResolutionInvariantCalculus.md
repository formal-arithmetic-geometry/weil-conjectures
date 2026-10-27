## What changed

Proved `AlgebraicGeometry.exists_resolution_invariant_calculus` in
`Sheaf.AlgebraicGeometry.ResolutionInvariantCalculus`, preserving its signature and the
public import of `ResolutionInvariantCalculusData`.

The proof fixes the existing marked-ideal numerical engine, obtains its normalized word
assignment from gluing, and assembles the four current DAG dependencies. Finite-history
comparison supplies geometry on all admissible histories. Progress supplies extension
existence, preservation and strict decrease. Maximum-center descent and reduced closed
subscheme uniqueness identify every actual extension center with the regular maximum
center. Noetherianity gives coherence of both actual ideals in the calculus's existing
`IsFiniteTypeWithFiniteTypeKernels` encoding. The comparison fields specialize the
stagewise statements to the final stage and handle arbitrary reduced stratum ideals,
including empty inverse images. Termination concerns the same fixed word assignment.

Private proved helpers handle reduced ideal uniqueness, coherence, final-index transports,
and universe lifting. The word type is small; its `ULift` lies in the universe required by
the unchanged existential statement. The lift preserves maxima, maximum extensions and
admissibility, and transports every field explicitly.

Updated the item's DAG proof, dependencies and proof origin to match this assembly.
No other existing module or node is changed. No new public API, definition, instance or
attribute is introduced.

Validation: the complete delivered Lean module compiled successfully through `lcompile.py`
in 8.1 seconds, with no errors or warnings.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.exists_resolution_invariant_calculus`
(node `lem-trf-hilbert-samuel-resolution-invariant-calculus`).

Holes closed: 1. Holes added: 0. Split-off statements: 0.
There are no `sorry` declarations left in the delivered module. This is a proof from the
existing named dependency theorems; their remaining proofs remain separate items.

The raw construction and universe transport cover empty and regular schemes, finite
disjoint unions, length-zero histories, deletion of every pullback stage, arbitrary
smooth relative dimensions, and an empty inverse-image maximum stratum. In particular,
a positive maximum is incompatible with regularity, and an empty stratum has unit ideal.

## No longer needed

Removed these old direct proof imports:

- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Sheaf.TraceFormula.SmoothGeometricallyNormal`
- `WeilConjectures.RingTheory.FlatUnderRegular`
- `Mathlib.RingTheory.FiniteType`
- `Mathlib.Algebra.Module.FinitePresentation`
- `WeilConjectures.AlgebraicGeometry.Regular`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Sheaf.SecTraceFormula.SmoothCenterBlowupGeometry`

Their low-level arguments are packaged by the four declared normalized-word dependencies;
several remain transitive dependencies, and reduced-induced uniqueness and regularity are
still used through public imports. No global module withdrawal or removal of any lower
node is claimed. All four current declared proof dependencies are used.

Removed obsolete direct-tool approvals for
`lem-weil-pbc-finite-type-algebra-noetherian`, `lem-pc-proper-base-change`,
`etale-proposition-etale-reduced`, and `lem-weil-pbc-flat-under-regular` from this node.
Their uses inside dependency modules are unaffected. Retained reduced-induced uniqueness.
Added the already-stated numerical-engine existence and locally Noetherian/coherence
inputs actually used by the Lean assembly.

## Where the brief, the DAG or earlier work was wrong

The module docstring still described the older seven-step construction, while the current
DAG already factors it through four normalized-word modules. The proof follows that current split; the original source docstring is retained
as the expanded argument underlying those dependency modules. The statement itself needs no repair.

The small normalized word type cannot directly witness `V : Type (u + 1)`. The explicit
universe-lift argument resolves this without changing the existential statement or the
meaning of any calculus field. Final-stage specialization uses dependent index transports;
rewriting dependent `ValueFamily` expressions with simplification was insufficient, so
private proved transport lemmas handle those equalities directly.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
