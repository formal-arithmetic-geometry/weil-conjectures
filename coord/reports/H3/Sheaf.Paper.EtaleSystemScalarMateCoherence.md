## What changed

Replaced the proof hole of
`AlgebraicGeometry.Etale.SystemScalarMate.etaleSystemScalarMateCoherence`
with explicit adjunction calculations, finite-ring quotient normalization, joint
conservativity of exact evaluation, and finite-free exactness. All existing public
signatures and definitions are preserved. The complete item compiled through
`lcompile.py` in 50.2 seconds. Local irreducibility and transparency settings prevent
expensive unfolding of chosen derived functors during the proof calculations.

The finite-free proof reuses the proved private `model_limits_of_flat` helper from
`Sheaf.SixFunctors.SystemProperOpenScalarSquare` through a proof-only `import all`.
It applies `constantFiniteFree_sectionBasis` independently at each level; neither a
constant rank nor bases compatible with the transitions are required. A private
universe-polymorphic version of the proved `evaluation_mate` calculation handles
system and finite-level derived categories with different hom universes.

Added `Sheaf.Paper.EtaleSystemProjectionPresentationCoherence` for the normalized
projection evaluation, composition and unit equations for an arbitrary fixed Theory.
This is projection-level mathematics, without exceptional adjoints, transitions or
finite-free exactness. It isolates the interface gap in the existential projection
theorem rather than restating scalar-mate coherence.

## Proved and sorry left

The original module had one hole, in
`AlgebraicGeometry.Etale.SystemScalarMate.etaleSystemScalarMateCoherence`.
Its assembly proof is replaced, conditional on the new projection lemma.
One hole is added in
`AlgebraicGeometry.Etale.SystemProjection.etaleSystemProjectionPresentationCoherence`
(node `lem-pur-etale-system-projection-presentation-coherence`).
This is a decomposition, not a net hole reduction: one hole closed, one added.
No holes occur in definitions or private declarations.

## No longer needed

Removed the proof-only import
`Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`.
The fixed scalar models already define the balanced associators used in both words;
the mixed-square assertion follows from composition and equality of coefficient
composites. No extra iterated-normalization theorem is invoked. The original proof dependency
`lem-sfb-successive-derived-quotient-normalization` is therefore removed.
The obsolete approved tools `lem-pur-sheaf-ring-derived-coefficient-adjunction`
and `lem-sfb-successive-derived-quotient-normalization` are removed from this
node’s `tool_uses`.
`lem-weil-pbc-mate-pasting` is also unnecessary for the main assembly: the proof
transposes both sides and performs the counit/naturality calculation directly.

The proof does not apply `etaleSystemEvaluationBound` (its DVR-specific theorem is
unnecessary for naturality of the actual transition transformation), nor the
existence theorem `systemLevelLeftExtension`. Ordinary level functors directly
detect sectionwise isomorphisms, and exact evaluation commutes with homology. Their
public imports are retained because the pre-existing Adjoints/Transitions signatures
and interface use those modules. The generic derived scalar adjunction is recorded
in each Scalar model, so its separate existence theorem is not applied.

The existential `etaleSystemCoefficientProjection` does not directly supply laws
for the fixed arbitrary Theory. Its projection construction remains relevant inside
the new lower projection-normalization argument; its module is not withdrawn.
No source-library declaration is removed or replaced by a hole, and no module is
withdrawn. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The coefficient projection dependency concludes existence of a presentation together
with its projection laws. The item quantifies over every fixed `t : Theory c l`.
An existential witness cannot be substituted for that fixed t. The new theorem
makes the missing presentation-independent normalization explicit. Its docstring
and DAG proof explain the section normalization, geometric/open mates, exact
localization, composite restriction and triangle calculations required.

The existing generic `SemilinearSections.evaluation_mate` constrains all eight
categories to the same object and hom universe. The actual system and finite-level
categories here have different hom universes. The private generalization repeats its
proved calculation with independent category universes, preserving the public API.

## New nodes

`lem-pur-etale-system-projection-presentation-coherence` records exactly the three
projection laws used by the item. The ordinary projection cocycle, scalar unit and
evaluation formulas are strictly below scalar-mate coherence and contain no right
adjoint of compact support. Its sources are Zheng Constructions 2.26 and 5.15,
Lemma 5.16, and Stacks 0GL6. Mathlib searches of all three kinds, the blueprint
ancestor search and the coefficient-projection duplicate search were performed.
Edge cases include identity coefficient maps, the zero ring, arbitrary nonflat
coefficient maps, and varying finite-free ranks. No change record is needed because
no existing public signature or definition changes.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
