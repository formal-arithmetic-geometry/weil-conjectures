## What changed

Only the assigned Lean module and its own DAG node change. The delivery proves the
identity normalization, exchange refinement, and compositor refinement clauses without
changing any existing signature, definition, attribute, or public import.

The exchange proof transports the existing compactification-independent base-change
map to both pairs of compactifications and takes mates of the resulting refinement
square. The compositor proof uses the existing every-tower formula and comparison
cocycle, then conjugates and expands the horizontal comparison. The identity proof
descends the ordinary sum-adjunction counit equation using exact-derived pasting and
uses the canonical graph identity normalization and the existing rho refinement law.
All new helpers are private and proved. The added proof imports are
Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence,
Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition, and
WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation. The latter two expose
the existing localized exact-adjunction and derived identity comparison APIs.

## Proved and sorry left

Seven holes were present initially. Three holes are closed, with no holes added:

- AlgebraicGeometry.Etale.etaleNormalizedMates_identity
- AlgebraicGeometry.Etale.etaleNormalizedMates_exchange_refinement
- AlgebraicGeometry.Etale.etaleNormalizedMates_composition_refinement

Four existing holes remain, all with node
lem-pur-etale-normalized-mates-composition-pasting and their original source and proof
docstrings:

- AlgebraicGeometry.Etale.etaleNormalizedMates_composition
- AlgebraicGeometry.Etale.etaleNormalizedMates_baseChange_pasting
- AlgebraicGeometry.Etale.etaleNormalizedMates_composition_restriction
- AlgebraicGeometry.Etale.etaleNormalizedMates_openRestriction

The previously proved declarations are preserved. No split-off theorem or new axiom
is introduced. The required server single-file compiler passed in 35.6 seconds.
The delivery tool runs the remaining preflight and independent declaration probes.

## No longer needed

None. No imports, nodes, modules, or approved tool uses are withdrawn. The dependencies
of the remaining composition and restriction arguments stay in the DAG. The added
proof imports are used by identity normalization.

## Where the brief, the DAG or earlier work was wrong

The composition clause of quasifiniteCompactSupportExact controls existential
comparison families c_h, c_e and c_he. Its statement does not identify these families
with canonicalEtaleCompactSupportComparison. Consequently the direct specialization
suggested in Step 1 still needs an argument identifying the actual graph-normalized
comparisons with those families, or a direct graph-composition normalization argument.
The main composition hole is preserved; no statement is weakened or marked false.

The new proof dependency lem-asd-compact-support-graph-coherence supplies the identity
normalization of the very graph comparison used in the statement. It is used as a
comparison-coherence input and does not replace any unit-level proof route.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
