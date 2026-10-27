## What changed

Replaced `AlgebraicGeometry.Scheme.sfbPerfectModel_complex_comparison` by an explicit
cochain isomorphism, preserving its statement, universes and public import. All added
helpers and proof imports are private to this module. Private instances pin
sheafification and local-bijectivity detection to the required universe, by Mathlib's
transport across an equivalent small site; this avoids a transitive instance whose
additional universe cannot be inferred from a maximum.

The proof first compares module sheafification under `AsSmall.down`. Its underlying
abelian-sheaf map is proved to be Mathlib's canonical
`pushforwardContinuousSheafificationCompatibility`, hence invertible. The comparison
with constant module realization retains the scalar action, using the existing
`moduleSheafificationComparison` and the equation for the constant-ring units.
The ordinary scalar extension comparison uses the recorded object/map equalities of
`completedAdicChangeData`, the sectionwise tensor formula, and the sheafification
comparison. A generic faithful-functor lifting lemma and the existing natural
sheafification isomorphisms avoid repeatedly reducing the full scalar-action
constructions while checking naturality. The completed coefficient-map square is proved after every finite
projection. Finally, the existing scalar-extension adjunction and composition
comparison transport that square, and naturality gives the differential equations
for `HomologicalComplex.Hom.isoOfComponents`.

Expanded the item's DAG proof into these explicit steps without changing its statement,
statement dependencies, proof dependencies, unit attachment or Lean declaration.

Searched by `leanfinder`, `loogle` and Mathlib `grep` through `msearch.py`, and by local
`rg`. No existing declaration compared these two complete realizations. The proof reuses
Mathlib's sheafification comparison and adjunction uniqueness, together with the
project's already proved module-sheafification and scalar-composition APIs.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.sfbPerfectModel_complex_comparison`
(node `lem-sfb-perfect-model-complex-comparison`), the item's one original hole.

Added holes: none. Split-off statements: none. Sorries left in delivered Lean files: none.
All newly added private helpers have complete proofs or explicit constructions.

The full proof passed remote single-file compilation (42 seconds with profiling).
Removed the profiling and checkpoint commands for delivery. Checked that the original
public theorem signature is unchanged and every delivered Lean line has at most
100 characters.

## No longer needed

None. No import, node, module or declaration is withdrawn. The four recorded proof
dependencies remain in use; the complete-reduction module supplies the actual model
and its scalar-composition API, without applying its completeness theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The comparison is entirely before
localization. No Noetherianity, finite generation, boundedness, perfectness or local
completeness assumption enters the proof. The constructions use only sheafification,
the actual positive quotient limits, ordinary tensor and naturality, and consequently
retain the zero-ring, zero/unit-ideal, empty-scheme and unbounded-complex cases.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
