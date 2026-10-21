## What changed

Proved both declarations in `Sheaf.AlgebraicGeometry.DirectImageScalarRestrictionCocycle`,
with the existing theorem signatures and public import unchanged. Uniqueness follows
from the published K-injective normalization, cancellation, and naturality along a
K-injective representative. The cocycle follows from ordinary scalar-pullback coherence,
exact localization, and adjunction mate pasting, followed by inversion and cancellation.

Repaired the return at ba186fbdf: removed the proof-only import of the quarantined
`Sheaf.Paper.FiniteCoefficientDirectImage`. Adapted its needed coefficient-chain
calculations into six fully proved private helpers in the item module. The ordinary
mate identity comes from the already imported fixed-scalar comparison module; the generic
mate calculation uses the adjunction hom equivalence directly. No quarantined source is
restored, deleted, or changed. No additional module, definition, statement, instance,
or exported attribute is changed. Proof-only `import all` of the fixed-scalar comparison
provides its hidden mate construction and its proved underived mate identity.

Updated the node's proof, proof dependencies and proof origin to describe the actual
self-contained coefficient-pasting calculation.

Validation: `lcompile.py` compiled the complete repaired proof without errors or warnings
in 11.9 seconds. Temporary `#print axioms` checks for both theorems reported exactly
`propext`, `Classical.choice`, and `Quot.sound`; the diagnostic commands were removed.
Both original theorem signatures were compared verbatim and are unchanged. Every direct
import has a current source file. The updated proof dependencies equal the union of
the proof steps' uses. Delivery preflight checks the final packet again.

## Proved and sorry left

Closed 2 of 2 holes:

- `AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImage_unique`
  (`lem-sf-direct-image-scalar-restriction-cocycle`).
- `AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImage_cocycle`
  (the same node).

Holes added: zero. Holes left in the item: zero. Split-off statements: zero.
All six private helpers are proved without holes.

## No longer needed

Removed these direct proof imports from the original item:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the public comparison
  already supplies the operations used by the signatures.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: the existing
  module-valued sheaf K-injective resolution instances suffice directly.
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`:
  `lem-sf-kinjective-derived-map-computation` is unnecessary for the mate proof route.
- `Sheaf.CategoryTheory.NormalizedDerivedComparisonComposition`:
  `lem-sf-normalized-derived-comparison-composition` is unnecessary because the
  specified comparison is already an adjunction mate.

Also removed the returned packet's `Sheaf.Paper.FiniteCoefficientDirectImage` import
and its `lem-coef-finite-direct-image` proof dependency: the elementary coefficient
chain is now proved privately in this item, using the existing fixed-scalar API and
exact-localization API. No statement or declaration of the quarantined module is
withdrawn. The two generic normalized-resolution nodes are also absent from the revised
proof dependencies. The site, operation, and scalar-restriction definition nodes remain
statement dependencies; redundant explicit proof-dependency entries are removed.

This packet withdraws no modules and makes no claim of global unreachability.

## Where the brief, the DAG or earlier work was wrong

The earlier packet imported a module whose compiled private helpers were accessible
but whose source had since been quarantined. A successful compile therefore did not
ensure that the dependency could land. This repair removes that dependency entirely
and carries the necessary proved calculations in the item itself.

The original plan is valid, but transporting to separately chosen generic right derived
functors is unnecessary: the published comparison is the inverse of an actual adjunction
mate. Pasting that mate gives the cocycle with the actual canonical associators. No
preservation of K-injectives, properness, boundedness, or constructibility is assumed.
Identity coefficient maps, the zero ring, and non-flat coefficient maps introduce no
extra hypothesis: the argument uses only exact scalar restriction and adjunction laws.

The unit `sk-def-sf-operations` has no realized statement or proof-step nodes to bypass.
No target or unit route changes. No new nodes or forced adaptations.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
