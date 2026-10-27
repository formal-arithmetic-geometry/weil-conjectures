## What changed

Proved `AlgebraicGeometry.coproductModel_represents_sheaf` in
`Sheaf.AlgebraicGeometry.CoproductModelRepresentsSheaf` with its exact existing signature.
Added two proved private helpers: compatible equivalences of sheaves glue on a covering
sieve, and the codiagonal of an arbitrary small coproduct of copies is separated.
The latter uses the open off-diagonal blocks and Mathlib's closed-range criterion for
preimmersions. The main proof descends separatedness and etaleness, constructs the
normalized representation using both sheaf axioms, proves both universal-section
identities, and proves uniqueness by cancellation of an fpqc effective epimorphism.

Updated the existing node's proof, proof dependencies and proof origin to describe this
implementation. Empty index sets and empty bases need no special choice; an index is
chosen only in the conditional surjectivity assertion. No signatures, definitions,
consumer modules or unit routes changed. The proof elaborator options are recorded in
`coord/changes/R4-coproduct-model-proof-elaboration.md`; downstream inspection found
zero current Lean consumers and no adaptation is required.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.coproductModel_represents_sheaf`
(node `lem-sfb-coproduct-model-represents-sheaf`). Added zero holes; zero remain in
the delivered module. Both private helpers are fully proved. No statements split off.

Validation: the final module compiled without warnings using `lcompile.py` (11.4 seconds).
A temporary `#print axioms` check of the proved theorem reported only `propext`,
`Classical.choice` and `Quot.sound`; the check command was removed before delivery.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.EtaleComparison` and the corresponding
proof dependency/tool use `det-pe-morphisms-etale-comparison`: Mathlib already supplies
etale implies weakly etale, so this four-part comparison theorem is unnecessary here.
Its module is not withdrawn, since other parents can still use it.

Removed `lem-weil-pbc-open-immersion-base-change` from proof dependencies: the block
ranges are computed directly with `Scheme.Pullback.range_map`; their openness follows
from continuity of the projections. No structure-sheaf extension-by-zero proof is needed:
the scheme diagonal is a preimmersion, and its closed range suffices.

Removed `def-weil-size-convention` from proof dependencies: all size assumptions are
already explicit in the unchanged statement. Other stated dependencies are retained.
All existing public imports are preserved as the module's importer-visible interface.
No Lean modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The long diagonal/sheaf-map
calculation in the DAG can be replaced by Mathlib's preimmersion criterion. The two
explicit Cech equalizer constructions can be implemented together as gluing compatible
local equivalences on the sieve of sources admitting a lift to V; this proves the same
argument, including its inverse and naturality, with no new unproved statements.
The planned separate etale-comparison dependency duplicated a Mathlib instance.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
