## What changed

Extracted the original public data declarations, byte-for-byte, into
`Sheaf.Paper.GlobalVerdierDualityData` and publicly re-exported them from the original module.
No existing signature or definition changes. Added `StageMaps`, `StageMaps.toConclusion`, and
`NormalizedData` to express the geometric construction before exchange invertibility.

Reduced `WeilConjectures.GlobalVerdierDuality.global_verdier_duality` to the separate
identity-normalization lemma. The main proof constructs natural represented-Hom bijections
from the two tensor-Hom adjunctions, projection, exceptional adjunction, and ordinary adjunction.
It proves their naturality, applies the library's proved `isoOfNaturalHomEquiv`, and checks that
the resulting hom is exactly the specified epsilon. It also proves both tensor-unit evaluation
identities and builds the constant case from the same exchange component.

The unit's route remains: the theorem explicitly applies `VerdierExchange.verdier_exchange`
at the structure morphism. Identity normalization takes this assertion as input. All signed
shift structures, canonical exceptional q comparisons and coefficient-unit equations are kept.
This is a decomposition, not a net hole reduction.

Validation: all three sandbox modules compile through the project compile server; the main
module compiles cleanly. The original theorem signature is byte-identical. The import-direction
check permits the normalization dependency, and all four node proof-dependency lists equal
the union of their proof-step uses.

## Proved and sorry left

Closed original hole:
- `WeilConjectures.GlobalVerdierDuality.global_verdier_duality` (both existing global-duality nodes).

Proved private helpers: `transpose_left`, `transpose_symm_left`, `transpose_symm_id`,
`unitAdjunction`, `closedUnitIso`, `closedUnitIso_hom`,
`closedUnitIso_inv`, and `epsilon_isIso`. Proved definition `StageMaps.toConclusion` promotes the specified map
using the componentwise invertibility supplied by the main proof.

Added and remaining hole:
- `WeilConjectures.GlobalVerdierDuality.identity_normalization`, node
  `lem-sf-global-identity-normalization`, in `Sheaf.Paper.GlobalIdentityNormalization`.
  This is the geometric identity/counit transport construction and its ring, unit, scalar and
  signed-shift equations. It asserts no inverse to epsilon and no constant-object duality.

Original holes closed: 1. New holes: 1. Item module holes left: 0. Delivery holes left: 1.
No data definition contains sorry or chooses an arbitrary witness of an unproved existence.
The construction-only normalization result remains unproved: its full counit/scalar transport
is not present in the available interfaces. The delivery proves the strictly separate
invertibility and constant-object portions of the argument.

## No longer needed

Removed proof imports from the original module: `Sheaf.Paper.FiniteTorStability`,
`Sheaf.Paper.PointFibreDerivedTensor`, `Sheaf.Paper.PointFibreEquivalence`,
`WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise`, and
`Sheaf.Paper.PointSectionsDerivedReduction`.

The point-category statement already uses literal internal Hom at the point. No fibre-functor
transport is needed in the combining Lean proof. Its old proof-route dependencies
`lem-weil-point-fibre-equivalence`, `lem-sf-point-fibre-derived-tensor`,
`lem-pod-point-sections-derived-reduction`, and `lem-weil-point-sections-scalar-extension`
are not direct dependencies of the new main proof. Preservation/closed-model facts remain
needed by identity normalization; the new node records those retained inputs.
The original public imports are retained verbatim, including the explicit Verdier exchange
unit-route import. The existing
`thm-sf-ctf-stability` tool approval is retained because identity normalization still needs it. Removed obsolete top-level tool approvals for the four point-fibre/sections lemmas above and
`def-pur-derived-internal-hom`; the latter is replaced by the abstract adjunction calculation.
No module is withdrawn,
no source-library declaration is removed, and no globally unused module is claimed on the
basis of this local route alone. Existing unit/target statements remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned specialization is mathematically valid but the Lean interfaces do not specialize
by reflexivity: `VerdierExchange.Package` uses arbitrary normalized Systems for the point
identity and composite structure map, while the item requires the literal identity operation
and a reflexive dualizing comparison. Its scalar records also use existential normalized
scalar functors, whereas the item pins the supplied System's scalar functors. These require
counit-normalized transport with coefficient coherence.

`StageData` stores objectwise projection isomorphisms without a projection-naturality field.
Objectwise invertibility alone does not justify the represented-Hom argument. `NormalizedData`
retains precisely that naturality equation, and the main Lean proof uses it explicitly.
The remaining lemma's docstring spells out the geometric source of that equation and all
normalizations. No statement is marked false and no original hypothesis is removed.

## New nodes

`def-sf-global-normalized-construction` records the construction-only interface and its
proved promotion after invertibility. `lem-sf-global-identity-normalization` records the genuine
identity-normalization part of the source argument, with a complete natural-language proof.
Edge cases checked: tensor-unit duality uses no nonzero or invertibility-of-coefficients
assumption, so applies to zero objects and finite rings of every positive level. The Hom-bijection
argument uses only the stated adjunctions and projection naturality; it treats all four coefficient
stages uniformly, with no field-to-finite reduction. The normalization statement needs only a
separated finite-type structure map, so it covers both geometric alternatives and empty X.
The additional LeanSearch query on the right adjoint of tensoring with the unit returned
`rightUnitorNatIso` (used in the main proof) and unit-closedness facts, but no geometric
normalization theorem.
Blueprint searches `identity normalization` (one match, `pur9-rg-def-phi`) and
`point verdier` (zero matches) were checked against this statement: none supplies the
construction-only identity/counit transport
on the published four-stage System. The nearest ancestor is `sk-thm-sf-global-duality`.
`lem-sfb-projection-internal-hom-formal` is used only for its already proved generic Yoneda
helper `isoOfNaturalHomEquiv`; it does not replace the unit route.
Both existing global-duality nodes now follow the written Lean proof. Change record:
`coord/changes/T2-global-verdier-data-extraction.md`.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
