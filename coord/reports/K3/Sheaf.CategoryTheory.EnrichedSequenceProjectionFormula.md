## What changed

Filled `ordinarySectionsIso_exists`, `sectionsH0Comparison_exists`, and
`ordinaryEvaluationIso_exists`, preserving their signatures and all existing definitions.
The first comparison uses the limit's section equivalence and the module unit-Hom
identification. The second follows from uniqueness of right derived functors, and its
uniqueness is checked on K-injectives. The third is pushforward along the equal vertical
ring maps and is identity on sections.

Implemented the six-step enriched projection argument. Private proved categorical helpers
establish projection transposition, uncurrying under evaluation, the inverse scalar-Hom
comparison formula, and the projected counit. The supplied strict derived pair is compared
with the pair in `coefficientSequenceSectionsLimitComparison` using universal derived
units; this also transports both normalization equations and the finite projection identity.

The final degree-zero calculation is reduced to the independent single-coefficient-map
result `scalarHomZeroCompatibility`. Its statement has no sequence, limit, system
normalization, or projection input. The main theorem combines it with the categorical
projection/counit formula. Added its separate module and DAG node and updated the item's
proof route. No existing statement, public import, or definition was changed. The local proof
elaboration commands are documented in
`coord/changes/enriched-sequence-proof-elaboration.md`; no consumer adaptation is needed.

Validation: the full item module compiles on the project server with no errors or
warnings (58.5 seconds). The new scalar compatibility module also compiles. The
four original theorem signatures were compared verbatim with the shared source.
Local irreducibility attributes and a generic derived-unit conversion prevent
expensive unfolding of the comparison definitions; the compile limit is unchanged.

## Proved and sorry left

Original module: four holes. Closed:

- `SheafOfModules.EnrichedSequenceProjection.ordinarySectionsIso_exists`.
- `SheafOfModules.EnrichedSequenceProjection.sectionsH0Comparison_exists`.
- `SheafOfModules.EnrichedSequenceProjection.ordinaryEvaluationIso_exists`.
- `SheafOfModules.EnrichedSequenceProjection.enrichedSequenceProjectionFormula`, by a
  complete combination of the existing statements and one strictly simpler result.

The first three are proofs. The fourth is a decomposition, not a fully discharged
mathematical proof. Added one named hole:
`SheafOfModules.ScalarHomZero.scalarHomZeroCompatibility`
(`lem-coef-scalar-hom-zero-compatibility`). Its proof body is exactly `by sorry` and its
docstring states the representative argument. There are zero holes in the item module
and one in the delivery. Net holes closed: three.

## No longer needed

Removed these private proof imports:

- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`.
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.

Removed the four corresponding obsolete top-level tool approvals from the item node.
The item uses the supplied normalized adjunctions, closed structures and comparison
isomorphisms directly. Their existence theorems are not called again. Their statements
and modules are preserved; no module is withdrawn and no whole-library pruning is claimed.
The existing public imports remain verbatim because they form the item's statement API.
The proof route also no longer invokes the existence statements
`lem-coef-sequence-projection-derived-adjunction`,
`lem-coef-sequence-pushforward-limit-projections`, `lem-pur-rhom-global-sections`,
`lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-sf-ringed-derived-closed-symmetric-monoidal`,
`lem-sfb-dc-hom-scalar-adjunction`, or
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` again. Their supplied normalized data
are enough for the formal projection argument; the scalar zero-cycle normalization has
its own explicit node. This does not remove the statement dependencies or any imports
needed by other declarations.

## Where the brief, the DAG or earlier work was wrong

The declared scalar internal-Hom theorem does not itself identify its H0 action with the
specified 08JA zero-cycle equivalence. That compatibility is an independent representative
calculation, now isolated by the new node; it is not inferred from existence or naturality
of unspecified isomorphisms. The finite projection and counit formulas, on the other hand,
follow formally from the given unit equation and naturality and need no new system lemma.

Checked the new statement against identity coefficient maps, zero inputs, the empty site,
and a nonflat coefficient map: its formulas are ordinary derived scalar adjunction formulas
in all cases. It makes no assertion that restriction preserves K-injectivity or that an
arbitrary varying-coefficient evaluation is K-injective. Both comparison directions are
fixed by their unit equations; no arbitrary isomorphism is accepted as normalization.

## New nodes

`lem-coef-scalar-hom-zero-compatibility`:
`lean/Sheaf/CategoryTheory/ScalarHomZeroCompatibility.lean`, declaration
`SheafOfModules.ScalarHomZero.scalarHomZeroCompatibility`. This is the single-ring-map
scalar-Hom/zero-cycle compatibility from Stacks 07A6, 08J9 and 08JA, extracted from step 6.
It retains all representative normalization hypotheses and has no inverse-limit content.

Change record: `coord/changes/enriched-sequence-proof-elaboration.md`.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
