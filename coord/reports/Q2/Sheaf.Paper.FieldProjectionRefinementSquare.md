## What changed

Proved `WeilConjectures.FixProjectionCompactification.fieldRefinementProjection` in
`Sheaf.Paper.FieldProjectionRefinementSquare`, preserving its full signature and public import.
Added five private proof imports: IntegralProjectionRefinementSquare,
IntegralStageProjectionStructuralIdentities, RationalProjectionComparisonEquations,
CommonProjectionComparisonEquations, and WeilConjectures.Compactification.CommonRefinement.
All five are used.

Two proved private cancellation helpers reuse the elementary common-refinement argument from
FixProjectionCompactificationComparison without importing that parent. Integral single-refinement
squares give the full integral compactification equation. Combining it with the existing three
integral structural identities supplies the premise of the existing rational coherence transport.
For every finite coefficient field, a datum is constructed from its recorded finiteLevels 0,
higher operations, normalization, and the unchanged closure data. The same argument gives its
rational coherence. Existing common-stage transport then gives common-stage coherence.
The requested two refinement equations are the reversed compactification components.
`identitySquare` and `compactSupportProjectionSquare` agree definitionally.

Updated the item's proof plan to record this reuse of existing transport declarations. Updated
only proof/proof_deps/proof_origin of the unclaimed integral structural-identities node:
its proper-coincidence argument needs integral refinement comparisons only, obtained by the
same common-refinement cancellation, rather than the full four-stage parent comparison.
This removes a dependency back through the parent to this item. Its statement, Lean attachment,
module and existing sorry proof are unchanged. No public interfaces or definitions changed.

Validation: the proof compiled with lcompile.py, exit 0, in 11.3 seconds before the final
comment-only cleanup. No new declarations with sorry, axioms, or data choices were introduced.
The combined statement/proof dependency graph with the two delivered node updates has no
cycle returning to this item. The unit sk-rem-sf-pf-done has no realized statement or steps;
its route is preserved. No source-library declaration was changed.

## Proved and sorry left

Closed one hole:
`WeilConjectures.FixProjectionCompactification.fieldRefinementProjection`
(node lem-sf-field-projection-refinement-square).

Zero holes remain in the delivered Lean module. Zero holes added or split off.
The proof uses the existing named statements integralRefinementProjection,
integralStageProjection_structuralIdentities, compactSupportProjectionCoherence_rational,
and compactSupportProjectionCoherence_common; their existing holes are not closed here.
Every private helper is completely proved.

## No longer needed

No existing imports or modules were removed, and no module is withdrawn or globally pruned.
The item's old direct proof dependencies lem-coef-integral-residue-tor,
def-exchange-projection and def-weil-algebraically-closed-coefficients are now handled by the
existing rational/common transport statements. They remain transitive dependencies and are
not claimed to be globally unnecessary. The integral single-refinement theorem and datum
remain directly used.

The integral structural-identities node no longer needs
lem-fix-projection-compactification-comparison: its proper clause needs only integral
refinement squares and comparison_trans. Its other proof dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The initial item plan predates the existing rational/common projection comparison-equation
transport declarations. Reusing these avoids duplicating their localization and finite-field
representative arguments and adds no split statements.

The structural-identities node's citation of the full parent comparison was unnecessarily
strong: its proper coincidence is entirely integral. Keeping that citation while reusing the
structural identities here would create the DAG cycle structural identities -> parent
comparison -> field refinement -> structural identities. The delivered proof-plan correction
uses the integral single-refinement theorem instead: for a proper f compare any c with the
identity-open compactification through a common refinement, invert only comparison
isomorphisms, and combine with the identity-open counit calculation. No projection map is
inverted. No statement or unit route is weakened.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
