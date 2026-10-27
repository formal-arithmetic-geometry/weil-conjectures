## What changed

Replaced the hole in `WeilConjectures.CompletionUnit.canonicalModels` by a construction
from two strictly smaller obligations and the existing coefficient-calculus existence
theorem. The original theorem signature, model structures and all their fields are unchanged.

The item now proves the termwise-limit comparison by constructing its limiting cone
and using uniqueness of limits. It constructs the actual constant-tower derived unit
from the existing homotopy-level right-derived unit, proves the specified K-injective
normalization and its universal right-derived property, and obtains the normalized
Roos isomorphism from `strictRoosDerivation` and uniqueness of right derived functors.
The final proof assembles all fourteen fields of `DerivedModel`; the system-unit
composition equation follows from its explicit construction.

New proof imports: `CompletionUnitOrdinaryAdjunction`,
`CompletionUnitDerivedAdjunctionComparison`, `StrictRoosDerivation`,
`ProEtaleProductsExact`, and `RingedToposDerivedPushforwardComposition`.
The first two modules each state one remaining theorem. `systemLimitUnit` in the
second is a real composite natural transformation; it chooses no data from a hole.
No existing public definition or signature was changed, so no consumer adaptation
or change record is required. All three modules were checked through `lcompile.py`;
the item compiled in 12.6 seconds before its final `simp only` linter cleanup.
The delivery command reruns compilation and the axiom probes for the final packet.

## Proved and sorry left

Closed the original hole in `WeilConjectures.CompletionUnit.canonicalModels`
(node `lem-trf-completion-unit-canonical-models`). The item contains zero textual holes.

Added two named holes, each in its own module:

- `WeilConjectures.CompletionUnit.ordinaryModel_exists`, node
  `lem-trf-completion-unit-ordinary-adjunction`: the ordinary tensor adjunction alone,
  without a derived coefficient calculus or any derived comparison.
- `WeilConjectures.CompletionUnit.derivedAdjunctionComparison_exists`, node
  `lem-trf-completion-unit-derived-adjunction-comparison`: comparison of the derived
  adjunction for a given ordinary model and given normalized tower unit with a given
  coherent calculus. It asserts no existence of those inputs and no Roos comparison.

This is a decomposition: one original hole closed and two holes added. For these
three declarations, closed minus added is -1; the packet's textual hole count increases
by one. The maintainer's ledger determines the full change in the target import closure.
This is not a completed proof without dependencies.
The lower statements have full source-based proof descriptions. The tower comparison,
canonical-unit normalization, right-derived universal property and normalized Roos
comparison are proved directly in the item rather than deferred again.

Edge cases checked in the mathematical statements: empty W, zero modules and complexes,
level zero (positive exponent one), arbitrary complex degrees, and non-K-flat Q in the
chain-map Hom equation. No boundedness, tensor-exactness or assumption that restriction
preserves K-injectivity is introduced. The tower unit is normalized on K-injectives;
its universal property alone would permit a scalar rescaling and would not suffice
for the fixed finite-evaluation normalization.

## No longer needed

No existing import was removed and no module is withdrawn. The item now directly uses
`lem-weil-strict-roos-derivation` in place of the larger
`lem-weil-strict-roos-comparison`; the latter is not needed for this construction.
The direct proof no longer invokes the sequence-site equivalence, sequence derived
adjunction, projected counit theorem, resolving-adjunction theorem or K-injective
resolution theorem. They remain dependencies of the two smaller obligations, so this
is no claim of global pruning of those modules.

The updated node records exactly the smaller obligations and the generic results
actually used by the proof. The unit route is retained; neither the unit statement
nor its realized steps are changed.

## Where the brief, the DAG or earlier work was wrong

No false statement or route departure was found. The general sequence-site declarations
are not a direct one-line construction of the fixed coefficient `OrdinaryModel`:
normalizing its actual scalar extensions and transporting the strict-system interface
are still necessary. The new ordinary obligation records precisely that transport.

The normalization of the constant-tower unit must use the underlying ring of
`completedIntegralCommRingSheafUnrestricted`, which is the ring used by
`scalarReductionSource`. Its separately constructed RingCat inverse-limit sheaf
cannot be substituted by definitional equality. Likewise a chosen limit of complexes
requires an explicit universal comparison with the termwise limit; they are not
definitionally identical. The proof respects both distinctions.

## New nodes

`lem-trf-completion-unit-ordinary-adjunction` is the ordinary part of original step 1,
following Stacks 03D7 and the sequence-site construction. It is independent of the
chosen coherent derived calculus. Its full proof plan retains every quotient transition
and the sectionwise tensor-unit formula.

`lem-trf-completion-unit-derived-adjunction-comparison` records original steps 2--3:
normalize right-derived composition and compare left adjoints using the actual Hom
bijections, then identify finite comparisons by counit mates. The normalized tower unit
and its degreewise comparison are explicit hypotheses, excluding arbitrary rescalings.
Both nodes retain the item's chapter, unit and blueprint ancestry; the three Mathlib
search types and the whole-blueprint duplicate search found no direct specialized match.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
