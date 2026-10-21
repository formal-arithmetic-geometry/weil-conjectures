## What changed

Replaced the hole in `WeilConjectures.coefficientExtensionReductionSkeleton_exists`
by a composition of finite scalar association, strict normalized representatives,
projection-normalized Roos comparison, and the existing normalized descent theorem
`integralScalarExtensionWellDefined`.

The following new modules supply the argument:

- `CoefficientExtensionFiniteAssociation`: ordinary adjoint uniqueness gives the balanced
  finite tensor associations, including the prescribed formula on tensor sections.
- `CoefficientExtensionStrictRepresentatives`: isolates the strict normalized quotient
  model, its evaluated universal comparison, and normalization. Its named theorem is
  the remaining hole. Private proved constructions provide the ordinary scalar cone,
  its additive strict-system functor, and its finite evaluation isomorphisms.
- `CoefficientExtensionRestrictedTower`: identifies the exact restriction of a strict
  representative with the published completed-coefficient tower. The actual section
  transition equation is used to prove equality of the tower maps.
- `CoefficientConstantTowerRoosComparison`: constructs the derived-limit/Roos comparison
  through functorial K-injective resolutions and proves every projection equation.
- `CoefficientExtensionRepresentativeRoos`: combines these comparisons and proves the
  projection formula by naturality, without identifying arbitrary triangle fillers.

Moved the existing model interfaces and predicates verbatim to
`CoefficientExtensionReductionData` to avoid an import cycle. The item publicly
reexports that module and keeps all four original public imports. The change record
`coord/changes/coefficient-extension-reduction-interfaces.md` lists declarations and
consumers. No source-library module or target statement is changed.

Validation: `lcompile.py --all` compiled all seven delivered modules. The
representative Roos proof and final assembly compiled in 20.0 and 20.7 seconds,
respectively. Temporary profiling has been removed; the delivery command performs
the final compile, consumer and axiom checks before pushing.

## Proved and sorry left

Original hole closed:
`WeilConjectures.coefficientExtensionReductionSkeleton_exists`
(`stage3-pur-reduction-skeleton-exists`). The item itself has zero remaining holes.

One hole added:
`WeilConjectures.coefficientExtensionStrictRepresentative_exists`
(`stage3-pur-extension-strict-representatives`), in its own module. It asserts only
strict normalized quotient representatives, not completion, the Roos projection
formula, descent, or invertibility of the completion counit. The independently proved
finite association and Roos arguments supply those other parts.

This is a decomposition: one original hole closed and one strictly smaller hole added,
with no net hole reduction claimed. The original hole is reduced, not an axiom-free
proof of the complete mathematical result.

The new public theorems `coefficientExtensionFiniteAssociation_exists`,
`coefficientExtensionRestrictedTower_exists`, `coefficientConstantTowerRoosComparison`,
and `coefficientExtensionRepresentativeRoos_exists` have complete Lean proofs.
The moved interfaces contain no holes and introduce no witness choices.

## No longer needed

No existing module is withdrawn, and no original public or private import is removed
from the item. There is no global pruning claim.

Removed redundant proof imports of
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle` and
`Sheaf.Paper.IntegralOperationsWellDefined` from the new representative-Roos module;
the interfaces it uses are supplied by its remaining imports. These modules remain
needed elsewhere and are not withdrawn.

The skeleton node no longer directly calls the K-flat resolution and change-of-rings
steps: its dependencies now name the finite association, strict representative,
representative Roos comparison and normalized descent actually used. K-flat resolution
and change of rings remain needed by the strict representative node. Exact countable
products and the strict Roos ingredients remain needed by the proved completion
comparison. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first packet omitted LeanSearch (Loogle and LeanFinder are one kind) and the
node attachment for the relocated interface module. Both metadata omissions are
repaired; the new definition node records the existing coherent model interface.

The previous skeleton node treated strict representatives, normalized systems, and
completion projection as one construction step. The new dependency route distinguishes
its strict quotient input from the Roos and descent arguments. The mathematical
statement of the original node and all existing declaration signatures are preserved.

The ordinary `integralScalarReduction` implementation was updated in the shared tree
during this session. The finite association and ordinary strict-system comparison use
its current concrete-model equality and natural map equation, rather than assuming
that the old existence witness is still its definition.

A check of the current published dependency graph and of this packet found the
same pre-existing cycle:
`lem-pc-ring-hom-extension-differential` →
`lem-pc-ring-hom-extension-differential-adjacent` →
`lem-pc-ring-hom-extension-differential`. It is reachable from the original published
skeleton as well as this packet. Neither node is edited here; the maintainer should
reconcile that planned dependency cycle separately from the Lean import graph.

Exploration of a separate ordinary evaluation right adjoint and a functorial completion
model is not part of this delivery; no unused exploratory module is submitted.

## New nodes

`stage3-pur-extension-reduction-data` attaches the extracted interface module to the
existing generic coherent model record. It records a verbatim relocation, with no
new existence claim or hole. The five result nodes also include their separately
performed LeanSearch queries; Loogle and LeanFinder count as one search kind.

`stage3-pur-finite-extension-association` records the proved ordinary finite association
and its actual balanced section formula.

`stage3-pur-extension-strict-representatives` records the remaining strict normalized
quotient-model theorem with its source and full natural-language proof. Its conclusion
is strictly part of the original skeleton argument.

`stage3-pur-extension-restricted-tower` records the proved strict tower identification,
including compatibility with the specified successor transitions.

`stage3-pur-canonical-tower-roos-comparison` records the proved inverse-limit/Roos
isomorphism normalized by every canonical projection.

`stage3-pur-extension-representative-roos` records the proved assembly of that Roos
comparison with the given strict representative and its projection equation.

The blueprint search for coherent scalar extension and quotient scalar found no exact
existing statement. The Roos search found general derived-limit statements, whereas
the new nodes retain the specified complex-level comparisons and their projections.
The inherited blueprint ancestor is `def-weil-frobenius-coefficient-twists`, through
`stage3-pur-reduction-skeleton-exists`.

Change record: `coord/changes/coefficient-extension-reduction-interfaces.md`.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
