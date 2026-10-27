## What changed

Completed the Lean proof of
`WeilConjectures.PurityFiniteSetting.varyingDimension_dualizing_inverse`
from two strictly smaller named steps. `FiniteClopenCommonExceptional` states
simultaneous normalized restriction records sharing their three global functors.
`SmoothClopenComponentInverse` states existence of integral, rational and
common-stage inverse pairs on one pure-dimensional smooth component, for the
actual component functors of an arbitrary normalized record. Neither lemma
asserts the finite-partition assembly or its prescribed-map equations.

The main proof derives pure smoothness on each labelled locus, transports the
component inverse pairs along the normalized unit comparisons, and applies the
existing proved categorical gluing helper at each coefficient stage. Added proved
private helpers establish integral finite-Tor invariance under isomorphism and
transport of both inverse maps. The uniform support and Tor interval assertions
follow from `finiteClopen_integral_bounds`, retaining the same interval at every
positive reduction. The geometric partition and finite-coefficient proof retain
their statements and proofs.

A source-overlay check exposed a missing private proof import in the unclaimed
`Sheaf.Paper.FiniteClopenDerivedDecomposition`: its existing instance-exclusion
block names `ClopenScalar.derived`, `sheafify`, and `locallyBijective`, but the
smaller support import no longer exposes their owner. Added the direct private
import `Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarData`; all public
signatures, definition bodies, proofs and public imports in that dependency
are unchanged. Record:
`coord/changes/P4-clopen-derived-scalar-proof-import.md`.

Removed the item's unused public import of
`Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and added only private
imports for the two new proof lemmas. Its only direct consumer,
`Sheaf.Paper.PuritySectionInvariantIntrinsic`, keeps the same finite inverse API.
Record: `coord/changes/P4-varying-dimension-public-import-pruning.md`.

The unit `sk-def-purity-conv` has no realized proof steps to bypass. This delivery
keeps its route: dimension partition, actual exceptional restriction, smooth
pure-dimensional local inverse, and clopen assembly. New statement edge cases
were checked mathematically: empty cover and empty component, singleton cover,
dimension zero, nontrivial rank-one monodromy, and arbitrary finite coefficient
stage. No index is selected from the possibly empty component family.

Final source-overlay validation passed in import order: the common-choice lemma
(7.9 s), the repaired decomposition dependency (cached; previously 46.5 s),
the pure-component lemma (8.9 s), the item (25.1 s), and its unchanged direct
consumer `PuritySectionInvariantIntrinsic` (29.4 s). The consumer was copied
only for validation and removed from the sandbox afterwards. All delivered
Lean lines are at most 100 characters.

## Proved and sorry left

Original item holes: 1. Closed in the item: 1,
`WeilConjectures.PurityFiniteSetting.varyingDimension_dualizing_inverse`
(node `lem-pur-varying-dimension-dualizing-inverse`). Remaining item holes: 0.
The original theorem is decomposed, rather than claimed as a proof independent
of new holes. Added holes: 2, both public named theorems with complete proof plans:

- `WeilConjectures.PurityFiniteSetting.finiteClopen_common_exceptional`
  (`lem-pur-finite-clopen-common-exceptional`), in
  `Sheaf.Paper.FiniteClopenCommonExceptional`.
- `WeilConjectures.PurityFiniteSetting.smooth_clopen_component_inverse`
  (`lem-pur-smooth-clopen-component-inverse`), in
  `Sheaf.Paper.SmoothClopenComponentInverse`.

The adapted dependency retains its one pre-existing hole,
`WeilConjectures.PurityFiniteSetting.finiteClopen_constructible_equivalences`
(`lem-pur-finite-clopen-derived-decomposition`). It is not added or moved by this
delivery. The delivered Lean files thus contain 3 holes total, of which 2 are new;
net holes closed minus holes added for this decomposition is -1. No definition
contains a hole and no axiom is added.

## No longer needed

Removed direct import:
`Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.
It remains used transitively by exceptional-system proofs, so no whole module
is claimed globally pruned.

Removed direct proof-dependency edges from the item to
`lem-pur-finite-setting-comparison-hypotheses`, `thm-asd-smooth-tensor`,
`def-weil-exceptional-inverse-image`, `lem-pur-shifted-line-site-inverse`,
`lem-pur-complete-residue-line-inverse`, and
`def-weil-derived-pullback-tensor-hom`. Their required local arguments now belong
to the pure-dimensional component lemma or the existing finite inverse lemma;
definition dependencies stay recorded. These nodes are not claimed globally
unnecessary. Retained the finite inverse, exceptional finite restriction,
geometric permanence and clopen decomposition dependencies actually used by the
item. Pruned the now-obsolete direct maintainer tool-use entries for
`lem-pur-finite-setting-comparison-hypotheses`, `thm-asd-smooth-tensor`, and
`lem-pur-shifted-line-site-inverse`, retaining the order of the other approvals.
Their arguments remain needed under the relevant local inverse nodes.
No module is withdrawn, and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The current server queue classifies this as a proof item with one hole; the
historical build-error file names unavailable imports, while the restored source
and initial published-artifact compile succeed. That initial compile was not
used as evidence that the newer source-overlay dependency chain was healthy.
The subsequent overlay exposed the dependency's missing scalar-data proof import,
recorded and repaired above.

The previous integral proof plan asked the finite-clopen exceptional restriction
statement for simultaneous literal equality of global functors, but it asserts
only separate existential records for each component. The new common-choice
lemma isolates that additional construction. Also, finite smooth tensor
invertibility alone does not provide the shifted etale residue-line presentation
needed by `completeResidueLineInverse`; the pure-dimensional component lemma's
proof explicitly obtains it from smooth tensor duality and actual finite
exceptional realization, then applies the existing complete-residue inverse
theorem and coefficient operations. For arbitrary normalized records it first
uses the unique comparison of integral compact-support right adjoints with the
canonical normalized exceptional construction. The canonical reduction system,
rather than an arbitrary inverse-limit presentation, supplies the residue
comparison. No statement was weakened.

The new component proof uses the same smooth tensor, finite-setting comparison,
site-comparison and uniqueness-of-adjoint tools as the source route. The two new
nodes declare their generic cross-unit tool uses under `split_report.tool_uses`,
with reasons for the independent reader. No maintainer `tool_uses` approval is
added by this delivery; the reader records any approved uses. These tools do not
replace the convention unit's route.

## New nodes

`lem-pur-finite-clopen-common-exceptional`, in
`dag/nodes/sec-smooth-purity/lem-pur-finite-clopen-common-exceptional.json`, is the
simultaneous choice of normalized comparison records for an arbitrary finite
clopen partition. It needs no smoothness and asserts no invertibility. The
proof plan fixes one global strict adjoint and its realizations before constructing
the component comparisons; all global-functor equalities then hold literally.

`lem-pur-smooth-clopen-component-inverse`, in
`dag/nodes/sec-smooth-purity/lem-pur-smooth-clopen-component-inverse.json`, is the
pure-dimensional, single-component integral/field inverse calculation. Its
proof plan uses a shifted residue line, the existing complete-residue inverse
theorem, and the normalized rational/common-stage operations. It does not glue,
assert a common global record, or prescribe components of global inverse maps.

Both modules compiled as statements in the first set check. Their Mathlib search
records come from actual LeanFinder, Loogle, source grep and LeanSearch queries;
no match was found. Blueprint-wide searches for clopen comparisons and dualizing
inverses found no existing node with either strengthened interface. The two new
nodes have no path back to their parent, and all their direct dependency ids exist.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 INFRA.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteClopenCommonExceptional": "d1c2d63baeaa1eee1bd69e16df2eb4db717743ea", "Sheaf.Paper.FiniteClopenDerivedDecomposition": "9e3a2103099d9d04aecdf49a810e68c2025b46ce", "Sheaf.Paper.SmoothClopenComponentInverse": "bdca158c4b8f6c3cddd3243d110a224b221434b1", "Sheaf.Paper.VaryingDimensionDualizingInverse": "b76346912b6b41dc747a104b368dfa3b09ca165a"}, "results": {"Sheaf.Paper.PuritySectionInvariantIntrinsic": {"hash": "29116a45c70b1391780b0479a72d32a46baf322b", "status": "INFRA"}}, "seconds": 76, "time": "2026-10-28T00:55:47+0800", "transitive": 0, "version": 1}
```

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
