## What changed

Proved `AlgebraicGeometry.Scheme.proetale_site_properties`, with its exact existing
signature, in `Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties`.

The unit-route theorem `weaklyEtale_stability` supplies the weakly etale
base-change and composition instances. Unfolding `ProEt.precoverage` exposes Mathlib's comap instances for isomorphisms,
composition and base change. `Precoverage.toPretopology.transitive` proves the
project's bind-composition clause. Actual pullbacks and the base-change instance
prove the quantified pullback-covering clause. Mathlib supplies subcanonicity and
essential smallness in universe `u + 1`. The final witness consists of `SmallModel`,
its induced topology, and `Equivalence.sheafCongr` for `Type (u + 1)` sheaves.

Updated the existing node's proof, proof dependencies and proof origin to describe
these APIs. No new declaration, signature change or definition change is needed.
The unit's covering-stability, fpqc descent and small-site presentation steps are
all retained; Mathlib already implements the substantive arguments.

Searches: Lean Finder for the small pro-etale site's covering axioms and
subcanonicity returned the etale analogues. Loogle for
`CategoryTheory.Equivalence.sheafCongr` found the exact transport theorem. The
launcher grep search confirmed `sheafCongr`; local source searches and reads
confirmed the proetale/comap instances, `toPretopology.transitive`, subcanonicity,
and `EssentiallySmall`. Read the current unit record and blueprint proof, all
stated dependency signatures or Mathlib matches, and the landed change record
`coord/changes/weaklyEtale-stability-prune-imports.md`.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.proetale_site_properties`
(node `det-pe-topos-functoriality-site`).

Remaining holes in the item: zero. Holes added: zero. Split-offs: zero.
The unchanged statement covers empty schemes, empty or infinite indexed coverings,
and all scheme characteristics. The presentation and coefficient universe are both
`u + 1`, as required. Single-file compilation passed without warnings.

## No longer needed

None. All original imports and dependency nodes are retained. In particular,
`Sheaf.AlgebraicGeometry.WeaklyEtaleStability` remains imported and its theorem's
base-change and composition clauses are used as local instances, preserving the
unit's specified route. Mathlib supplies the covering operations and sheaf transport.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original DAG proof is realized
using the project stability theorem and the existing closed Mathlib covering,
descent and sheaf-transport APIs.
`ProEt.precoverage` does not itself export the three stability instances under
its defined name; unfolding it locally exposes the instances for `comap`.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
