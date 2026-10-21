## What changed

Proved all three theorems in `Sheaf.AlgebraicGeometry.EtaleInjectiveSupportSequence`.
The support counit is the kernel inclusion through the upstream support isomorphism;
the open unit is split epic on injectives by the existing extension-by-zero argument.
Exact extension by zero makes open restriction preserve K-injectives. Private proved
comparison lemmas identify the specified endpoint maps with the actual derived
adjunction maps. The existing natural closed-support triangle supplies the boundary;
open-closed orthogonality forces the third component of the triangle isomorphism.
Boundary naturality is Mathlib's canonical SES-boundary naturality theorem.

Change record: `coord/changes/etale-injective-support-proof-context.md`, requested
by server preflight for the added private-helper section and local irreducibility
commands. The consumer scan reports zero downstream Lean modules; no adaptations
are required. These commands leave the public interface unchanged.

All existing signatures, definitions and public imports are preserved. No other
module is changed. Updated the assigned node's proof route, dependencies and origin;
removed its obsolete tool-use entries without adding or reordering approvals.
The added route dependencies are existing proved nodes for extension by zero,
its open-closed short exact sequence, and derived open-closed vanishing.

## Proved and sorry left

Closed 3 original holes:

- `AlgebraicGeometry.Etale.etaleSupportSequence_zero`.
- `AlgebraicGeometry.Etale.etale_injective_support_sequence`.
- `AlgebraicGeometry.Etale.etaleSupportSequence_boundary_naturality`.

Added 0 holes; split off 0 holes. No `sorry` remains in the delivered module.
The full module compiled cleanly through `lcompile.py` in 46.4 seconds, with no
errors or warnings. A text comparison confirms all seven public definition bodies
and all three theorem signatures are unchanged.

All private helpers are proved. The main statement retains every hypothesis and all
three prescribed triangle components, for every unbounded representative and every
representing isomorphism. No new resolutions, arbitrary witnesses, definitions or
axioms are introduced.

## No longer needed

Removed these private proof imports:

- `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`.
- `Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction`.
- `Sheaf.CategoryTheory.RingedSiteInjectiveMonoRestriction`.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`.
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`.

The proof no longer directly uses the following planned node dependencies; their
corresponding obsolete tool-use entries are removed:

- `def-weil-pbc-direct-image`.
- `def-weil-sheaf-of-modules-category`.
- `lem-pur-etale-supported-kernel-adjunction`.
- `lem-pur-kinjective-degreewise-existence`.
- `lem-pur-kinjective-restrict-localized`.
- `lem-pur-ringed-site-injective-mono-restriction`.
- `lem-weil-pbc-etale-inverse-image-restriction`.
- `lem-weil-pbc-etale-site-localization-open`.
- `lem-weil-pbc-kinjective-hom-derived`.
- `lem-weil-pbc-kinjective-total-derived`.
- `lem-weil-pbc-ring-sheaves-grothendieck`.
- `prop-weil-pbc-inverse-image-modules-exact`.

These include the ringed-site injective restriction/Grothendieck transport route,
localized-site restriction, and construction/comparison of additional K-injective
replacements. Existing source-library declarations and imports remain intact;
this report claims no global withdrawal of their dependencies. Public imports
already required by the unchanged interface are retained, including the closed
support triangle. Its already established natural boundary replaces a new descent
construction. The unit's own statement and realized steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The planned route was longer than necessary:
injectivity and K-injectivity are already hypotheses on the supplied model, and
the source library proves the ordinary-etale injective splitting and the required
module-valued support adjunction. The existing closed-support triangle also avoids
constructing and descending a new boundary. Empty schemes, the zero ring and
unbounded complexes introduce no extra hypotheses in these categorical arguments.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
