## What changed

Kept `AlgebraicGeometry.Etale.graph_proper_interchange` and its public imports unchanged.
Replaced its hole by a proof from two geometric steps and a proved derived-mate calculation.
The proof constructs the ordinary sheaf mate, identifies the two transformations after the
same right-derived unit, and applies `Functor.rightDerived_ext`.

Added three modules, each with its own node:

- `CartesianSumMateUnits`: a complete categorical proof using the existing
  `exact_localization_inverse_mate` and `derivedExact_mateEquiv_app_fac`. The proof identifies
  the inverse sheaf sum mate with the canonical sheaf base-change isomorphism, derives that
  identity, verifies its exact-localization factors, and computes the right-derived mate.
- `CartesianSumMateSheafNormalization`: the ordinary sheaf section calculation. It has no
  properness, compactifications, derived categories, Noetherianity, or finite coefficients.
- `EtaleGraphProperSupportUnit`: the compatibility of the chosen compact-support word with
  the direct-image inclusion and right-derived units. It applies to a commuting square and
  an arbitrary normalized sheaf transformation; it contains no derived sum mate.

The original node now records this route. No other existing module or definition was changed.

All four modules compiled on the server: the sheaf normalization in 15.0 s, the categorical
calculation in 27.5 s, the support-unit statement in 26.4 s, and the original theorem in
31.0 s. A private abstract categorical helper avoids expensive conversions of concrete
sheaf functors: its type-checking took 7.3 s, down from 102 s in the direct specialized
proof. Profiling options were removed after diagnosis; the delivery checks compile the
final files again. The only debug warnings were those removed profiling options.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.graph_proper_interchange` (one of one),
by decomposition. Also proved `AlgebraicGeometry.Etale.cartesian_sum_mate_units` without
adding any hole to its proof.

Added two holes, both named public theorems with complete source-based proof descriptions:

- `AlgebraicGeometry.Etale.cartesian_sum_mate_sheaf_normalization`, node
  `lem-pur-cartesian-sum-mate-sheaf-normalization`.
- `AlgebraicGeometry.Etale.graph_proper_support_unit`, node
  `lem-pur-graph-proper-support-unit`.

Thus the item module has zero remaining holes, and the delivery has two holes total. This is
one original hole replaced by two geometric obligations, not a net reduction of the sorry
count. Neither new hole is the original theorem under another name: the first is entirely
underived; the second assumes only commutativity and a sheaf-level section normalization,
and omits the Cartesian hypothesis and every sum-exchange mate. The proof joining them
uses the independently proved categorical calculation and right-derived uniqueness.

The edge checks were identity squares (adjunction triangle identities), empty graph or
support (zero maps), and the zero ring. No nonemptiness hypothesis is used. The arbitrary-ring
sheaf and categorical lemmas also make sense without finite coefficients.

## No longer needed

None globally. The original geometric dependencies remain needed by the support-unit lemma.
The direct proof dependencies of the original node are reorganized through the three new
nodes; this does not claim that the former dependencies can be pruned from the project.
No existing imports, declarations, or modules were removed.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The original node combined a sheaf section calculation, a
compactification normalization, and a categorical derivation in a single proof step. The
last calculation can be proved from the library's existing abstract derived-mate lemmas;
the two geometric calculations have now been separated without changing the item statement.

Searches used LeanSearch, LeanFinder, Loogle and grep. They found generic mate and derived-unit
identities, but no theorem giving the required sheaf or compact-support normalizations. The
existing proper/open interchange is restricted to an open horizontal leg and does not apply
to the arbitrary separated etale leg of this item. Search details are recorded in the nodes.

## New nodes

`lem-pur-cartesian-sum-mate-units` records the complete derived-mate unit computation. Its
proof invokes existing exact-localization and mixed-derived-mate nodes rather than restating
either of them as a new obligation.

`lem-pur-cartesian-sum-mate-sheaf-normalization` is the graph-on-summands normalization of the
ordinary Cartesian sheaf mate. Its source is the graph inclusion construction in Tag 0F4L,
the canonical adjoint-uniqueness base change of Tag 03S6, and the transpose step of Tag 0F7F.

`lem-pur-graph-proper-support-unit` is the common-support comparison of Tag 0F7B, transported
through the chosen graph and proper compactifications and the every-tower formula of
Tags 0F7I and 0F7J. Its sheaf normalization input is explicit, so it does not also assert the
Cartesian mate calculation.

All three inherit the original chapter, unit and blueprint ancestry. No change record is
needed because no existing signature, definition, public import or other module was changed.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
