## What changed

Proved both public theorems of `Sheaf.Paper.ProperIndConstructibleBoundedBelow`, with
unchanged signatures and public imports. Added private, fully proved helpers for
right-derived lower bounds, propagation of object properties and zero terms through
exact-couple pages, finite-filtration induction, and their application to the proper
heart bound. Both coefficient cases explicitly convert the fibre-dimension hypothesis
and apply the existing heart, kernel/cokernel, and extension theorems. Updated their
proof docstrings to describe the actual argument and its positionwise stabilization.

The generic spectral-sequence theorem supplies positionwise stabilization and a finite
abutment filtration, so no separate uniform stabilization construction is necessary.
The retained proof, with refreshed proof docstrings, was recompiled cleanly through
lcompile.py in 10.6 seconds against the current compiled baseline on 2026-10-19,
with no errors or warnings, before delivery checks.
The negative-d case is retained: hd forces each fibre dimension to bottom, so no
natural-number lower bound on a fibre dimension is possible. The proof of the upper bound works for any integer
column bound, including an empty interval.

Updated the existing node's proof and dependencies to describe the actual argument.
The pro-etale sheaf and internal-module Grothendieck instances used instead of the
ringed-site equivalence route are recorded by the already closed nodes
`lem-sfb-proetale-sheaves-grothendieck` and `lem-sfb-modobj-grothendieck`.
No definitions, public signatures, other library modules, or target statements changed.

## Proved and sorry left

Closed 2 of 2 original holes:
- `AlgebraicGeometry.ProEtale.proper_indConstructible_boundedBelow`.
- `AlgebraicGeometry.ProEtale.proper_indConstructible_boundedBelow_padicAlgCl`.

No sorry remains in the item; no holes or split-off statements were added.
All new private helpers are proved. The imported proper-heart, kernel/cokernel,
and extension statements remain the intended next proof obligations of their own nodes.

## No longer needed

Removed the proof-only import
`WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian` and the corresponding
node dependency and tool-use approval `lem-pur-ringed-site-grothendieck-abelian`.
The existing Grothendieck instances for the actual module-object category suffice;
no equivalence with sectionwise ring modules is needed here.

The interrupted sandbox's import of `Sheaf.Paper.ProperUnboundedWindow` is discarded:
that theorem's proof plan depends on the present bounded-below case and cannot be used
as its proof. It was not an import of the repository version. The three unused,
unregistered draft split modules `ProperIndConstructibleCohomology`,
`ProperIndConstructibleLowerBound`, and `ProperIndConstructibleUpperBound` are archived
outside lean/ in the sandbox; none is delivered or required. There are no new nodes.
Also removed the redundant proof imports
`Sheaf.Paper.CondensedModuleDerivedPushpull` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`: the existing public
import `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` already
supplies the general right-derived and module-pushforward APIs used here. Their DAG
nodes remain dependencies, since these APIs are used. Added proof-only Mathlib imports
for object-property extensions and Noetherian scheme instances.
All other original proof-dependency imports are used.

## Where the brief, the DAG or earlier work was wrong

The retained earlier proof compiled by applying the unbounded proper-window theorem,
but this reverses the unit's proof dependency and is circular in the mathematical DAG.
It is replaced completely by the spectral-sequence proof. The retained split files
had no nodes and contained unnecessary holes; this delivery needs none of them.

The DAG's uniform stabilization step was stronger than needed: the existing
hypercohomology theorem already identifies each stable term with a finite page and
provides the required finite filtration. The lower-bound conclusion also follows
directly from the established bounded-below right-derived API. These changes preserve
the unit's bounded-below spectral-sequence route and all three conclusions.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
