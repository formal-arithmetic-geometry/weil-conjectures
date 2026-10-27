## What changed

Replaced the whole proof of
`AlgebraicGeometry.FineSaturatedLogScheme.free_characteristic_regular_boundary`.
Its signature and all four existing public imports are unchanged. Added two private,
proved helpers: `regular_iff_free_at` and `reduced_ideal_comap`.

The local helper applies the already stated monoidal local regularity criterion to a
sharp-chart local-algebra certificate, explicitly enumerates its finite set of
indecomposables, composes its two equivalences, and transports regularity through the
strict-henselization invariance theorem. In the reverse direction the certificate's rank
identification converts a free presentation of arbitrary finite rank to the criterion's rank.

The global proof constructs geometric points above ordinary points using algebraic
closures of residue fields, proves stalkwise regularity, chooses boundary charts,
proves openness as a union of open chart images, and proves density by meeting each
nonempty open on a chart. It applies reduced Cartier descent to the resulting jointly
surjective etale family. Taking kernels of the descent isomorphisms identifies the
pullback ideals, and composing the local normal crossings witnesses proves the required
parameter equations on X.

Two new modules isolate genuine remaining steps: the construction and transport of the
sharp-chart local algebra, and the reduced parameter-product boundary on one pointed
free chart. The first asserts no ambient regularity or monoid freeness, and the second
assumes freeness only at a single geometric point and concludes no global statement.
Their theorem proofs are each exactly `by sorry`, with source and full proof in words.
The existing item node now records this assembly, and both new modules have nodes.
No existing module besides the item is changed, so there are no forced adaptations or
shared-interface consumer changes requiring compilation.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.FineSaturatedLogScheme.free_characteristic_regular_boundary`
(node `lem-trf-free-characteristic-regular-boundary`): the item has zero textual holes.
Added exactly two holes:

- `AlgebraicGeometry.FineSaturatedLogScheme.logRegular_sharp_local_algebra`,
  node `lem-trf-log-regular-sharp-local-algebra`, in
  `Sheaf.AlgebraicGeometry.LogRegularSharpLocalAlgebra`.
- `AlgebraicGeometry.FineSaturatedLogScheme.exists_free_characteristic_boundary_chart`,
  node `lem-trf-free-characteristic-boundary-chart`, in
  `Sheaf.AlgebraicGeometry.FreeCharacteristicBoundaryChart`.

This is a decomposition: one original hole closed, two lower holes added, not a proof
independent of sorry. Existing holed dependencies such as the monoidal criterion and
reduced Cartier descent are used as intended by stage 3. No holes are placed in
definitions or private helpers. There are no new definitions or axioms.

Edge cases checked mathematically: rank zero gives the empty monoid basis and product 1;
unit coordinates disappear from the boundary ideal; there is no global labelling of
branches; the empty scheme gives a vacuous chart family and all pointwise conditions.
The two new statements compiled individually in 4.7 s and 4.6 s respectively. The item
and the delivery's axiom probes are checked by lcompile.py and deliver3.py.

## No longer needed

The following direct private proof imports were removed from the item:

- `WeilConjectures.RingTheory.StrictHenselizationNoetherian`.
- `WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters`.
- `WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence`.
- `Sheaf.RingTheory.StrictHenselizationComparison`.
- `WeilConjectures.RingTheory.StrictHenselizationCotangentDimension`.
- `Mathlib.RingTheory.LocalRing.Module`.
- `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`.
- `Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction`.
- `Sheaf.AlgebraicGeometry.LogRegularSharpChart`.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`.
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`.

These removals simplify the assembly's imports; they do not withdraw any existing
mathematical statement. Sharp charts, contraction, Noetherianity and affine comparison
are retained in the local-algebra node's proof. Ordinary free-chart parameters,
parameter-product reduced Cartier, and reduced-induced uniqueness are retained in the
boundary-chart node's proof. The corresponding old direct item proof dependencies are
moved to those nodes, not declared globally obsolete. The adopted source declarations
and all existing modules remain intact. No entire module is claimed pruned.

The obsolete direct item `tool_uses` entries removed are
`lem-sc-strict-henselization-noetherian`,
`lem-weil-pbc-regular-local-quotient-kernel-parameters`,
`lem-weil-pbc-regular-local-generators-regular-sequence`,
`lem-sc-strict-henselization-comparison`, and
`lem-sc-strict-henselization-cotangent-dimension`.
The relevant algebra remains under the existing monoidal criterion or the new bridge
plans. Strict-henselization regularity and flat-lfp openness remain direct uses.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was corrected. The item still imported the old fine-grained
local-algebra modules, whereas its current DAG already calls for the newer monoidal
criterion, free-chart parameters and parameter-product theorem. Those declarations do
not themselves supply all the transport and chart-boundary identification glue. The
two new nodes make that gap explicit instead of inserting holes inside the assembly.
The fixed unit and chapter records are unchanged; no realized unit step is bypassed.
The source passages were read in ILO VI 1.2 and 1.4--1.7 (printed pp. 69--70),
VIII 3.4.3--3.4.4 (p. 110), and VIII 4.1.1--4.1.2 (p. 117).
The initial compile identified an unconstrained cover-index universe in a projection
of the descent theorem; it is explicitly instantiated in the private helper.

## New nodes

`lem-trf-log-regular-sharp-local-algebra` prepares the strict-henselization and sharp
chart hypotheses for `monoidal_local_regularity_criterion`, including finite rational
rank and its identification for any free presentation. Its proof follows ILO VI 1.2,
1.6 and VIII 3.4.3 with the existing affine comparison and monoidal-contraction nodes.
It is strictly local algebra data, not the target's regularity criterion under a new name.

`lem-trf-free-characteristic-boundary-chart` supplies one pointed etale neighbourhood
whose open triviality locus has dense reduced normal crossings complement. Its proof
uses the existing sharp chart, ordinary-parameter and parameter-product declarations,
then reduced-induced uniqueness. Global openness, density and descent are proved in
the item. Both new nodes record LeanSearch, LeanFinder/Loogle and source grep searches;
none found these bridges. No change record is needed because existing public interfaces
and statements have not changed.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
