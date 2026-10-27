## What changed

Extracted the original interfaces and already-proved helpers verbatim into
`Sheaf.Paper.ReconstructedPairRefinementData`; the original module publicly
re-exports them. The change record is
`coord/changes/A5-reconstructed-refinement-interface.md`. No target, original
signature, definition body or map normalization changes.

Reduced `reconstructedPairRefinementCoherence` to five strictly smaller statements.
The combination proof implements coordinate conjugation identity/composition,
functorial integral refinement identity/composition, both cocycles, the actual
reduction square, the Brown mate counit equation, all representing Hom naturality,
the closure adjunction transpose, the common-pair trace equation, and scalar
identity/transitivity. Each unfinished geometric/reconstruction step is separately
stated with its source and full natural-language argument.

## Proved and sorry left

The original hole in
`WeilConjectures.ReconstructedPairRefinement.reconstructedPairRefinementCoherence`
is closed by reduction. The already-proved `systemDown_isIso` and `output_origin`
are retained unchanged in the data module. Five holes are added, all in namespace
`WeilConjectures.ReconstructedPairRefinement`:

- `reconstructedRefinementCommon`
  (`lem-pur-reconstructed-refinement-common`): only common-refinement independence,
  with no mate, representing-pair, coefficient, or cocycle conclusions.
- `reconstructedBrownMateLaws`
  (`lem-pur-reconstructed-brown-mate-laws`): only invertibility and composition of
  the actual system Brown mate, with no reconstructed trace conclusions.
- `reconstructedRefinementSingleDegree`
  (`lem-pur-reconstructed-refinement-single-degree`): only the same-degree system
  equality detection step.
- `reconstructedRefinementTraceSquare`
  (`lem-pur-reconstructed-refinement-trace-square`): only the integral counit square
  from the supplied theta square, without Hom, scalar or realization conclusions.
- `reconstructedRefinementTraceTransport`
  (`lem-pur-reconstructed-refinement-trace-transport`): transport of an assumed
  integral trace equation for arbitrary objects/maps/traces; it proves no Brown or
  supplied-system square and has no representing-pair assumptions.

This is a decomposition: one original hole closed, five added, net minus four;
it is not reported as a completed axiom-free proof. There are no holes in the
item or data module. No holes are moved into definitions or private declarations.

## No longer needed

No module is withdrawn. The final direct geometric import is narrowed from
`WeilConjectures.Compactification.CategoryBaseChange` used during development to
`WeilConjectures.Compactification.CommonRefinement`, whose actual existence
theorem is all the combination proof needs. The original public imports are retained transitively
through the data module. Its finite-origin proof import remains needed for the
unchanged `systemDown_isIso` proof. The five new imports in the item are proof-only. A private import of
`WeilConjectures.Compactification.CommonRefinement` supplies the actual common
compactifications used to combine the integral cocycle.

The direct proof no longer needs `lem-pur-reconstructed-pair-finite-scalar-extension`
(`Sheaf.Paper.PurRepresentingPairFiniteScalar`): the required conclusions only
transport the existing trace equation through specified functors and comparisons,
and scalar identity/transitivity follow directly from ComparisonFamily's laws.
It likewise does not use the filtered-two-colimit theorem to extend an equality
already between actual closure scalar images; the arbitrary-test Hom equation
then follows from naturality. The corresponding statement dependencies and public
interfaces remain, so nothing is withdrawn from the unit route.

Direct imports of `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` and
`Sheaf.AlgebraicGeometry.CompactificationRefinementCoherence` are unnecessary:
`systemRefinement_id` and `systemRefinement_comp` already expose the actual
intrinsic laws. Common-refinement cancellation is isolated in its stated substep.
The ringed coefficient, semilinear sections and strict proper/open dependencies
remain below the finite-origin and coefficient-transport substeps; no adopted
source declaration or proof is removed.

## Where the brief, the DAG or earlier work was wrong

The original parent plan did not expose the cross-compactification reconstruction
square, common-refinement cancellation, restricted Brown mate laws or generalized
trace transport as directly applicable declarations. Existing naturality APIs
suffice for their categorical consequences, which are now proved explicitly.
The five new substeps isolate only the missing parts. A full transitive dependency walk
also encountered the pre-existing cycle
`lem-pc-ring-hom-extension-differential` /
`lem-pc-ring-hom-extension-differential-adjacent`; neither is changed here, and
a separate reachability check found no cycle through any delivery node. The single-degree argument
uses full faithfulness on the shifted heart, not faithfulness of finite evaluation
on arbitrary derived maps. Zero objects, identity refinements, arbitrary common
refinement choices and arbitrary traces were checked against the stated arguments.
The read-only blueprint ancestor tool prints `None` for this derived item; the
new nodes preserve the parent record's explicit ancestor
`thm-pur-rational-and-qbar-purity` and cite the current latest unit proof.

## New nodes

`def-pur-reconstructed-refinement-data` records only the verbatim interface
extraction and retained helpers. Its Lean attachment lists the original names.

`lem-pur-reconstructed-refinement-common` is the common further-refinement
cancellation step of parent Steps 2--3.

`lem-pur-reconstructed-brown-mate-laws` is the counit-uniqueness inverse and
composition calculation in parent Steps 4 and 6.

`lem-pur-reconstructed-refinement-single-degree` is the good-truncation/shifted-heart
recognition argument of parent Step 4.

`lem-pur-reconstructed-refinement-trace-square` is the reduction/limit naturality
calculation of parent Steps 4--5.

`lem-pur-reconstructed-refinement-trace-transport` is the functorial scalar,
rational and finite-valued closure transport calculation of parent Steps 7--8.

The parent's proof and proof dependencies now describe the implemented combination.
All new statements are genuine substeps, and the blueprint unit route is retained.
The complete final seven-module sandbox passed `lcompile.py --all` with no
diagnostics. The combination theorem's preceding single-file run used 26.7 seconds
of Lean time; batch per-file wall times also include queue/server setup.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
