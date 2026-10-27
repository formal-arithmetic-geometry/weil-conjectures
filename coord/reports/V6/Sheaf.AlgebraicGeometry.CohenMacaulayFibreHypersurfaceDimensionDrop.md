## What changed

Proved `AlgebraicGeometry.exists_affine_flat_hypersurface_of_fiber_depth` with its
original signature. Extracted the first element of a positive-length regular
sequence from positive depth, lifted it through the fibre projection stalk map,
and applied the existing flat-hypersurface theorem. Explicit stalk congruences
handle the difference between the given fibre point and `g.asFiber x`.

Added the proved module `Sheaf.AlgebraicGeometry.PrincipalHypersurfaceFibreStalk`.
It constructs the closed hypersurface fibre point from Spec of the quotient
local ring, proves the stalk kernel is precisely the principal germ ideal, and
checks compatibility with the original total-space stalk map. The proof uses
only Mathlib. In particular the new lemma is valid without flatness,
Noetherianity, regularity or any depth/dimension assumption.

Applied `IsLocalRing.depth_quotient_nonzerodivisor` for the dimension drop and
transported its regular sequence across the ring equivalence for the depth
bound. Both delivered modules compile cleanly (7.2 s and 9.4 s respectively).
The delivery check will recompile the final packet.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.exists_affine_flat_hypersurface_of_fiber_depth`
(node `lem-trf-cm-fibre-hypersurface-dimension-drop`).

Also proved the new theorem
`AlgebraicGeometry.exists_closed_fiber_point_principal_stalk_equiv`
(node `lem-trf-principal-hypersurface-fibre-stalk`).

Actual remaining holes in delivered Lean: zero. Holes added: zero. Split-off
sorry statements: zero. The assembly continues to use the already stated
`AlgebraicGeometry.exists_affine_flat_hypersurface_of_fiber_regular`, whose
pre-existing sorry is outside this delivery. Thus this closes the assigned
hole from its stated dependencies, without claiming axiom-free completion of
that transitive dependency.

## No longer needed

Removed proof imports:
`WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage` and
`Mathlib.RingTheory.Localization.Ideal`.

The assigned theorem no longer uses nodes
`lem-pc-closed-subscheme-base-change-ideal-image` or
`lem-weil-pbc-localization-at-prime-of-quotient`: the quotient universal
property and the first isomorphism theorem replace ideal-sheaf images and
localization of quotients. Its own proof also no longer directly needs
`lem-weil-pbc-affine-open-stalk-localization`; the new geometric lemma uses
that Mathlib API for the affine factorization of the canonical stalk morphism.
Removed these three obsolete approvals from the item's `tool_uses`, retaining
the remaining entries in order. No existing module is withdrawn or deleted,
and no global unreachability is asserted for these shared dependencies.

## Where the brief, the DAG or earlier work was wrong

The old geometric proof plan was unnecessarily indirect. Using Spec(A/(b))
gives the fibre point and a left inverse to the surjective fibre stalk map
modulo (b); the other kernel inclusion follows from the affine quotient chart.
This also gives the required compatibility directly by naturality of maps from
spectra of stalks. No statement correction or shared interface change was needed.
The blueprint unit route is retained: positive depth gives a regular germ,
then a flat hypersurface, then the Cohen--Macaulay quotient theorem. In the
edge case d=1, the quotient regular list is empty and the transported depth
bound is zero. In the new lemma a=0 gives the open chart and quotient by zero;
a unit germ is excluded by the maximal-ideal hypothesis, ensuring the local
quotient is nonzero. An empty fibre cannot furnish the assumed point.

## New nodes

`lem-trf-principal-hypersurface-fibre-stalk` records the compatible quotient
identification used in the positive-dimensional case of Stacks Tag 0570,
`lemma-slice-CM`. The Lean proof replaces the affine localization computation
with an explicit universal-property argument. Its docstring and node give
that complete argument. LeanFinder, LeanSearch, Loogle and grep searches are
recorded from `searches.jsonl`; existing germ/stalk results are ingredients,
not this theorem. The blueprint search found no duplicate. This is a proved
auxiliary theorem, with no new postponed proof. No change record is necessary:
no existing statement, definition, attribute or public import was changed.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
