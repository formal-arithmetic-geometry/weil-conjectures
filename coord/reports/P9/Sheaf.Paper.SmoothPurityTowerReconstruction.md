## What changed

Repair of returned head ab05c97498f (reviewer C-ab05c): the proof review passed,
but landing rejected a reviewer correction named
`sp-tower-integral-consumer-instances.md`. The record is present in the packet at
`coord/changes/sp-tower-integral-consumer-instances.md`; the landing tool accepts its
reviewer correction only as `sp-tower-integral-consumer-instances.change.md`.
Documented that mapping in the record and changed the shared-data record's bare
cross-reference to the full repository path. This repairs the handoff metadata;
the approved mathematical argument and the two remaining obligations are retained.
Compared the sandbox with current sheaf-dag: the four new Lean modules and four new
nodes remain absent from main; the item node differs only in its proof, proof_deps,
proof_origin and lean attachment. IntegralDirectImageTower is unchanged (reviewer
correction: its adaptation was not forced and is withdrawn). The delivery tool rebases this packet
on freshly fetched sheaf-dag and repeats compilation and server preflight.

Decomposed spTower_reconstruction with its full original statement into canonical
finite-projection comparison and arbitrary-tower derived completeness, then wrote the
Lean assembly. The assembly transports constructible homology and the common Tor interval
through the canonical reduction isomorphisms; the cofinality proof transfers these to
uniformizer reductions. Their support is explicitly contained in a finite integer interval,
which supplies the intrinsic bounded-constructibility witness.

Proved sp_cofinal_integral_reduction_bounds from the existing
sp_cofinal_finite_reduction_constructibility, using localization uniqueness for exact
restriction and left-adjoint uniqueness for the scalar models. Constructibility is
transported by the already proved module-sheaf iso lemma, and Tor amplitude is transported
by composing the isomorphisms from every representative. This proof uses neither an
arbitrary scalar-model equality nor a new assumption.

Extracted the unchanged completed evaluations, transitions and projection-adjunct map into
SmoothPurityTowerReconstructionData so the new comparison statements can use them without
an import cycle. The original module publicly re-exports the data module. Reused the identical polymorphic
completed ell projection already defined by EllCoefficientFiber, importing it publicly
from the data module. No upstream source file or target is edited. A fixed-universe abelian instance in the
data module preserves instance inference in its importers; it uses the original
module-sheaf abelian structure. The change record is
coord/changes/sp-tower-reconstruction-shared-data.md.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.ProEtale.spTower_reconstruction by the Lean
assembly. Proved the new theorem AlgebraicGeometry.ProEtale.sp_cofinal_integral_reduction_bounds
(node lem-sp-cofinal-integral-reduction-bounds) completely from existing declarations.

Added exactly two holes, each a whole public named theorem in its own module:

- AlgebraicGeometry.ProEtale.spTower_projection_finite_reduction
  (lem-sp-tower-projection-finite-reduction): one specified finite projection; no
  boundedness or constructibility assumptions.
- AlgebraicGeometry.ProEtale.spTower_limit_derived_complete
  (lem-sp-tower-limit-derived-complete): arbitrary coefficient-tower limits; no
  normalization, boundedness or constructibility assumptions.

This is a decomposition of one original hole into two independent, strictly smaller
obligations, not a net hole reduction. There are zero holes in the item module and zero
holes in the new definition module. EllCoefficientFiber retains its existing three holes
sp_completed_coefficients_regular,
sp_ell_coefficient_tensor and sp_ell_coefficient_fiber unchanged. No existing proof is
replaced by sorry. Its coefficient regularity theorem is used unchanged.

## No longer needed

No mathematical dependency modules are pruned or withdrawn. The parent assembly now uses
the two comparison nodes and the proved cofinal bounds node; the old six extracted
mathematical lemmas remain needed through those arguments. No unit route is bypassed.

The old proof-only import all SmoothPurityCoefficientTowersAbelian is needed only by the
extracted characterization proofs and moves to the data module. The redundant proof import EllCoefficientFiber was removed from the cofinal bounds
module because its public data import already provides it. Existing public imports
of the item are kept; EllCoefficientFiber itself is untouched. Cofinality uses the existing
theorem and
successive-quotient normalization rather than a duplicate scalar construction. The
standalone Roos cohomological bound [a,b+1] is not needed in the assembly: uniform Tor
bounds on finite reductions already yield the exact support bound required by
sfIntegralConstructible. It remains part of the generic Koszul--Roos lemma used by the
finite-projection argument; it is not deleted from the library.

## Where the brief, the DAG or earlier work was wrong

The six extracted declarations do not directly match the item interface: the semilinear
model uses a strict complex and completed lift, the error diagram and Koszul--Roos theorem
use different generic tensor models, and power-torsion completeness ends in
IntegralOnSlice.IsComplete rather than IsSfDerivedComplete. The two new holes isolate
those projection- and unit-preserving comparison steps with the complete source argument
in their docstrings and nodes. The cofinal scalar-model comparison was proved here.

EllCoefficientFiber and this item independently defined the same fully qualified
spCompletedEllProjection. The data module now publicly imports the existing
coefficient-fiber declaration,
with no change of its formula. EllCoefficientFiber is currently held by J7 and is
not adapted. Consumer statements keep their meaning. The unchanged CompletedTowerRoos source
initially failed with `u + 1 =?= max (u + 1) ?u.26` because the coefficient-fiber
import exposed a generic instance with an underdetermined coefficient universe. The
data module now offers the original fixed-universe abelian structure at higher
priority; all direct consumers, IntegralDirectImageTower included, compile unchanged
(reviewer correction: the IntegralDirectImageTower timeout was caused by load, not by the delivery).

New statements were checked on the zero tower, arbitrary (not necessarily normalized)
towers for completeness, the empty scheme, level zero (positive exponent one), and ramified
extensions where ell is a unit times a higher uniformizer power. No invertibility of ell
on T, uniform termwise torsion exponent, quotient flatness, or equality of ell with pi
was introduced. The cofinal bounds theorem also permits an unbounded original M and a
single-point interval a=b. It uses the provided finite-quotient scalar-extension theorem
without strengthening its assumptions.

Mathlib searches used LeanSearch, LeanFinder, Loogle and grep through msearch.py; queries
and actual results are recorded on the new nodes. Searches of the current blueprint and
both source roots found no exact existing statement for the two interface comparisons.

## New nodes

- def-sp-tower-reconstruction-data: the existing evaluation, transition and adjunct data,
  with their already proved unique characterizations.
- lem-sp-tower-projection-finite-reduction: projection-induced finite reduction comparison,
  no constructibility or boundedness assumption; remaining hole.
- lem-sp-tower-limit-derived-complete: completeness with the recorded quotient unit for
  any coefficient-tower Roos limit; remaining hole.
- lem-sp-cofinal-integral-reduction-bounds: proved transfer from ell-power reductions
  to the existing uniformizer reduction functors and common cohomology interval.

The existing item node records the actual Lean assembly, and the coefficient-fiber
node and its existing module remain untouched. The change record is coord/changes/sp-tower-reconstruction-shared-data.md
(coord/changes/sp-tower-integral-consumer-instances.md is withdrawn).

## Forced adaptations

None. The worker's local `attribute [-instance]` and `attribute [local irreducible]`
commands in Sheaf.Paper.IntegralDirectImageTower (held by B8) were withdrawn by the
reviewer: the original module compiles unchanged, without diagnostics, against the
delivered modules (29.1 s on 2026-10-26; 24.1 s and 34.1 s on 2026-10-25; published
baseline 34.0 s). The worker's 60 s timeouts were caused by machine load. The direct importers
SmoothPurityCompletedTowerRoos, SmoothPurityNormalizedEquivalence and
IntegralDirectImageTower compile unchanged.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
