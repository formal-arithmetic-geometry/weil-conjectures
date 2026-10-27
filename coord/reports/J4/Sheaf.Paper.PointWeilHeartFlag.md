## What changed

Replaced the sorry in `WeilConjectures.zl_point_weil_heart_flag` with a Lean proof
combining the algebraic finite-stage flag and the scalar punctual-spectrum comparison.
The proof calculates the logarithmic weight, proves purity of every quotient, chooses
one upper bound for its finite family of weights, transports purity across the Weil
cokernel isomorphisms, and supplies the mixed filtration explicitly. The construction
works for the empty quotient family without a separate nonzero-dimension assumption.

Moved the original data prefix, with identical declaration signatures and bodies,
to `Sheaf.Paper.PointWeilHeartFlagData`, publicly reexported by the assigned module.
This allows the new construction and comparison lemmas to use the existing data
without an import cycle. It is a dependency split, not a response to a timeout.
The original theorem signature and all definition bodies are unchanged. The data
node records their new location. See `coord/changes/J4-point-weil-flag-data.md`.

The two new statements are strict argument parts. The algebraic construction neither
mentions a complex embedding nor asserts purity or mixedness. The spectrum comparison
only identifies eigenvalues when an operator is already scalar; it constructs no flag
or finite coefficient model. Their combination additionally requires the real-power
calculation, finite upper bound, isomorphism invariance of punctual purity, and the
explicit mixedness witnesses proved in the assigned module.

## Proved and sorry left

Closed the original hole in `WeilConjectures.zl_point_weil_heart_flag`
(`lem-zl-point-weil-heart-flag`) by decomposition into two named holes. This is a
decomposition, not a completed proof of all underlying theory: one hole closed,
two holes added, net minus one. The assigned module has zero remaining holes.

Added, with complete proof sketches and DAG nodes:

- `WeilConjectures.zl_point_weil_algebraic_flag`
  (`lem-zl-point-weil-algebraic-flag`), in `Sheaf.Paper.PointWeilAlgebraicFlag`.
- `WeilConjectures.zl_point_scalar_punctual_spectrum`
  (`lem-zl-point-scalar-punctual-spectrum`), in `Sheaf.Paper.PointScalarPunctualSpectrum`.

No holes occur in definitions. The two private proof helpers are proved in full.
The data module has zero holes. The three support modules compiled successfully.
The assigned proof compiled successfully with only a redundant-tactic warning; the
redundant tactic and import were then removed. The first delivery preflight exposed
a data signature record mismatch, which was repaired, and an unnecessary parent
stmt_deps edit, which was reverted. The subsequent delivery compile failed for
infrastructure reasons: stdbuf could not create a temporary directory in /tmp,
reporting `No space left on device (os error 28)`. Retrying delivery returned the
same server failure. Nothing was pushed; a final clean compile/preflight remains
required after server disk space is restored.

## No longer needed

The assigned module no longer directly imports `Sheaf.Paper.PointFibreEquivalence`,
`Sheaf.Paper.ConstructibleTruncations`,
`Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`,
`Sheaf.SixFunctors.FrobeniusPointTransportNatural`, or
`WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable`.
The algebraic flag subproblem retains the actual dependencies through
`PointHeartFiniteStage`, `AutomorphismFlagFiniteCoefficients`, and
`PointEquivariantDiagramLift`. Thus these modules and their nodes are not globally
pruned; their work remains needed for that construction. The main proof now depends
on the two smaller statements rather than repeating their categorical machinery.
No module is withdrawn and no unit route is bypassed. The parent
`thm-zl-real-mixed-by-curves` still uses this node for its dimension-zero step.

## Where the brief, the DAG or earlier work was wrong

The existing dependencies provide the mathematical construction but their interfaces
do not directly return the required `ZlPointWeilFlagDiagram`. Combining the adapted
linear flag with the finite equivariant diagram requires forming a finite index
category, transporting from Spec(k) to the geometric fibre, specifying the endpoint,
and recording the coefficient Shrink identifications. Those are retained in the
algebraic construction subproblem, with the original construction route preserved.

There are two further interface details in the original assembly sketch. Punctual
purity uses eigenvalues of arbitrary finite presentations, while the flag statement
uses the specified common-stage local operator; the scalar-spectrum comparison must
bridge them. Mixedness uses cokernels in the actual Weil heart, while the flag
predicate records exactness only in the underlying heart. The algebraic construction
therefore explicitly supplies the Weil-arrow monos and cokernel isomorphisms, justified
by equivariance of the unique underlying-heart factorization.

Edge cases checked: zero-dimensional fibre gives the singleton zero endpoint and no
quotients; rank one gives a single unit scalar; nontrivial Jordan blocks are allowed;
coefficient enlargement permits eigenvalues outside the initial field; no reality or
semisimplicity is assumed. The scalar-spectrum lemma permits an arbitrary scalar,
including zero: a zero fibre has no eigenvalue, so that case is vacuous. The norm
calculation in the main proof uses the stronger unit condition of the quotient data.
`python3 tools/downstream.py Sheaf.Paper.PointWeilHeartFlag` reports zero Lean importers;
DAG parents and the unit realization still require the theorem and are retained.

## New nodes

`def-zl-point-weil-flag-data` owns precisely the existing data declarations moved to
the support module. It introduces no changed mathematical notion. Its definition
bodies, public interfaces and cached instances are preserved; the original module
publicly reexports them.

`lem-zl-point-weil-algebraic-flag` packages the algebraic construction, before weights,
from the existing finite-stage descent, finite-coefficient linear algebra and diagram
lifting statements. It also makes the categorical quotient universal property needed
by the mixedness definition explicit.

`lem-zl-point-scalar-punctual-spectrum` compares the specified scalar point operator
with every finite-presentation eigenvalue and identifies the point's residue
cardinality. It is independent of choosing or constructing an invariant flag.

Change record: `coord/changes/J4-point-weil-flag-data.md`.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
