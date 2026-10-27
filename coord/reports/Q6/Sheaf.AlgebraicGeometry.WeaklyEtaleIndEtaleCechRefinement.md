## What changed

Proved `AlgebraicGeometry.exists_finite_affine_indEtale_cech_refinement` without changing
its statement. The construction first refines the pullback of the target affine cover,
takes a finite source subcover, and applies the proved ring-level weakly-etale refinement
theorem on each affine chart. The finite jointly surjective family is pro-etale by the
standard finite quasi-compact-cover instance. An induction using product fans in `Over U`
proves the qcqs and chart assertions, and a final finite subcover supplies finiteness.

Added `Sheaf.AlgebraicGeometry.IndEtalePullbackCharts`, isolating the binary geometric
step: pull back the preceding charts to the affine source open, refine them by affines,
pull back along its ind-etale refinement, and transport by the pullback-pasting isomorphism.
The helper is strictly a binary chart statement, with no cover existence, qcqs, tuple,
weakly-etale-base, or finiteness assertion. The other helpers are private and proved.
Remote `lcompile.py --all` succeeded: 6.2 seconds for the binary chart module and
11.1 seconds for the item, with no compiler warnings or errors.
The existing node's proof and dependencies now follow this implementation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_finite_affine_indEtale_cech_refinement`
(node `lem-sfb-weakly-etale-indetale-cech-refinement`).

Added zero holes. No `sorry` remains in either delivered module. In particular,
`AlgebraicGeometry.exists_affine_indEtale_pullback_charts` is proved rather than split off.
There is no data definition chosen from an unproved existence theorem: the spectrum,
open-cover, and pullback constructions in the proofs use proved existence results only.

## No longer needed

Removed these proof imports:

- `Sheaf.AlgebraicGeometry.EtaleComparison`
- `Sheaf.RingTheory.IndEtaleSmallIndex`
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
- `Sheaf.AlgebraicGeometry.ProEtaleQcqsSiteLimits`
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`
- `Sheaf.AlgebraicGeometry.WeaklyEtaleStability`

The corresponding wrapper dependencies `det-pe-morphisms-etale-comparison`,
`lem-pe-ind-etale-small-index`, `lem-sbc-finite-affine-tensor-base-change`,
`lem-weil-pbc-proetale-qcqs-site-limits`, `pqf-lem-qs-intersection-qc`, and
`sk-lem-pe-weakly-etale-stability` are no longer needed by this proof. Their functions
are supplied directly by the proved source pro-affine-etale API and Mathlib instances.
The additional original dependencies `lem-pqf-finite-affine-cover-qc-open`,
`lem-weil-pbc-etale-ring-map-iff-etale-affine`, and `def-weil-pbc-proetale-site` are also
unneeded here. No module is withdrawn: other consumers may still need all these files.
All five obsolete `tool_uses` entries of the item node are removed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original route needed more geometric bookkeeping than
the available APIs require. A finite affine source family over target charts follows
by refining the pullback of the target affine cover and then taking one finite source
subcover; no initial finite target cover is necessary. The ordinary qcqs pullback
instances replace the qcqs-site finite-limit bridge. The ring refinement already gives
universe-u rings and small ind-etale presentations, so no small-index reduction is needed.
The arbitrary nonaffine fibre products are never asserted to be affine.

Edge cases checked in the argument: an empty source permits an empty finite cover;
the singleton tuple uses `productUniqueIso`; repeated indices use the same induction;
zero rings are admitted by the ring refinement theorem; and an empty pullback has its
usual affine open refinement. Neither the unit statement nor its realized route changes.

## New nodes

`lem-sfb-indetale-pullback-charts` records the proved binary chart theorem in
`lean/Sheaf/AlgebraicGeometry/IndEtalePullbackCharts.lean`. It inherits the item's chapter
and unit, specifies the source argument, and records LeanSearch, Loogle and grep searches.
It is a genuine binary step in the Čech induction, with a complete Lean proof and no
new hole. No definition or statement change record is needed.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
