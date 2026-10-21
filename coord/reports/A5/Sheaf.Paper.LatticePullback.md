## What changed

Proved `AlgebraicGeometry.ProEtale.lattice_pullback` with its statement and its two
section constructions unchanged. The inclusion is pullback of `i` followed by the
canonical restriction-of-scalars comparison. Its normalized adjunction unit proves
the section formula and uniqueness; exact pullback proves monicity. A double-mate
argument constructs the invertible rationalization and identifies its adjoint with
that same inclusion.

Added two proved support modules: continuous coefficient inverse-image isomorphisms
for totally disconnected rings in the scheme universe, and preservation of finite
local bases by ringed-site pullback. Neither introduces a hole or chooses data from
an unproved mere existence statement. The coefficient proof uses the existing
universe-polymorphic continuous realization, with an explicit identity comparison
between its continuous-function presentation and the lattice presentation.

Validation: both support modules compile cleanly in import order (4.6 and 20.7
seconds); the final main module compiles cleanly in 37.4 seconds. Its theorem
signature and both original definition bodies were compared with the repository
and are unchanged. The required delivery command performs the final preflight.

Updated the item's proof steps and dependencies to this route. No target, existing
statement, definition body, source-library declaration, or consumer was changed.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.ProEtale.lattice_pullback` (`lem-sfb-lattice-pullback`).
Added zero holes; zero remain in the delivered modules. Both new support theorems,
`SheafOfModules.finiteLocallyFree_pullback` and
`AlgebraicGeometry.ProEtale.LatticePullbackProof.continuousCoefficientInverseImageMap_isIso`,
are proved. No unfinished result was split off.

## No longer needed

Removed the redundant proof imports
`Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
`Mathlib.CategoryTheory.NatTrans`,
`Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`, and
`Sheaf.Paper.ContinuousCoefficientRealizations`. Required finite-limit and covering
APIs remain available from the unchanged public imports.

The proof no longer uses the ordinary tensor comparison theorem of
`lem-pur-proetale-inverse-image-tensor-comparison`: the scalar-extension comparison
comes from double mates of the existing restriction/pullback comparison. Its module
remains a public import because the unchanged section definition uses
`ProEtaleTensorComparison.inverseSection`; no withdrawal is claimed.

`lem-sfb-proetale-object-inverse-image-restriction` is unnecessary for this argument:
the more general localized ringed-site module comparison pulls the local bases.
`lem-sfb-coefficient-pullback-square` is unnecessary: naturality of the actual
coefficient adjunct follows directly from its defining sectionwise map.
`lem-weil-pbc-continuous-coefficient-realizations` is replaced by the already proved
universe-polymorphic `lem-sfb-continuous-ring-universe-realization` in the new
coefficient helper. The condensed `lem-sfb-alpha-iso` remains used there, and the
inverse-image finite-limit and covering APIs remain used by the main proof.
These dependencies are removed from the item's own proof list where applicable;
no claim is made that another target or upstream theorem ceases to need them.

## Where the brief, the DAG or earlier work was wrong

The planned tensor calculation is valid, but the existing restriction/pullback
adjunction comparison gives a shorter formal route and preserves the exact unit
normalization. The continuous-coefficient realization needed by the first step
already exists for general topological rings in the scheme universe. Applying
inverse image directly to two definitionally equal presentations was expensive;
an explicit identity isomorphism between those presentations avoids that unfolding.

The unit route is retained: this module still proves restriction of an actual
integral lattice, with locally finite free source and target, and rationalization
induced by the specified inclusion. Rank zero, varying local ranks, empty schemes,
and identity or arbitrary scheme morphisms require no extra assumptions.

## New nodes

`lem-sfb-continuous-coefficient-inverse-image-iso` records the proved invertibility
of the actual adjunct of precomposition for totally disconnected topological
commutative rings. It uses the existing continuous realization, chart naturality,
and normalized forgetful comparison. Its new module is
`Sheaf.Paper.ContinuousCoefficientPullbackIso`.

`lem-sfb-finite-locally-free-ringed-pullback` records the proved transport of finite
local bases along a continuous, cover-preserving, finite-limit-preserving ringed
site functor. It uses the existing slice-pullback comparison and Mathlib's free
module pullback isomorphism. Its new module is
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreePullback`.

No change record is needed: no existing statement or definition changes.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
