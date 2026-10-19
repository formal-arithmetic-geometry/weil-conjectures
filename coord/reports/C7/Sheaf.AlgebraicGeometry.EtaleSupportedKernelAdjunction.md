## What changed

Proved `AlgebraicGeometry.Etale.supportedKernel_closedAdjunction` with its exact existing
signature and definitions unchanged. A proved private natural isomorphism compares the
functor-category kernel with the library's objectwise `sectionsWithSupport` functor.
The existing `isZero_upperStar_sectionsWithSupport` and
`isIso_upperStarLowerStarAdjunction_unit_app_of_isZero` then prove invertibility of the
specified canonical unit. Exactness is supplied by the finite-direct-image instances.
Transport `lowerStarClosedUpperShriekAdjunction` along the comparison whiskered by inverse
image to obtain the required right adjoint. All reused declarations are in
`WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek`.

Updated the theorem node's proof to record this reuse of the original support/kernel
argument. Its unit's `realized` fields are unchanged; no unit step is bypassed.
All new imports are proof-only. No other module is adapted.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Etale.supportedKernel_closedAdjunction`
(node `lem-pur-etale-supported-kernel-adjunction`).
One of one original holes proved, zero holes added, zero split off, zero holes remaining.
The private kernel comparison is fully proved. No new statement, definition repair,
or new assumption is involved.

The final module compiled with lcompile.py without errors or warnings. Delivery preflight
also compiles the module and checks declaration axioms.

## No longer needed

Removed these standalone proof imports:

- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact` (both duplicate occurrences)
- `Sheaf.AlgebraicGeometry.OpenImmersionRestriction`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm` (both duplicate occurrences)
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`
- `WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion`

Finite exactness and closed full faithfulness remain used transitively by the existing
closed-support library. They are not claimed as globally pruned. The separate sheaf support
and Leray modules are unnecessary for this proof. Removed the explicit stalk-comparison
and stalk-conservativity dependency edges `lem-weil-pbc-inverse-image-stalk-germ` and
`lemma-weil-pbc-geometric-stalk-conservative` from this node: the existing library's supported
sheaf identification supplies this step directly. Stalk machinery may remain transitively
needed by that library. No library file is withdrawn, and global reachability is left to
the maintainer's ledger.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound, but its sheaf-level kernel and adjunction argument
already exists in `ClosedImmersionUpperShriek`. Only the natural comparison between the two
kernel constructions was needed. No disputed statement or tool workaround.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
