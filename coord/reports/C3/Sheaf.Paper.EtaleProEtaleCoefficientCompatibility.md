## What changed

The sum clause of `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` is reduced to
`AlgebraicGeometry.Etale.etaleSumScalarRepresentative`, a normalization equation for the
sum/scalar derived mate on a bounded flat cochain representative. The new theorem has no
compactification or compact-support comparison in its statement. The assembly uses the
existing sheetwise coefficient computation, proves that the supplied normalization has
the graph sheaf map by monomorphism cancellation, identifies its derived boundary using the existing bounded-model equation, cancels
the scalar representative and the comparison isomorphisms, and transports the result to
the given object by naturality.

Local irreducibility declarations and proved private cached instances keep the large derived functors
abstract during elaboration. Existing public signatures and definitions are unchanged.

## Proved and sorry left

Original holes: 2. Closed by decomposition: 1,
`AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility_sum`
(node `lem-sp-et-proet-coefficient-compatibility`).

One original hole remains:
`AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility`
(node `lem-sp-et-proet-coefficient-compatibility`).

One hole is added:
`AlgebraicGeometry.Etale.etaleSumScalarRepresentative`
(node `lem-sp-etale-sum-scalar-representative`). This is a decomposition, with net hole
change zero; the new equation is only the derived-mate normalization step, and the
compact-support assembly is proved separately.

## No longer needed

No modules are withdrawn and no existing public imports are removed. The temporary private
import of EtaleProEtaleScalarMate used only for instance caching is removed; its small
proved cache helpers are local instead. The sum clause uses
the direct flat constructible model theorem rather than the larger finite coefficient
input model package; that package remains in the plan for the separate site clause.
No dependency needed by that unfinished clause or the existing refinement, composition,
counit and naturality proofs is pruned.

## Where the brief, the DAG or earlier work was wrong

The sum computation names the degreewise scalar map, whereas `sumCoefficientIso` is fixed
by a conjugate of derived adjunctions. Their representative normalization is a separate
step, now explicitly stated. The normalizations also use two presentations of the same
right-derived unit; the assembly includes their identification. The bounded-model theorem
already exposes the inverse-comparison equation, so no new generic localization theorem
is needed.

## New nodes

`lem-sp-etale-sum-scalar-representative` states the representative equation for the derived
sum/scalar conjugate. Its source is Stacks 06YY, 03S5 and 0GL6. It is strictly a normalization
of the sum/scalar mate; it does not assert compact-support coefficient compatibility.
No definition or statement change record is required.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
