## What changed

Proved `CategoryTheory.completed_localized_adjunction_square` with its signature unchanged.
All additional constructions are private, proved helpers in the item module. They construct
base-changed functors, balanced additive lifts into already localized-linear categories,
extended natural transformations, and the localized adjunction. The naturality of the integral
comparison and inverse cancellation prove the transported unit and counit compatibility.
The localized comparisons have exactly the original components, and the final equations
reduce to those integral compatibility equations.

Updated the existing node proof and proof dependencies to record the direct tensor route.
No source-library module, public definition, signature, instance or import was changed.
Added the preflight-required context-change record at
`coord/changes/completed-localized-adjunction-square-private-context.md`.
Its user audit reports no downstream modules; no adaptation is needed.
The complete theorem passed single-file compilation in 10.3 seconds. The one unused
simp argument reported by the linter was removed before delivery.

## Proved and sorry left

Closed the single original hole in `CategoryTheory.completed_localized_adjunction_square`
(node `lem-weil-pbc-completed-localized-adjunction-square`): 1 of 1.
Added holes: none. Remaining holes in this delivery: none. Split-off statements: none.

## No longer needed

Removed the private proof import `Sheaf.CategoryTheory.SemilinearScalarLocalization`.
The proof does not use `lem-pur-semilinear-scalar-localization` or its module. Instead,
`LinearMap.baseChange` and `TensorProduct.liftAddHom` directly construct the required maps.
There is no localization of the primed categories at 1, coefficient-map identification,
triangulated-category argument, or rationalization comparison in this proof.
The node retains the transport, linear-functor, raw scalar-localization and module
base-change dependencies actually used. No declaration or module is withdrawn.

Searches used the provided leanfinder, loogle and grep services, together with local searches
in Sheaf, WeilConjectures and Mathlib. Mathlib supplies the left-isomorphism transport and
tensor base change; no existing declaration states the complete comparison-square result.

## Where the brief, the DAG or earlier work was wrong

The statement is sound and unchanged. Steps 3--5 of the previous plan took a longer route
through the general semilinear localization API and localization at 1. A balanced pairing
into each already B-linear Hom module constructs the desired functor directly. Tensor
induction proves the extension and naturality laws without these detours. The unit route
is preserved: this node is not itself a replacement for any realized unit step.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
