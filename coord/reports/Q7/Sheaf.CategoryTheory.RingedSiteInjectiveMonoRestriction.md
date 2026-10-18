## What changed

Proved `CategoryTheory.injective_ringed_site_mono_restriction` in
`Sheaf.CategoryTheory.RingedSiteInjectiveMonoRestriction`, preserving its signature.
The proof transfers injectivity through the exact module-sheafification adjunction,
then extends a free Yoneda presheaf map along the map induced by the site monomorphism.
Componentwise injectivity follows from `Finsupp.mapDomain_injective` and cancellation.
Naturality identifies the extended section with the required preimage.
The existing node now records this adjunction formulation of the same source argument.
Added the proof import `Mathlib.Algebra.Category.Grp.FilteredColimits` to supply the
small-site sheafification instances. No definitions or statements changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.injective_ringed_site_mono_restriction`
(node `lem-pur-ringed-site-injective-mono-restriction`).
Added 0 holes; 0 holes remain in the delivery. No split-offs.
Single-file compilation succeeds. The axiom check reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the redundant direct proof import
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`: the public statement
import `Sheaf.CategoryTheory.RingedSiteModules` already imports this API.
The sheafification declarations remain used. All five original proof-dependency
nodes remain needed; no node or module is pruned.
The explicit sheafified Yoneda evaluation calculation is packaged by
`Injective.injective_of_adjoint`, rather than introduced as additional lemmas.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The source argument can be expressed directly
with existing Mathlib declarations; no additional intermediate theorem is needed.
The node's proof was updated to match this equivalent adjunction-based proof.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
