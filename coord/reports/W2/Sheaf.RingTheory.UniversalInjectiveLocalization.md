## What changed

Proved `LinearMap.universally_injective_localizedModule_map` in
`Sheaf.RingTheory.UniversalInjectiveLocalization`, without changing its statement,
universes, public imports, or definitions. The proof follows Stacks Project,
Algebra, Tag 05CM(1), and all three steps of the existing DAG plan.

For any test module L, tensor symmetry converts the hypothesis to injectivity
of the S-linear map M tensor L → M' tensor L. Mathlib's
`IsLocalizedModule.rTensor` identifies localization of these tensor products
with tensoring the canonical localization maps. The equality between the
induced localized map and the tensor of `LocalizedModule.map T f` follows
by `IsLocalizedModule.linearMap_ext`, then checking pure tensors. Applying
`IsLocalizedModule.map_injective` and tensor symmetry proves the conclusion.

The declared dependencies were read before writing the proof:
`def-weil-pbc-module-localization` is Mathlib's `LocalizedModule`, and
`lem-weil-pbc-localization-tensor-over-base` is `IsLocalizedModule.rTensor`.
Both are used. LeanFinder, Loogle, the server grep search, and local searches
in Mathlib, Sheaf, and WeilConjectures found these ingredients but no exact
replacement theorem. No additional imports were necessary.

## Proved and sorry left

Closed the one existing hole:
`LinearMap.universally_injective_localizedModule_map`
(node `lem-trf-local-universal-injective-localization`).

One of one holes proved; zero holes added, zero split off, zero sorry left.
The module compiled cleanly through `lcompile.py` (1.8 seconds).

## No longer needed

None. No imports were removed, and both declared dependency nodes remain
needed. No modules or unit steps were bypassed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The planned proof works with the
existing Mathlib interfaces. Tensor symmetry is applied before localization
so that the S-action is on the first tensor factor, as expected by Mathlib's
`TensorProduct.AlgebraTensorModule.rTensor`. The existing proof dependencies
and unit route remain unchanged.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
