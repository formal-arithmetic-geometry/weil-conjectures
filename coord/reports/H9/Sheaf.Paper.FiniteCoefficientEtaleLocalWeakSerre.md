## What changed

Replaced the sorry body of `AlgebraicGeometry.Scheme.finiteCoefficient_etaleLocal_weakSerre`
by a categorical proof using the existing `finiteCoefficientSliceRestriction`,
`proEtaleModuleEncoding`, `intrinsic_fixedModels`, and `proEtale_fp_localModels_serre`.
One new local-model comparison, `finiteCoefficient_etaleLocal_encoding`, bridges the
remaining difference between the two covering-sieve conditions. The original statement,
universes, public imports, and docstring are unchanged. New imports are proof-only.
The main proof constructs its exact functor explicitly: existing fixed-scalar chart
restriction followed by the inverse of the existing constant-scalar module equivalence.
It uses the counit to compare models, transfers canonical kernels and cokernels,
handles arbitrary limiting forks and colimiting coforks by comparison isomorphisms,
and maps short exact sequences for the extension clause. The node follows this argument.
No existing module other than the assigned item is changed.

## Proved and sorry left

Closed the original body hole in
`AlgebraicGeometry.Scheme.finiteCoefficient_etaleLocal_weakSerre`.
The item contains zero sorry bodies. One new hole is left in
`AlgebraicGeometry.Scheme.finiteCoefficient_etaleLocal_encoding`, node
`lem-weil-pbc-finite-coefficient-etale-local-encoding`.

This is a decomposition, not a net hole reduction: one hole closed and one added.
The new theorem compares the two local-model conditions for one sheaf under the
existing chart restriction. It contains no functor-existence, exactness, kernel,
cokernel, or extension conclusion. The original closure theorem uses the already proved
intrinsic weak Serre theorem in substantive Lean code. The remaining comparison has its
source and full proof in words in its docstring. No definition chooses data from it.

Both final modules compiled cleanly on the server, without warnings: 7.7 s for
`FiniteCoefficientEtaleLocalEncoding` and 10.0 s for `FiniteCoefficientEtaleLocalWeakSerre`.
The original signature and docstring were checked byte-for-byte. All Lean lines are at
most 100 characters. The delivery repeats the required mechanical checks.

## No longer needed

No existing public import is removed, and no module is withdrawn. No mathematical
prerequisite is globally pruned: ringed localization, constant realization, and etale
chart descent are still needed by the new comparison. The closure module itself needs
only the existing exact coordinate restriction, existing intrinsic encoding comparison,
the new local-model comparison, and existing intrinsic weak Serre closure. Neither
etale descent nor constant-module transport is duplicated in the closure proof.
The unit statement and its steps remain intact.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies are mathematically sufficient but their Lean encodings do not
compose directly. The Serre theorem concerns intrinsic modules on a chart scheme; the
item concerns global R-modules, concrete pro-etale slices, `completedAdicChange`, small
finite module representatives, and etale covering sieves. The existing
`finiteCoefficientSliceRestriction` already constructs the exact coordinate functor,
so this construction does not need a new existence theorem. The new node isolates
only the local-model comparison. `coefficientFpLocalSystem_etaleCover` supplies charts
on a coefficient-sized site, rather than this comparison. Existing slice-heart origin
and derived model transport were inspected: the former supplies one-way etale origin
with a marking, and the latter transports supplied derived complexes; neither states
the required equivalence of these two local-model conditions.

The blueprint ancestor command reports `None` for the item: its creation chain names Lean
modules rather than DAG ids. The new node retains that unresolved ancestor and records the
precise original proof steps it serves. The blueprint search for finite locally constant
nodes found no duplicate of this coefficient-and-slice comparison.

## New nodes

`lem-weil-pbc-finite-coefficient-etale-local-encoding`, in
`Sheaf.Paper.FiniteCoefficientEtaleLocalEncoding`, compares the displayed etale-local
models with `ProFiniteModels.fixedModels` of the existing fixed-scalar chart restriction.
The proof uses normalized constant-module comparisons, promotes etale covers to pro-etale
covers in the forward direction, and uses Tag 099Y etale charts and finite representatives
in the reverse direction. Source passages read: proetale.tex,
`lemma-compare-locally-constant` (Tag 099Y); sites-modules.tex,
`lemma-kernel-finite-locally-constant` (Tag 093U). LeanFinder returned finite-presentation
predicates and condensed-module constructors; Loogle and Mathlib grep returned no match.
Project searches found the intrinsic encoding comparison and the exact chart restriction,
but no equivalence of these local-model conditions. Empty charts and the zero ring
satisfy both conditions. Disconnected charts allow different models on different covering
members, and no global constant model is asserted.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
