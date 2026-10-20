## What changed

Proved `AlgebraicGeometry.Scheme.finiteExtension_properBaseChange` without changing its
signature or the rational component definition. All original public imports remain.
Added three proved private helpers: a degreewise coefficient round-trip isomorphism,
reflection of invertibility for the transported Koszul unit, and quotient-tower
completeness of integral constructible objects. The proof obtains the four membership
witnesses from identity squares of the existing integral corollary, identifies the
specified exchange with its integral natural isomorphism, and maps the resulting full-
subcategory isomorphism through rationalization.

Added proof imports for completed-exchange identity coherence, pullback pasting, field
Krull dimension, uniform-complete isomorphism closure, and the existing constructible-
completion lemma in `Sheaf.Paper.WeilTensorProduct`. Updated the item's proof plan and
proof dependencies to match this argument. No public interface or target changes.

Verified the entire sandbox with `lcompile.py --all`: clean single-file compilation,
about ten seconds. The saved search log contains LeanFinder, Loogle and grep searches;
the library supplied the shorter functorial-isomorphism route.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.finiteExtension_properBaseChange`
(node `thm-weil-pbc-finite-extension`).

Added zero holes and split off zero theorems. No `sorry` remains in the delivered
module. The proof uses already stated theorems, including the integral corollary,
completion comparison, constructible completeness and isomorphism closure; those
existing dependencies may still have their own holes.

## No longer needed

Removed these proof imports:

- `Sheaf.Paper.CompletedRlimFunctor`
- `Sheaf.CategoryTheory.ScalarLocalization`
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`
- `Mathlib.LinearAlgebra.TensorProduct.Basic`
- `Mathlib.RingTheory.Localization.Away.Basic`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.PbcQbarCompletedPullback`

The extra left/right derived scalar-linearity argument is unnecessary for this Lean
statement: its rational component is already the image under the actual localization
functor. Therefore it suffices to map the integral isomorphism. The proof no longer
uses `lem-weil-linear-abelian-derived-category`,
`lem-pur-left-derived-from-kflat-class`, `lem-weil-pbc-kinjective-total-derived`,
`prop-weil-pbc-rlim-functoriality`, `prop-weil-pbc-rational-transport`, or a separate
application of `def-weil-linear-scalar-localization`. Removed the obsolete tool-use
approval for `lem-pur-left-derived-from-kflat-class` from the node. The old
`lem-weil-pbc-constant-completion-equivalence` proof dependency is subsumed by the
published `towerComplete_iff_intrinsic` interface; no direct application remains.
These modules can still be transitively needed by retained definitions or other
items; this report claims pruning of this item's direct proof dependencies only.
The original public import `Sheaf.Paper.PbcRationalTransport` stays to preserve the
module's exported interface, although its theorem is unnecessary in this proof.

## Where the brief, the DAG or earlier work was wrong

The former nine-step plan proves scalar linearity and exactness of individual rational
functors beyond the actual theorem's conclusion. Its component definition already
uses `pbcRationalization.map`, so generic preservation of isomorphisms is sufficient.
The integral corollary states preservation of two composites, so the individual
membership witnesses genuinely require the auxiliary identity-square argument.

The existing `wfConstructible_complete` theorem (node `def-wf-tensor-product`, another
unit) is used solely as the library's available constructible-completeness comparison
for every generating tuple on the canonical representative. It is not used to bypass
the proper-base-change unit's route; all proper-base-change input still comes from
`cor-weil-pbc-constructible-complete`. Its explicit proof docstring says it transports
the first defining membership condition and makes it independent of tuple and
representative. This existing tool avoids restating that comparison as a new hole.
The coefficient-restriction tool `lem-weil-pbc-ring-sheaf-change-adjunction` supplies
exact conservative restriction; the derived reflection and representative transfer
are proved in this module. No new tool-use approval was written by the worker.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
