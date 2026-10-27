## What changed

Filled `AlgebraicGeometry.Etale.nonempty_iso_constructible_compact_support_base_change`
without changing its signature, existing public imports, or its parent consumers.
The proof follows the compactification route: prove invertibility of each proper-refinement
unit by complementary open/closed restrictions; compare two compactifications through their
common refinement; then compose the proper exchange with exact extension-by-zero exchange.
The three stalk lemmas are proved private helpers. No data is chosen from an unproved
existence theorem: all object isomorphisms use specified comparisons and their inverses.

Added `Sheaf.SixFunctors.GrothendieckTorsionProperBaseChange`, with a complete proof reducing
bounded torsion proper base change to its sheaf case. It reuses the existing library Postnikov theorem
`DerivedCategory.exists_iteratedExtensions_of_bounded` and the triangulated isomorphism
locus `NatTrans.isoLocus`, rather than duplicating finite-range induction. Shift
compatibility places each single homology sheaf in that locus; extension closure
then gives the bounded result. No uniform cohomological-dimension bound is assumed.

Added `Sheaf.SixFunctors.GrothendieckTorsionSheafProperBaseChange` for the genuinely separate
proper-base-change theorem on a single sheaf. Its sole remaining hole is the extension from
module coefficients to general Grothendieck abelian coefficients. The docstring and node
specify the coefficient-localization/hypercover argument, including passage from the
factorial-kernel filtration to stalkwise finite exponent. This is the sheaf case of proper
base change, not compact-support base change under another name: there are no
compactifications, change-of-compactification units, or finite truncation induction in its
statement.

All proof imports are private. No source-library file, existing public definition, target,
or consumer has been changed. The original node now records the actual argument and the
two new result nodes. Compilation through `lcompile.py --all` passed for all three modules,
with no warnings after reusing the library Postnikov devissage: 3.0 s for the sheaf
statement module, 24.0 s for the bounded reduction, and 26.7 s for the assigned module.
The delivery tool runs the required full packet checks.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.nonempty_iso_constructible_compact_support_base_change`.
There are zero `sorry`s in the assigned module.

Also proved the new declaration
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_bounded_stalkwise_finite_exponent`
(node `lem-sf-grothendieck-torsion-proper-base-change`), by the existing bounded Postnikov devissage and the shift-compatible isomorphism locus.
This new module has zero `sorry`s.

Added exactly one hole:
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_single_of_stalkwise_finite_exponent`
(node `lem-sf-grothendieck-torsion-sheaf-proper-base-change`), in
`Sheaf.SixFunctors.GrothendieckTorsionSheafProperBaseChange`.
Its proof is exactly `by sorry`. No other hole is left or added by this packet.

Thus this is a decomposition: one original hole closed and one lower hole added, net zero
holes closed. The compactification comparisons and finite truncation argument are proved;
proper base change with general coefficient sheaves remains unproved. The zero sheaf,
empty schemes, the identity square, a zero-length cohomology interval, and a single
nonzero cohomology degree have been checked in the mathematical argument; the library
Postnikov theorem includes the acyclic and empty-support cases.

## No longer needed

No existing module or node is withdrawn, and no existing public import is removed.
All original statement dependencies remain necessary to state the unchanged theorem.
No complete proof or downstream use in the adopted source library has been removed.

For the proof, constructibility and the finite-Tor condition are used only through the
boundedness component of `constructibleFiniteTor`. No constructibility-preservation or
finite-Tor-preservation theorem is needed for either inverse image or extension by zero.
There is no need for a general unbounded compactification-independence isomorphism, a
finite-coefficient-ring assumption on A, a uniform cohomological-dimension theorem, a
qcqs hypothesis on the entire base scheme, or a proof that A is a module category.
The existing common-refinement construction `Compactification.inf` works with the given
quasi-compact morphism, so the stronger base-qcqs common-dense-refinement statement
`det-nagata-refinement-common-dense` and its module
`Sheaf.Compactification.CommonDenseRefinement` are not imported or used here. This does
not withdraw those declarations or claim that other consumers no longer need them.

The original proof dependencies on `def-kun-derived-tensor`, `def-pc-scheme`,
`def-sp-grothendieck-abelian`, and `def-weil-abstract-derived-category` are retained as
statement dependencies but removed from `proof_deps`: they name the ambient definitions,
not the proper-base-change result that the proof actually requires. The revised
`proof_deps` names the sheaf-stalk facts, open/closed conservativity, open exchange,
compactification refinements, and the new bounded proper comparison.

## Where the brief, the DAG or earlier work was wrong

The original DAG did not state the general-coefficient proper-base-change theorem as a
proof dependency. Its first step described finite calculations as additive, but this is
not an application of the existing proper-base-change declarations: those take abelian
groups or `ModuleCat R`, while the assigned theorem quantifies over an arbitrary concrete
Grothendieck abelian category A. The distinction remains even though the supplied torsion
hypothesis annihilates the whole stalk object. The new sheaf node isolates precisely this
coefficient extension. SGA 4's cited statements themselves concern ring/module
coefficients; the extension in the new docstring is explicitly an agent-written argument
using exact localization and the existing Grothendieck-coefficient hypercover comparison.

In particular, Gabriel--Popescu's right adjoint is not treated as exact or as preserving
filtered colimits, and an arbitrary Grothendieck abelian category is not asserted to be
equivalent to a module category. The proposed coefficient proof instead uses its exact
cocontinuous left localization and computes cohomology on the coherent etale basis.

The available bounded-complex triangulated-devissage declaration concerns the terms of a
strictly bounded representative. Our torsion hypothesis is on homology sheaves. The
implemented reduction therefore uses the library Postnikov theorem and the homology sheaves,
without asserting that a bounded representative has finite-exponent terms.

## New nodes

`lem-sf-grothendieck-torsion-proper-base-change` attaches the proved bounded-complex
proper-base-change reduction in `Sheaf.SixFunctors.GrothendieckTorsionProperBaseChange`.
It inherits the assigned chapter and unit; its proof uses the separate sheaf comparison
and reuses the library's proved finite Postnikov decomposition and triangulated
isomorphism locus.

`lem-sf-grothendieck-torsion-sheaf-proper-base-change` attaches the remaining sheaf theorem
in `Sheaf.SixFunctors.GrothendieckTorsionSheafProperBaseChange`. Its source is the sheaf
proper-base-change theorem and the coefficient argument described in full in its node
and docstring. Mathlib natural-language, type-pattern and source searches and a search of
the current blueprint found no theorem with these Grothendieck coefficients. The existing
abelian and ring-module proper-base-change nodes are reused in its proof plan.

No definition/signature change record is necessary: no existing statement or public
definition changes, and no forced adaptation is made.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
