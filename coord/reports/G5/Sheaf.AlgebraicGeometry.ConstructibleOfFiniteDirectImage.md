## What changed

Proved `AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_of_finite_lowerStar`
with its signature unchanged. The proof follows the blueprint's finite-counit route:
convert the constructibility predicate, pull back the constructible direct image,
use the existing epimorphic finite counit, make its kernel constructible, take the
constructible cokernel, and transport along the abelian kernel/cokernel isomorphism.

Added proof-only imports of `WeilConjectures.SixFunctors.Finite.Counit` and
`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`. Kept the existing
constructible-subobject and constructible-cokernel declarations. All four public
imports and all existing signatures are unchanged. No definition or statement repair,
consumer adaptation, change record, or new Lean declaration is required.

Updated the item's proof, proof dependencies and proof origin to reflect these
applications. Pruned its unused `lem-weil-pbc-inverse-image-stalk-germ` tool approval.
Read the current blueprint statement/proof in
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/`.
The unit record `sk-prop-sf-cbc` has no realized statement or proof steps to bypass;
the actual original finite-counit/kernel/cokernel argument is preserved.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_of_finite_lowerStar`
(node `lem-fin-finite-reflects-constructibility`).

Added 0 holes; split off 0 obligations. No `sorry` remains in the delivered Lean file.
This is a proof, not a decomposition. The new DAG attachment names an existing
proved instance and creates no theorem.

The final file compiles through `lcompile.py`. A compiler probe of the proved theorem
and the reused finite-counit instance reports exactly `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`. Empty sources, zero sheaves, and nonsurjective
finite morphisms require no special cases: the counit instance is valid for all of
them. The finite ring and Noetherian source hypotheses feed the subobject theorem;
the original Noetherian target hypothesis is preserved.

## No longer needed

Removed these direct proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`
- `WeilConjectures.SixFunctors.Finite.Stalk`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`

The direct proof no longer cites `def-constructible-constant`,
`lem-pur-scheme-constructible-preimage`, or
`def-weil-pbc-etale-constructible-sheaf`: the existing constructible pullback theorem
and comparison encapsulate the stratification details. The two latter definitions
are still needed for the statement or transitively; this does not assert their
global unreachability.

The direct proof also no longer cites `lem-weil-pbc-finite-stalk-formula-restriction`,
`prop-weil-pbc-geometric-stalks-exact`, or
`lemma-weil-pbc-geometric-stalk-conservative`: they now sit below the already proved
finite counit attachment. Their modules remain transitively imported by that theorem.
The separate abelian germ theorem `lem-weil-pbc-inverse-image-stalk-germ` and its
module `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm` are unnecessary for
this argument: the published module-valued counit proof already computes its stalks.
The `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` wrapper is unnecessary
because the canonical definition is already publicly imported. No global deletion
or withdrawal is claimed for modules which may still have other consumers.

## Where the brief, the DAG or earlier work was wrong

The planned stalk calculation was already implemented and proved in
`WeilConjectures.SixFunctors.Finite.Counit`, but no DAG node attached its epi instance.
Reusing it avoids repeating that proof and the separate abelian germ bridge. The
constructibility comparison was also already proved and supplies the precise bridge
between the stated predicate and the source library's pullback/cokernel API.

No mathematical statement was disputed or changed. The proof neither assumes
surjectivity of the finite map nor replaces the module sheaf by a different
coefficient encoding.

## New nodes

`lem-fin-finite-direct-image-counit-epi` attaches the existing
`AlgebraicGeometry.Etale.epi_upperStarLowerStarAdjunction_counit_app_of_isFinite`
in `WeilConjectures.SixFunctors.Finite.Counit`, specialized to `ModuleCat Λ`.
The module and its complete proof were read, the instance was checked by the
compiler, and its axiom list is standard. The attachment gives a complete proof in
words from the finite-stalk formula and exact conservative geometric stalks, with
Stacks sources 03QP and 03PU. Searches of all DAG Lean records and blueprint counit
statements found no existing attachment of this finite counit epi result. Three
kinds of Mathlib search are recorded from actual launcher searches; Mathlib's
faithful-right-adjoint counit lemma does not itself establish faithfulness of this
finite direct image. No new Lean module and no unproved obligation is introduced.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
