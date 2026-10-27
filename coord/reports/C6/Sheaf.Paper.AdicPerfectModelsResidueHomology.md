## What changed

Replaced the proof hole in `AlgebraicGeometry.Scheme.adicPerfectModels_residueHomology`
with the stratified local-model argument. The existing target signature and every
existing definition are unchanged. The proof obtains finite residue cohomology from
`adicPerfectModel_complete_reduction`, constructs its covering sieve of constant finite
models, transports that condition across the coefficient-sized site equivalences, and
uses the sheaf equivalence in `constructibleComparison`. It then proves that the ordinary
etale realization is constructible using finite stalks and the same stratification.
All helper definitions and lemmas in the item are private and proved. The generic
site-equivalence and pullback-square helpers follow the already proved private
arguments in `FiniteComparisonPresentation`; they are specialized here without its
finite-underlying-coefficient assumptions or unrelated encoding imports.

The sole split is the local derived scalar/restriction comparison
`adicResidue_localModelComparison`. This identifies the residue on one specified slice
with the constant algebraic residue complex. It does not assert finiteness, existence
of a stratification, constructibility, or etale descent. The parent proof supplies all
of those steps and commutes exact restriction with homology explicitly. This is a
strictly local part of the source argument, rather than the parent conclusion renamed.

## Proved and sorry left

Closed: the body of
`AlgebraicGeometry.Scheme.adicPerfectModels_residueHomology` (one original hole).
Added: `AlgebraicGeometry.Scheme.adicResidue_localModelComparison`, the only remaining
hole in this packet, in node `lem-sfb-adic-residue-local-homology-comparison`.
This is a decomposition: one upper hole closed and one strictly local hole added,
net zero holes closed. Joint compilation through `lcompile.py --all` passed with
no warnings: the local module took 16.0 seconds and the parent took 54.1 seconds. No sorry occurs inside a definition, a private lemma, or the
combining proof. The local theorem has its source and full intended argument in its
docstring and node.

## No longer needed

No existing public import was removed, and no module is withdrawn. The original
item imported only its statement data. The new proof uses private imports for the
local comparison, the intrinsic comparison equivalence, coefficient-model realization,
Noetherian global constructibility, and finite-stalk facts. Two redundant proposed proof
imports, `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence` and
`Mathlib.CategoryTheory.Functor.Flat`, were removed after checking the retained public
import closures; they are already available through the retained modules.

The item no longer directly uses the weakly-etale localization lemma
`lem-weil-proetale-weakly-etale-localization`; it instead works with the actual covering
sieves on the original sites and their equivalent coefficient-sized site models.
The immersion limit-preservation step has moved to the genuinely local comparison
node, where it is still needed. The Noetherian finite-presentation fact is supplied
by Mathlib `Module.finitePresentation_of_finite`. Complete reduction, global
constructibility, and sheaf comparison remain in the route. No assertion is made
that an indirect dependency has become globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The earlier plan did not provide a declared comparison between the original-site
`sfbResidueComplex`/`sfbLocalRestriction` constructions and the coefficient-sized
completed-model calculation. The new local node states exactly this missing part.
The existing complete-reduction theorem already proves the coefficient calculation
and finite cohomology, so those are reused rather than restated.

The pro-etale source-library predicate based on finite underlying sets is unsuitable
for an infinite residue field. The proof instead uses the intrinsic coefficient
constructibility theorem and finite generation, and proves the connection to the
ordinary etale finite-stalk predicate. Zero complexes and empty slices satisfy the
local comparison, and no finite-cardinality residue-field assumption is introduced.
No target, adopted source declaration, or unit-level route is changed.

## New nodes

`lem-sfb-adic-residue-local-homology-comparison`, in
`dag/nodes/sec-six-functors-basics/`, records the local derived residue comparison for
one specified completed perfect model. Its Lean module is
`Sheaf.Paper.AdicResidueLocalHomologyComparison`; its source is the local residue
calculation in Bhatt--Scholze Proposition 6.6.11 (reverse implication), with the
canonical exact restriction and tensor comparisons written out. It uses the existing
complete-reduction and completed-constant-sheaf-reduction declarations. The parent
node now records the actual combining proof and dependencies. No change record is
needed because all existing public signatures and definitions are unchanged.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
