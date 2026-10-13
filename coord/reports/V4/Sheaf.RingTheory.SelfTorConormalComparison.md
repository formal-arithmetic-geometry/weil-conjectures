## What changed
Moved `AlgebraicGeometry.conormalExteriorModule` verbatim to
`Sheaf.RingTheory.ConormalExteriorModule`, and `AlgebraicGeometry.IsSelfTorConormalComparison`
verbatim to `Sheaf.RingTheory.SelfTorConormalComparisonPredicate`. The parent re-exports
both through its public predicate import. This avoids a circular import when its
proof imports the new existence and uniqueness statements. Their signatures and
bodies, and all three remaining original signatures, are byte for byte unchanged.

The target proof obtains a comparison from `selfTorConormalComparison_exists` and
supplies uniqueness using `selfTorConormalComparison_unique`. No arbitrary witness
is used in a definition: the original choice definition still uses the unique
existence theorem, which determines its value.

The interface relocation is documented in
`coord/changes/self-tor-conormal-definitions.md` with verbatim old definitions,
the unchanged new definitions, and all downstream modules. No forced adaptations.

## Proved and sorry left
Closed the original hole in
`AlgebraicGeometry.existsUnique_selfTor_conormal_comparison`
(node `new-r4-self-tor-conormal-comparison`) by an ExistsUnique introduction.
Added two holes, in separate modules:

- `AlgebraicGeometry.selfTorConormalComparison_exists`
  (node `new-r4-self-tor-conormal-comparison-existence`).
- `AlgebraicGeometry.selfTorConormalComparison_unique`
  (node `new-r4-self-tor-conormal-comparison-unique`).

These are respectively the existence and uniqueness parts of the original argument;
neither individually restates the original unique-existence conclusion. This is a
decomposition, not an axiom-free proof of the comparison. One hole closed, two
added; net hole count in the import closure is -1. The selection definition and
its specification remain dependent on sorryAx, as before. The two concrete moved
definitions contain no holes.

## No longer needed
No old proof-dependency node is pruned: the original proof_deps was empty.
No module is shown to leave the targets' closure. The Tate construction, comparison
of lifts, and generation argument are retained in the two new nodes.

The parent's direct imports of Mathlib.RingTheory.Ideal.Cotangent,
Mathlib.Algebra.Category.ModuleCat.Projective,
Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic,
Mathlib.CategoryTheory.Monoidal.Tor,
Mathlib.LinearAlgebra.ExteriorPower.Basic,
Mathlib.Algebra.Category.ModuleCat.ChangeOfRings, and Sheaf.Paper.KoszulComplex
are supplied publicly by the two foundational modules. This is import relocation,
not pruning of those dependencies. ConormalExteriorModule itself now imports only
Cotangent, ExteriorPower.Basic and ChangeOfRings. Predicate imports its concrete
Koszul, projective-resolution, monoidal-module and Tor dependencies. The two new
lemma imports of the parent are plain proof imports.

## Where the brief, the DAG or earlier work was wrong
The first report named SelfTorConormalComparisonBasics, which was absent, and
claimed that direct Tate/Koszul proof steps were no longer needed. They remain
necessary to prove the existence hole. Its recorded searches were placeholder
claims rather than searches; replaced with actual msearch.py results from this
reading. LeanSearch returned Internal Server Error; LeanFinder, Loogle and grep
ran successfully. Loogle supplies exteriorPower.linearMap_ext and ιMulti_span,
and LeanFinder finds projective-resolution lifting tools, but no full normalized
comparison theorem. Searches of both library roots find only the existing parent
comparison and its users, not another proof.

Stacks Tag 09PQ supplies the strictly graded commutative Tor algebra. Tag 062I
is a regularity lemma, not the general comparison construction. The new proof
outlines therefore explicitly use Tag 00LS for comparison of free complexes with
resolutions and the quotient exact sequence for degree-one conormal classes.
Existing declaration docstrings were preserved.

## New nodes
`new-r4-conormal-exterior-module` records the relocated concrete exterior module.
`new-r4-self-tor-conormal-predicate` records the relocated normalization predicate.
`new-r4-self-tor-conormal-comparison-existence` records the Tate construction and
resolution comparison, with its full proof outline in the Lean docstring.
`new-r4-self-tor-conormal-comparison-unique` records the free Koszul lift and
exterior-generation argument, with its full proof outline in the Lean docstring.
The original comparison node now packages those two parts, and its lean.declarations
list contains the declarations remaining in its module.
Change record: `coord/changes/self-tor-conormal-definitions.md`.

## Second reading by V4
1. Compared the parent with the repository using diff and compared the extracted
   declarations as text. Verdict: the two moved signatures and bodies, and every
   other original signature, are identical. Only imports, declaration locations
   and the target proof changed. No target statement or definition meaning changes.
2. Compiled all five modules through lcompile.py in import order. Explicit
   #print axioms checks cover all seven declarations, including the two new lemmas.
   Verdict: no error, no forbidden declaration or hole in a definition; the only
   nonstandard axiom is sorryAx from the two named new theorem holes. Definitions
   chosen from unique existence satisfy the project rule.
3. Checked the existence and uniqueness arguments separately, including n=0,
   I=0, I=A and characteristic two. Verdict: both are true and strictly parts of
   the original argument. The uniqueness outline needs existence of Koszul lifts
   and cycle preimages, now made explicit. Searched with alternate semantic queries,
   Loogle and rg; found useful extensionality/lifting tools but no exact full result.
   Neither remaining statement can be closed in a few minutes with these tools.
4. Read the original proof plan and sk-thm-picard-duality.realized. Verdict: the
   same Tate/Koszul normalization and exterior-generation route is retained;
   the item does not occupy any realized slot, so none is bypassed or altered.
   Removed redundant direct imports, retained all mathematical dependencies,
   and corrected No longer needed to claim no module/node pruning.
5. Compared node Lean records, proof steps and dependency unions with the modules.
   Verdict: the parent uses exactly the two intermediate theorems; new definitions
   have definition-kind nodes and actual statements; every new signature is recorded
   verbatim. Replaced placeholder searches and generic proof-step descriptions.

Changed in this reading: redundant imports, proof docstrings of the new unlanded
lemmas, new-node statements/dependencies/searches/proof outlines, the definition
relocation record, and this report. No existing theorem signature or definition
body was changed. This delivery remains a decomposition with two open theorems.
