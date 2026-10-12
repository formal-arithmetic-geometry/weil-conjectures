## What changed

Replaced the sole proof hole in `AlgebraicGeometry.localizedCohomology_mayerVietoris`
without changing its signature, universes, hypotheses, visibility, or conclusion.
The proof constructs the nonvanishing open using the existing
`nonvanishing_section_trivializes`, proves its two distributive lattice identities,
and uses `module_mayerVietoris` to supply the lower row and restriction-compatible
module-natural connecting transformations. It assembles the upper row and comparison
squares from smaller intermediate statements.

Added four modules, one declaration and one node per module:

- `Sheaf.Paper.CohomologySectionDivision`: division on individual twists before forming fractions.
- `Sheaf.Paper.CohomologyFractionComparison`: proved direct-sum extension and quotient descent.
- `Sheaf.Paper.CohomologyFractionMayerVietorisExact`: upper-row construction and exactness.
- `Sheaf.Paper.CohomologyFractionMayerVietorisSquares`: proved all three comparison squares.

The comparison proof explicitly kills the closure of the fraction relations, then
uses `QuotientAddGroup.lift`. The squares proof derives composition of open cohomology
restriction using `NatTrans.rightDerived_comp`, proves additive extensionality for the
fraction quotient by quotient/direct-sum induction, and checks the squares on generators.
For the boundary it composes the given restriction-naturality square with the two
lattice-identification restriction maps and uses naturality in the multiplication morphism.

All five modules compiled together through `lcompile.py --all`, without warnings.
Several intermediate single-file compiles checked the quotient proof, restriction
composition, generator extensionality, and the boundary square. One attempt timed out
under concurrent load; specifying the parameters of fraction extensionality explicitly
made the subsequent final compile complete within the per-file limit.

Read Stacks Tags 09MR and 01EB online because their local literature files are absent.
Mathlib searches: LeanFinder returned generic MayerVietorisSquare short complexes;
Loogle returned additive exactness transport/kernel-range lemmas; grep found generic
Mayer--Vietoris infrastructure, DirectSum.toAddMonoid, QuotientAddGroup.lift, and the
project's already existing fraction presentation. LeanSearch returned an Internal
Server Error, recorded as unavailable without a mathematical verdict.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.localizedCohomology_mayerVietoris`
(node `lem-sc-invert-s-cohomology-mayer-vietoris-diagram`).

New intermediate declarations proved completely in Lean:

- `AlgebraicGeometry.exists_cohomologyFraction_comparison`
  (`lem-sc-cohomology-fraction-comparison`).
- `AlgebraicGeometry.cohomologyFraction_mayerVietoris_squares`
  (`lem-sc-cohomology-fraction-mayer-vietoris-squares`).

Every remaining delivery hole is a public named theorem whose entire proof is `by sorry`:

- `AlgebraicGeometry.exists_cohomologySection_division`
  (`lem-sc-cohomology-section-division`): construct the division maps on individual
  twisted cohomology groups, prove transition compatibility, and prove bijectivity
  of multiplication on the nonvanishing open. It has no quotient, upper row, or squares.
- `AlgebraicGeometry.exists_cohomologyFraction_mayerVietoris_exact`
  (`lem-sc-cohomology-fraction-mayer-vietoris-exact`): construct the upper additive
  maps and prove their exactness from the supplied module-natural exact sequence.
  It has no nonvanishing open, lower-row construction, comparisons, or squares.

This is a decomposition: one original hole closed, two holes added, net minus one
before any pruning or shared dependency effects. It is not an axiom-free proof of
the full theorem. Existing imported declarations retain their existing dependencies.
There are no holes in definitions, private helpers, or partially completed proofs.

Edge cases checked mathematically: for s=0 the nonvanishing open is empty and the
comparison targets vanish; in numerator degree zero division is restriction; in
cohomological degree zero the initial injection is explicitly retained; empty opens
and zero modules are allowed; the difference map keeps the negative V sign. The
new comparison and square theorems need no quasi-coherence or compactness, since
restriction and an invertible section suffice. The exactness theorem uses only
module naturality and exactness of the supplied family on individual twists.

## No longer needed

Removed the following four proof-only imports and their direct proof dependencies:

- `Sheaf.Algebra.Module.GradedLocalizationExact`
  (`lem-sc-graded-localization-exact`). The explicit quotient can be treated as a
  sequential direct limit: move finite sums to a common denominator and use the
  eventual-zero criterion. A graded ring/module construction is unnecessary for
  this route.
- `Sheaf.AlgebraicGeometry.QuasiCoherentMayerVietorisOpenCover`
  (`lem-sc-mayer-vietoris-open-cover`). Its underlying general ringed-space theorem
  already gives precisely the natural transformations needed by this statement.
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
  (`lem-weil-pbc-right-derived-universal-delta-functor`). Connecting-map naturality
  is already the naturality of the transformations supplied by module Mayer--Vietoris.
- `Sheaf.Paper.PQFCohomology` (`pqf-def-cohomology`). The existing open cohomology
  definition and derived restriction maps already compute the groups in the statement.

Also removed the unused exactness import from the new division module and the
unused ample import from the new upper-row module. The division module imports
open cohomology and tensor-power section constructions directly.

These nodes are unnecessary on this item's direct proof route; this delivery does
not claim they are globally unreachable from every target. No public imports changed.
The unit record has only `thm-sc-proper-cohomology` as its realized statement and no
realized steps; this below-unit reduction bypasses none of its mandated route.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or interface correction. The original DAG planned a graded
localization argument, but its generic graded exactness theorem does not directly
provide maps on the concrete quotient presentation used by the item's signature.
The explicit direct-limit formulation isolates that bridge in the upper-row theorem.
The quasi-coherent open-cover specialization also presents connecting maps as
objectwise arrows on an open subscheme; the underlying ringed-space result supplies
the natural transformations on all modules that the item's signature asks for.

The two residual arguments have complete source-based natural-language proofs in
their docstrings and nodes. They are strictly separate pieces, and neither is the
original theorem with renamed or repackaged hypotheses. There are no forced
adaptations and no changes to target statements or definitions.

## New nodes

`lem-sc-cohomology-section-division` records invertible multiplication and compatible
division on individual twists, in `Sheaf.Paper.CohomologySectionDivision`. It uses the
existing nonvanishing-section trivialization as a tool; that supplies the local
isomorphism, while open cohomology and injective restriction identify its cohomology map.

`lem-sc-cohomology-fraction-comparison` records the proved extension of division maps
through direct sums and quotient relations, in `Sheaf.Paper.CohomologyFractionComparison`.

`lem-sc-cohomology-fraction-mayer-vietoris-exact` records the independent upper-row
construction and exactness step, in `Sheaf.Paper.CohomologyFractionMayerVietorisExact`.
Its complete proof describes both the common-denominator/eventual-zero criterion
and the lifting of kernel classes at sufficiently large twists.

`lem-sc-cohomology-fraction-mayer-vietoris-squares` records the proved restriction,
difference, and boundary squares, in `Sheaf.Paper.CohomologyFractionMayerVietorisSquares`.
It assumes generator formulas and restriction-compatible boundaries, without assuming
exactness. The main item's node now follows the actual five-dependency Lean proof.
No change record is needed because no existing signature or definition changed.

## Second reading by B2

1. **Unchanged interfaces — pass.** Compared the existing module with the repository
   using `diff -u`: only the four removed/five added proof-only imports and the proof
   body differ. The theorem signature, universes, hypotheses, conclusion, visibility,
   and docstring are byte-for-byte unchanged; public imports are unchanged. There
   are no adapted existing modules or changed definitions and no change record is
   required. The existing node differs only in proof, proof_deps, and proof_origin.
2. **Proof and trust boundary — pass.** Independently compiled all four new modules
   and the main module through lcompile.py. The main module initially timed out;
   replaced the final refine with one exact tuple whose lattice witnesses are
   explicit, and the repaired main module compiled in 26.9 seconds. Reviewed
   quotient descent, restriction composition, generator extensionality, the minus
   sign in the V summand, and boundary naturality line by line. Exactly the two
   named full-theorem sorries listed above remain; no axioms, unsafe/opaque/extern
   declarations, hollow definitions, or choices defining arbitrary data are added.
   Existential elimination here takes local proof witnesses, not data definitions.
3. **Split statements — pass.** Read both residual signatures and their complete
   docstring proofs. Division needs neither quasi-coherence nor compactness:
   restriction of an injective resolution computes cohomology on the open, and
   the restricted multiplication is an isomorphism. Exactness is preserved by
   the directed system of twists: tensor coherence gives composable transitions,
   finite relations move to a common denominator, and eventual vanishing permits
   applying the supplied exactness at that twist. Checked s=0, empty opens, zero
   modules, degree zero (including the initial injection), U=V, and denominator
   increment zero. Neither statement contains the whole diagram. Independently
   searched LeanFinder for filtered-colimit exactness, Loogle for iso preservation
   (the service did not recognize its requested identifiers), msearch grep for
   of.zero_exact/free-generator/derived-iso lemmas, and rg in both project roots.
   Mathlib has AddCommGroup.DirectLimit.of.zero_exact and filtered colimits; these
   require identifying this concrete fraction quotient and its transition system,
   so neither is an exact replacement. The existing FractionZeroTensorPower lemma
   only treats vanishing of a whole fraction group and does not give upper-row
   maps/exactness. Neither remaining hole can be closed by a short existing lemma.
   Sources checked online: [09MR](https://stacks.math.columbia.edu/tag/09MR),
   [01CY](https://stacks.math.columbia.edu/tag/01CY), and
   [01EB](https://stacks.math.columbia.edu/tag/01EB).
4. **Route and pruning — pass.** Every old direct proof dependency is listed under
   No longer needed. The general module Mayer--Vietoris theorem supplies exactly
   the module-natural and cover-restriction-natural lower row. Each new proof-only
   import is used; the public imports in new modules supply signature notions.
   The unit sk-thm-curveestimate has only thm-sc-proper-cohomology as its realized
   statement and no realized steps, so this below-unit route bypasses none. One
   original hole closed and two added remains a decomposition, net minus one,
   not a proof of the full theorem without sorryAx. No global pruning is claimed.
5. **DAG agreement — pass.** Checked the existing node's three proof steps against
   the actual witness assembly and its five proof dependencies. All four new
   nodes have source, self-contained statement, statement dependencies, proof
   steps and their dependency union, proof origin, search records, created and
   blueprint records, matching chapter/unit, and verbatim Lean theorem signatures.
   The division node correctly records the nonvanishing and injective-restriction
   tools needed by its unproved argument; comparison and squares accurately
   record their proved reductions.

Second reading changed only the final witness assembly in the main proof, corrected
a punctuation typo and made the division node's proof-origin citation specific to
01CY/01E1, and appended this review. No mathematical statement or remaining-hole
count changed.

Validation completed: deliver3.py --no-push printed OK and review class CODEX.
An import-only scratch module checked #print axioms for all five public declarations:
each lists exactly propext, Classical.choice, Quot.sound, and sorryAx (the two new
open statements and existing upstream holes remain). The scratch module was removed.
The delivery tool also ran its declaration axiom probes. No prohibited axiom appeared.
Repeated gate attempts encountered load-dependent timeouts in the squares file; a
temporary profiling copy compiled in 40.6 seconds and showed substantial linting time,
with no single expensive tactic. All profiling files/options were removed, and the
final complete dry run passed with the ordinary checks enabled.
