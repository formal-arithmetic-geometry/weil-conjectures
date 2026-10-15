## What changed

The original public theorem
`AlgebraicGeometry.ProEtale.subsingleton_cohomology_comparisonUpperStar_obj_of_injective_of_isAffine`
now applies the already proved
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` from
`WeilConjectures.CategoryTheory.Sites.CechCriterion`. Two private, fully proved helpers
extract a finite affine ind-etale refinement of a covering sieve and prove that its entire
Čech nerve stays in the basis. These helpers use the existing cover-dense affine-basis
inclusion, finite covering refinement, and preservation of pullbacks and finite products.

Replaced the first worker's auxiliary cohomology equivalence with
`AlgebraicGeometry.ProEtale.exactAt_cechComplex_comparisonUpperStar_of_injective` in
`AffineComparisonInjectiveVanishingAux.lean`. It states just the finite Čech exactness
condition (3) of Stacks 099U; its docstring and node give the complete two-limit-reduction
proof in words. The continuity, descent and injective-Čech proof dependencies remain imported
there for the next worker. The withdrawn, empty `AffineEtaleSiteColimit` module is removed.

The literal signature, visibility and docstring of the existing theorem are unchanged.
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` is public because the signature needs
`Sheaf.H`; a scratch removal test confirms that a private import is insufficient. All added
imports needed only for proofs are private. The first worker's linter suppressions were
removed. The public-import and file-local attribute changes are declared in
`coord/changes/AffineComparisonInjectiveVanishing-imports.md`.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.ProEtale.subsingleton_cohomology_comparisonUpperStar_obj_of_injective_of_isAffine`
(node `lem-cbc-abelian-affine-comparison-vanishing`).

Added exactly one hole:
`AlgebraicGeometry.ProEtale.exactAt_cechComplex_comparisonUpperStar_of_injective`
(node `lem-cbc-abelian-affine-comparison-vanishing-aux`). Its whole proof is `:= by sorry`;
there is no other textual sorry in the delivered files. The first worker's unlanded
`nonempty_cohomology_comparison_iso_of_injective_of_isAffine` was removed, not counted as a
closed repository hole.

This is a decomposition: one original hole closed, one strictly smaller Čech hole added,
net zero holes. The finite refinement and nerve-closure arguments are fully proved.
The item still depends on the named auxiliary sorry; no claim of a closed target is made.
No definitions, arbitrary witness constructions, or custom axioms are added.

## No longer needed

Removed direct imports from the original item module (some are retained as auxiliary
proof dependencies or supplied transitively):

- `Mathlib.AlgebraicGeometry.Sites.Etale`
- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`
- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes`
- `Sheaf.AlgebraicGeometry.FibreProductLimit`
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`
- `Sheaf.CategoryTheory.ExistsDirectedReindexing`
- `Sheaf.CategoryTheory.InjectiveSheafCechAcyclic`
- `Sheaf.CategoryTheory.SiteCechVanishingCriterion`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.RingTheory.IndEtaleStability`
- `Sheaf.RingTheory.IndPrincipalZariski`
- `WeilConjectures.CategoryTheory.SiteCechComplex`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

Every original `proof_deps` edge absent from the new main proof is listed here. These
are moved to the auxiliary's finite Čech proof, and are not claimed mathematically pruned:

- `lem-cbc-comparison-pullback-sections`
- `def-weil-pbc-site-comparison-morphism`
- `lem-weil-pbc-etale-cohomology-limit-of-schemes`
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact`
- `def-weil-pbc-site-cech-complex`
- `lem-weil-pbc-ind-etale-stability`
- `def-weil-pbc-ind-etale-algebra`
- `lem-weil-pbc-filtered-category-directed-cofinal`
- `lem-kun-fibre-product-limits`
- `lem-weil-pbc-limit-affine-transition`
- `lem-weil-pbc-affine-etale-site-colimit`
- `def-weil-pbc-etale-site`
- `lem-weil-pbc-etale-composition-cancellation`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-etale-base-change-continuous`
- `lem-weil-pbc-injective-sheaf-cech-acyclic`
- `def-weil-pbc-sites-and-cohomology`
- `lem-weil-pbc-affine-scheme-qcqs`

The alternative Sheaf implementation of the general-site Čech criterion is replaced by
the proved upstream criterion. Source-import closure comparison removes the following
modules from this item's closure:

- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `Sheaf.CategoryTheory.EffaceableDeltaFunctorSuccessor`
- `Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal`
- `Sheaf.CategoryTheory.EffacingSequenceComparison`
- `Sheaf.CategoryTheory.EffacingSequencePushout`
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
- `Sheaf.CategoryTheory.SiteCechVanishingCriterion`
- `Sheaf.CategoryTheory.SiteCechVanishingStep`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.SiteSesCechH1Surjective`

All except the already withdrawn and empty `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`
remain reachable elsewhere from `TargetsCheck`. Only that empty module becomes globally
unreached. No live mathematical node is claimed globally prunable. The unit route remains
the affine-basis/finite-Čech route of Stacks 099U.

## Where the brief, the DAG or earlier work was wrong

The first worker's new additive equivalence was equivalent to the original vanishing
problem, because the étale cohomology of injective J already vanishes. It repackaged the
entire missing argument and was not a strict reduction. Its new node also depended on
the parent statement in `stmt_deps`, making the parent/auxiliary dependency circular,
and recorded no searches. These faults are repaired by replacing it with the finite Čech
condition, giving its independent statement dependencies and actual recorded searches.

The old search notes predated the upstream generic-site finite-cover criterion. That
proved theorem is now used directly. The previous report also called all geometric
imports pruned while its auxiliary still needed their arguments. The corrected report
and auxiliary retain those dependencies and distinguish moved imports from global pruning.

## New nodes

`lem-cbc-abelian-affine-comparison-vanishing-aux`: finite positive-degree Čech exactness
on affine ind-etale covers for the comparison pullback of injective étale coefficients.
It isolates only condition (3) of Tag 099U, with no derived cohomology conclusion. Empty
covers, repeated intersections and arbitrary abelian coefficients are included. Mathlib
searches used LeanFinder, Loogle, grep, and an attempted LeanSearch (service unavailable);
none supplies this specific comparison-pullback exactness. The node retains every geometric
and algebraic input used in its written proof.

Change record: `coord/changes/AffineComparisonInjectiveVanishing-imports.md`.

## Second reading by V3

1. **Existing interfaces — pass after repair.** Diffed both delivered modules against the
   repository. The auxiliary is new. The existing public theorem's signature is byte for
   byte identical; its visibility and docstring are unchanged. No target statement or
   public definition changes. Public-import removal is covered by the change record.
2. **Proof and trust — pass.** Both files compile locally through `lcompile.py`. The only
   remaining textual sorry is the named auxiliary theorem. Scratch `#print axioms` checks
   verify that both private geometric helpers use only `propext`, `Classical.choice`, and
   `Quot.sound`; the public theorem additionally uses `sorryAx` through its auxiliary.
   The auxiliary's only extra axiom is `sorryAx`. No forbidden declarations or data
   chosen from an unproved existence theorem occur. The original direct importer is
   checked unchanged against the delivered overlay.
3. **Split statement — repaired.** Rejected and removed the cohomology equivalence that
   restated the item. The replacement is precisely finite Čech exactness, an intermediate
   condition strictly below derived cohomology vanishing. Checked n=0, q=0 (degree one),
   empty schemes, repeated indices, and arbitrary abelian coefficients against Stacks
   099U. Its source, complete written proof, independent node and recorded searches are
   present. The full Čech limit argument is substantial and remains the one named hole.
4. **Shortest route and pruning — pass after repair.** Used the proved upstream criterion
   found by searching generic Čech terminology. Proved cofinality and intersection closure
   rather than moving them into a new sorry. All old proof edges removed from the main
   node are enumerated above. Removed the empty withdrawn module. Read
   `dag/units/sk-prop-sf-comparison.json` (its realized statement/steps are empty); this
   supporting lemma is not the unit's key statement, and preserves its 099U comparison
   route. No unit/chapter edits or bypasses were made.
5. **DAG agreement — repaired.** The main proof records basis geometry, the upstream
   version of the general-site criterion, and the new Čech input. The new node records
   only that input, with all dependencies used by its written proof, a verbatim Lean
   statement, source, creation record, blueprint origin, searches, chapter and unit.
   Removed the circular parent statement dependency. Checked that no new node duplicates
   an existing finite-comparison statement in the DAG or library.

Second reading changed the auxiliary statement and proof route, supplied the two real
geometric proofs, repaired the nodes/searches/dependency cycle, restored the auxiliary's
proof imports, removed unused/withdrawn imports and linter suppressions, and corrected the
progress and pruning report.
