## What changed

The original theorem `CategoryTheory.AdicSites.PerfectQuotientExchange.perfectQuotientExchangeNormalization` is proved from the quotient-diagram normalization, the strict perfect projection, and the completion-unit equation, retained as a separate normalization result. Its signature is unchanged. The proof factors `strictExchange` through the prescribed `towerProjection`, reflects invertibility through exact conservative scalar restriction, and cancels the presentation comparisons in `completionExchange`. The extracted interface block and the parent theorem signature were checked against the current repository text; both are identical (apart from the interface blueprint docstring tags).

The original declarations from `Modules` through `completionExchange` move verbatim to `Sheaf.Paper.PerfectQuotientExchangePresentation`, which the item publicly imports. Only blueprint docstring tags change in the moved block. This allows the independent diagram-construction theorem to use `Presentation` without a circular import. The change record is `coord/changes/B7-perfect-quotient-exchange-interface.md`. No existing consumer requires adaptation; the current downstream search reports the unclaimed `CompactSupportScalarProjectionIdentification`, which only imports this item and uses none of its declarations directly, and the item and all of its declarations remain available to unfinished DAG parents.

`perfectStrictReductionProjection` proves the cohomological assembly from single-level invertibility: exact evaluation commutes with derived homology, strict tower homology maps are invertible componentwise, and the derived homology criterion reflects the isomorphism. It never treats derived evaluation as faithful on morphisms.

`strictReductionProjectionCompletionUnit` isolates the augmentation/mate/limit
normalization, without perfectness or completeness. This separate result remains
unproved in this packet. The scratch proof constructs the quotient augmentation as the
adjunction transpose of the fixed completion unit and reaches the full representative
square; it has not yielded a complete checked proof. The packet retains its precise
canonical equation and the complete source argument as a named public theorem.
No existing dependency module is edited.

## Proved and sorry left

The original module had one hole, in `CategoryTheory.AdicSites.PerfectQuotientExchange.perfectQuotientExchangeNormalization`; that body is now complete. This is a decomposition, not a net proof of the original import closure: three strictly smaller public statements remain as new holes.

Proved new theorem: `CategoryTheory.AdicSites.perfectStrictReductionProjection`. The presentation module has zero holes. The item module has zero holes.

Holes added and left:

- `CategoryTheory.AdicSites.strictReductionProjectionCompletionUnit`, in `Sheaf.Paper.StrictReductionProjectionCompletionUnit`, node `lem-pur-strict-reduction-projection-completion-unit`. It is only the completion-unit equation for the fixed strict projection and has no Noetherian, perfectness, or presentation-existence hypothesis.

- `CategoryTheory.AdicSites.PerfectQuotientExchange.quotientExchangeDiagramNormalization`, in `Sheaf.Paper.QuotientExchangeDiagramNormalization`, node `lem-pur-quotient-exchange-diagram-normalization`. It constructs the normalized presentation and proves the scalar and evaluation mate equations, without any perfectness, invertibility or completion-unit assertion.
- `CategoryTheory.AdicSites.perfectReductionProjectionEvaluation`, in `Sheaf.Paper.PerfectReductionProjectionEvaluation`, node `lem-pur-perfect-reduction-projection-evaluation`. It proves invertibility at one perfect quotient level; it assumes no Noetherian hypothesis and no perfectness at any other level.

Each remaining hole has a complete proof in words, a source and its own DAG node. None repeats the original assertion or repackages its hypotheses. Zero ring, unit ideal, zero ideal, empty sites and unbounded inputs are addressed in the arguments; no uniform bound or flat quotient is imposed.

## No longer needed

The item removes these old private imports: `Sheaf.CategoryTheory.DiagramRingRestrictionPushforward`, `Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit`, `Sheaf.Paper.RingedSitePerfectProjectionFormula`, `Sheaf.SixFunctors.GeometricInverseImageConstantModule`, `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`, `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`, `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, `Mathlib.RingTheory.Finiteness.Defs`, `Mathlib.Algebra.Module.Projective`, and `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.

The perfect-coefficient and diagram arguments still need the mathematical dependencies represented by these imports; they now belong to the corresponding separate result, rather than to the proved parent assembly. No existing node or module is claimed globally prunable, and no module is withdrawn. The original public imports are retained by the publicly re-exported presentation interface. The planned unit proof uses the generic Mathlib unit-mate and iterated-mate/conjugate identities and the normalized augmentation square, in place of an application of the general ringed tensor projection theorem. The canonical maps remain the same.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies provide general ringed-diagram and tensor presentations, whereas the item uses its fixed `AdicSites` scalar-quotient presentation. Their interfaces require substantial ordinary section and full cochain comparisons; no existing theorem directly supplies the entire normalized `Presentation` record or the evaluated strict scalar-quotient projection. Those comparisons and the independent augmentation/unit normalization remain. The parent assembly, conservative-restriction argument and cohomology detection are formalized here.

`completedProjectionCoherence` initially looks like a shortcut but its DAG depends on this item, so it is not used. No source declaration, target, mathematical hypothesis, or approval list is changed.

## New nodes

`def-pur-perfect-quotient-exchange-presentation` owns the unchanged extracted public interface; the old node's declaration list now owns just its theorem. The mathematical definitions and public names are identical.

`lem-pur-quotient-exchange-diagram-normalization` carries original proof steps 1--3, including construction and all transition normalizations, independently of perfectness and the completion unit.

`lem-pur-perfect-reduction-projection-evaluation` carries the finite-projective realization and projection-formula argument for one level of original steps 4--5.

`lem-pur-perfect-strict-reduction-projection` records the proved assembly of single-level isomorphisms through cohomology of the strict tower.

`lem-pur-strict-reduction-projection-completion-unit` records the augmentation/mate/limit calculation of original steps 6--7. Its statement holds without Noetherian, perfectness or completeness assumptions.

Blueprint-wide searches `quotient exchange`, `perfect projection` and `completion unit` find related scheme, pro-etale and coefficient-compatibility statements, but no duplicate of these arbitrary small-site canonical comparison subarguments. The nearest imported ancestor is `thm-pur-rational-and-qbar-purity`; the new nodes serve its coefficient-independence clause through the existing strict exchange auxiliary.

The existing parent node's proof, proof dependencies and proof origin follow the completed Lean assembly. Its statement and statement dependencies are unchanged. Change record: `coord/changes/B7-perfect-quotient-exchange-interface.md`.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
