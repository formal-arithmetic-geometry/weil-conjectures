## What changed

Proved `AlgebraicGeometry.ProEtale.det_brown_hypotheses_ambient` in
`Sheaf.SixFunctors.BrownHypothesesAmbient`, preserving its complete signature and
all public imports. No definitions or other modules were changed.
The two proof-scope opens are documented in
`coord/changes/z8-brown-ambient-proof-scopes.md`; the direct and indirect consumers
were inspected and require no adaptations.

The shorter route applies the existing internal-module Grothendieck theorem
`CategoryTheory.Mod.isGrothendieckAbelian` directly to the actual pulled-back
coefficient ring. The existing `DerivedCategory.locallySmall` and
`CategoryTheory.derived_hasCoproducts` supply the ambient properties. The proof
then establishes repleteness, zero, shifts, distinguished-triangle extension
closure, and coproduct closure by checking membership in every candidate in the
defining intersection. Mathlib creates coproducts in the full subcategory;
`CategoryTheory.isIdempotentComplete_of_countableCoproducts` splits its idempotents.

The original closure quantifies over index types in the ambient object universe
`u + 2`. The proof first checks closure at exactly that size, then transports it
along `Discrete.equivalence Equiv.ulift` to index types in `u + 1`. It only requires
ambient coproduct existence in `u + 1`. Empty families are included throughout.
Zero coefficients, the empty scheme, and zero/identity idempotents require no
additional assumptions or case exclusions.

Updated `det-brown-hypotheses-ambient`'s proof, proof dependencies, and proof origin
to the compiling route; removed obsolete tool approvals without adding or
reordering approvals. Existing proved tools used by the shorter route are
`lem-sfb-modobj-grothendieck`, `lem-pc-derived-category-locally-small`, and
`lem-grothendieck-derived-has-coproducts`. Their declarations replace the longer
sectionwise reconstruction and explicit K-injective Hom calculations. The
pro-etale sheaf Grothendieck and closed tensor instances already belong to the
publicly imported ambient framework. The unit's ambient Grothendieck-derived,
localizing intersection, and countable-coproduct splitting route is retained.

Validation: compiled the completed proof and then the pruned final import set
through `lcompile.py`, without compiler warnings. All Lean lines are at most
100 characters. The first dry run also compiled and ran the axiom probe successfully; its only
rejection requested the change record for those opens, now supplied. The next dry
run checks the completed delivery.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.det_brown_hypotheses_ambient`
(node `det-brown-hypotheses-ambient`).

Holes closed: 1. Holes added: 0. Holes left in delivered Lean: 0.
No split-offs, axioms, new definitions, or statement changes.
Existing imported declarations retain their independent proof obligations.

## No longer needed

Removed these proof imports:

- `Sheaf.CategoryTheory.SheafTensor`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`

Added direct proof imports for Mathlib full-subcategory colimits, the internal-module
Grothendieck theorem, derived local smallness, and derived coproduct existence.
Retained the countable-coproduct idempotent-completeness theorem.

The sectionwise reconstruction dependencies are unnecessary:
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`
(`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`) and
`lem-weil-pbc-ring-sheaves-grothendieck`
(`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`).
`sk-def-sfb-sheaf-tensor` (`Sheaf.CategoryTheory.SheafTensor`) is replaced by the
already available tensor instances for the actual ambient sheaf category.
`lem-kun-grothendieck-derived-coproducts`
(`Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`) is replaced by the
proved derived coproduct-existence theorem, which already chooses representatives.

Removed direct DAG proof edges to `lem-weil-pbc-kinjective-hom-derived`,
`def-weil-pbc-proetale-site`, and `def-weil-size-convention`: the existing local
smallness, pro-etale sheaf, and tensor interfaces already encapsulate these
calculations/conventions. The size convention remains a statement dependency;
K-injective comparison remains behind the existing derived theorems. Removed
obsolete direct tool approvals for `lem-weil-pbc-ring-sheaves-grothendieck`,
`lem-weil-pbc-kinjective-hom-derived`, and
`lem-kun-grothendieck-derived-coproducts`. These are local route removals, not a
claim that no other project item imports the corresponding modules.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The original node and
existing theorem docstring describe a longer sectionwise-module proof plan.
The source library already proves the internal-module Grothendieck theorem and
packages derived local smallness and coproduct existence, so the actual proof
and updated DAG use those directly. No additional intermediate theorem is needed.
The theorem's coefficient restrictions remain exactly as stated, although its
structural proof does not need to case-split on them.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
