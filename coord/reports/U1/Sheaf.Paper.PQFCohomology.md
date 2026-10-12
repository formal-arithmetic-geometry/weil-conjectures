## What changed

Proved `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` in
`Sheaf.Paper.PQFCohomology`, preserving its complete signature and original docstring.
Global sections is module-sheaf evaluation, whose finite-limit preservation is already
in Mathlib. Apply the stated universal right-derived delta-functor theorem, retaining
its degree-functor equality. For higher direct images, whisker the inverse of the
source library's bounded-below/unbounded comparison and compose with its natural
single-object/classical-derived-functor comparison. This proves a functor isomorphism,
including naturality, rather than merely objectwise isomorphisms.

Added proof-only imports `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.
Updated the existing node's proof, proof dependencies, and proof origin to match.
The unit record `sk-prop-av-pqf-finite` has no realized nodes for its statement or step;
this proof changes no unit-level geometric route.

Searches: LeanFinder searched for homology of an unbounded right derived functor on
a single object and returned general homology/localization and injective-resolution
lemmas. Loogle `Functor.rightDerived` returned an unknown-identifier response.
The logged grep found Mathlib `evaluationPreservesFiniteLimits`; local repository
search found the exact source-library compatibility and natural single comparison.
Their signatures were read before use. The import-cycle check permits the new source
import. Local compilation checks the full theorem, all instance and universe arguments,
and its original statement, without errors or warnings.

## Proved and sorry left

Proved the sole original sorry:
`AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`
(node `pqf-def-cohomology`). No sorry remains in the delivered module and no new
sorry or declaration is added. The proof intentionally uses the existing
`CategoryTheory.Functor.exists_universal_rightDerived_deltaFunctor`
(node `lem-weil-pbc-right-derived-universal-delta-functor`), which still has sorry
in its own module. Existing direct-image additivity and Grothendieck-category
instances also remain dependencies; this delivery does not claim to close them.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact`
and its direct proof dependency `lem-sc-global-sections-left-exact`. Its statement
uses scheme modules valued in abelian groups, whereas this proof needs ringed-space
module evaluation valued in modules over the global ring; Mathlib proves the needed
finite-limit preservation directly.

Removed the redundant explicit import `Sheaf.Topology.RingedSpaceModuleEnoughInjectives`.
Its module remains a public dependency of `RingedSpaceModuleCohomology`, so this is
import redundancy removal, not removal of that module from the targets' closure.
The direct proof dependency `lem-sc-ringed-space-module-sheaves-enough-injectives`
is replaced by the shared Grothendieck instance from
`def-pc-ringed-spaces-derived-direct-image`. The cohomology definition still mentions
its enough-injectives theorem; that underlying statement dependency is preserved.

Removed the direct proof dependency
`lem-weil-pbc-bounded-below-injectives-kinjective`: the existing proved
`src-right-derived-functor-plus-compatibility` handles this step internally using
Mathlib's K-injective theorem. The mathematical fact is still used transitively.
No public import was removed and no existing module or node was deleted.

The existing `moduleCohomology_iso_resolution`, `moduleCohomology_independent`,
`derivedModuleDirectImageFactorization`, and
`derivedModuleDirectImage_computed_by_resolution` are not used by this proof.
Their containing modules remain needed for the statement's definitions.

## Where the brief, the DAG or earlier work was wrong

The planned global-sections lemma is about a different codomain and module model;
using Mathlib evaluation avoids that unnecessary comparison. The planned manual
resolution comparison is already provided naturally by the source library. No
statement is disputed or changed, and no new definition or hypothesis is introduced.
The original declaration docstring describes the longer plan; the updated node
records the actual Lean route.

## Second reading by U1

1. I compared the delivered module with the repository version. The theorem signature
and all existing declaration statements are unchanged byte for byte; only the proof
and proof-only imports changed.

2. The sandbox module compiles cleanly with `lcompile.py`. It contains no `sorry`,
`axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. The
remaining open proofs are only in imported declarations, as recorded by their nodes.

3. No statement was split off. The existing theorem is the exact target statement,
and the updated node's proof dependencies and proof origin name the route used by the
proof. The two added imports are proof-only; the removed imports are not needed.

4. The route is below the unit level and does not alter any unit statement or step.
The unit currently has no realized statement or step nodes, so its record is left
unchanged.

5. The proof matches the statement: module-sheaf evaluation preserves finite limits,
which supplies the universal delta-functor, and the natural right-derived
plus-compatibility comparison supplies the displayed higher-direct-image isomorphism.
No hypothesis was added and no conclusion weakened.

I changed only proof imports, the existing node's proof metadata, and this report; no
definitions, theorem statements, or target files were changed.
