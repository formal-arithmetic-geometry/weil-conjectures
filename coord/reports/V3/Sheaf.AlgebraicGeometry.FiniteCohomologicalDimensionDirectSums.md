## What changed

Proved `AlgebraicGeometry.Etale.derivedDirectImage_and_globalSections_preserveCoproducts`
with its statement, binders and universes unchanged. Only its proof and proof imports changed
in the Lean file; the original public imports remain. Updated the node's proof,
proof_deps and proof_origin to record the actual route.

The shorter route reuses the already proved source-library theorems
`AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedLowerStar` and
`AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedGlobalSections` from
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts`.
The proof extracts finite bounds using `sInf_lt_iff`, transfers them through the existing
coefficient-forgetting comparisons, and applies those theorems. The existing proved private
`CategoryTheory.preservesCoproducts_of_small` is accessed by `import all` from
`WeilConjectures.CategoryTheory.CompactTestsRightAdjointCoproducts`; no helper was duplicated
and no public API was changed. It uses only locally small endomorphisms and preservation
of zero morphisms, not compactness or the compact-test theorem of that module.

Search: launcher leanfinder and loogle queries returned no matches; launcher grep returned
no match. Direct rg over the source library found the coefficient-specific coproduct
theorems and the general universe-extension helper. Read their proofs and Stacks 0F11
in `literature/stacks-project/etale-cohomology.tex`.

Validation: remote lcompile compiled the complete proof, and compiled it again after pruning
proof imports (20.4 seconds). The finite-ring argument includes n=1 (the zero ring), the
bound d=0, and every existing coproduct including the empty family. The universe helper
shrinks nonzero support of an existing coproduct; it does not assert existence of coproducts
larger than the ambient universe.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.derivedDirectImage_and_globalSections_preserveCoproducts`
(node `lem-kun-0f11`). Added 0 holes. No sorry remains in the delivered Lean module.
No split-off theorem or new axiom was introduced. Existing imported theorem dependencies
are used under the stage-3 policy; this is not a claim that their transitive proofs are all closed.

## No longer needed

Removed these direct proof imports:

- `Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`
- `Mathlib.CategoryTheory.Abelian.RightDerived`
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `WeilConjectures.CategoryTheory.DerivedModuleDirectSums`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`

The following original proof dependencies are no longer needed as separate named statements
by this proof, because the source-library coproduct theorems already implement the abstract
acyclic-complex and filtered-colimit argument:

- `lemma-weil-pbc-direct-image-filtered-colimit`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `def-sp-left-exact-additive`
- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `lem-pur-kinjective-degreewise-existence`
- `lem-kun-grothendieck-derived-coproducts`
- `def-weil-pbc-direct-image`
- `lem-kun-finite-cd-acyclic-complex`
- `def-weil-pbc-global-sections-functor`
- `lem-weil-pbc-cohomology-filtered-colimit`
- `lem-pc-derived-module-direct-sums`

Some underlying constructions remain transitively used inside the source-library theorem;
this list records pruning of the explicit plan and direct imports, not a claim that every
associated source module is unreachable from all targets. In particular the unused Sheaf
acyclic-complex, Grothendieck coproduct and colimits-forgetting wrapper modules are not imported.
No unit statement or realized proof step was bypassed: the unit's realized lists are empty.

## Where the brief, the DAG or earlier work was wrong

The existing module's plan did not mention that the source library now proves both
coefficient-specific versions of this very result. Reusing them leaves only finite-bound
conversion and universe extension to prove. Its numerical torsion dimension differs from
the source hypothesis, so a direct exact application without these conversions would fail.
The source coproduct results accept indices in Type (u+1); the original statement allows
Type w, requiring the nonzero-support argument. The private helper is already proved in the
source library, so importing all that module avoids rewriting it or changing another module.
No false statement or definition repair was necessary. No new nodes or change records.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
