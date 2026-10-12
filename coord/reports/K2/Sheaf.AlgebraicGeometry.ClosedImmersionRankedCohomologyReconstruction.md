## What changed

Reduced `AlgebraicGeometry.closedImmersion_rankedCohomology_reconstruction` to two strictly separate steps of its existing plan, with its signature and existing docstring unchanged. Its Lean proof now establishes finite-limit preservation using the module pullback-pushforward adjunction, installs finite-colimit preservation, and uses the source library's proved exact-functor comparison to identify the derived direct image with the localized termwise direct image. It supplies the explicit exterior sheaves on the rank strata to the generic stratum-formality statement and composes the two isomorphisms.

Added two modules, each with one named theorem and matching node: `Sheaf.AlgebraicGeometry.ClosedImmersionAlgebraDirectImageExact` and `Sheaf.AlgebraicGeometry.ClopenRankStrataFormality`. The first asserts only finite-colimit preservation, for all module sheaves, with no complex, rank function, derived category or cohomology hypothesis. The second reconstructs the termwise direct-image complex of an arbitrary family of sheaves on the rank strata; it has no exterior-power calculation, no source derived category and no derived direct image. They are the exactness and rank-splitting parts of the argument, respectively, rather than restatements of the original theorem.

The main module privately imports both new modules, `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`, and `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`. No existing signature, definition, or public import changed. Updated the original node's proof, proof dependencies and proof origin to match the compiled proof.

Validation: all three modules compile together without warnings through `lcompile.py --all`. The assembly genuinely uses `rightDerivedFunctorIsoMapDerivedCategory.app`, `mapDerivedCategoryFactors.app`, the definition of each exterior term, and `Iso.trans`. The new statements were checked in words for empty source, rank zero, empty rank fibers, negative degrees and arbitrary non-quasi-coherent module sheaves. For an empty source every algebra-module sheaf vanishes; empty fibers give zero sheaves, and negative terms are explicitly zero. No clopen image in Y is assumed. No witness from an unproved existence theorem is used to define data.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.closedImmersion_rankedCohomology_reconstruction` by a compiling reduction. This is a decomposition, not a proof free of sorry dependencies: one upper hole closed, two lower holes added (net -1 before any closure/import effects).

The delivery leaves exactly these named sorries:

- `AlgebraicGeometry.closedImmersion_algebraDirectImage_preservesFiniteColimits`, node `lem-sc-closed-immersion-algebra-direct-image-exact`.
- `AlgebraicGeometry.clopenRankStrata_formality`, node `lem-sc-clopen-rank-strata-formality`.

The requested module itself has no sorry left. Both new holes have complete proofs in words, source citations, and matching DAG statements. No axiom or hollow definition was added.

## No longer needed

Removed the private import `Mathlib.Algebra.Homology.DerivedCategory.TStructure` from the requested module: its proof uses the exact-derived-functor comparison and generic stratum statement instead of directly invoking single-degree truncation. The latter truncation remains part of the lower stratum-formality proof, so its mathematical role is not pruned.

No Sheaf or WeilConjectures module and no existing DAG node is globally pruned. The original definition dependencies remain necessary to state the theorem or its new lower statements. No blueprint unit statement or realized proof step is bypassed. An exploratory standalone homology lemma was removed from the sandbox because the final proof does not need it.

## Where the brief, the DAG or earlier work was wrong

The plan's rank-idempotent splitting is not furnished by the listed definition declarations. It needs a lower theorem, now `lem-sc-clopen-rank-strata-formality`. Its arbitrary-family statement isolates the splitting and single-degree reconstruction from all exterior-power and derived-direct-image calculations.

The exactness step's left exactness is already available from the pullback adjunction. The missing part is finite-colimit preservation under the closed embedding. The source-library module `RightDerivedFunctor.MapDerivedCategory` already proves the required passage from exactness to termwise computation, so no new derived comparison hole is needed.

The parent cites [Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ) for the surrounding Koszul duality calculation and [Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW) for the algebra-valued derived image. These tags do not directly state generic finite-stratum formality; its written proof expands the parent node's indicated idempotent/truncation argument. For the exactness component, [Tag 00AE](https://stacks.math.columbia.edu/tag/00AE) describes the stalks of a closed-embedding direct image and [Tag 01AX](https://stacks.math.columbia.edu/tag/01AX) deduces exactness for abelian sheaves. The same stalk argument applies to the module direct image in the present identity-ring-map setup.

LeanSearch returned Internal Server Error; its real failed queries are recorded in searches.jsonl and the new nodes. LeanFinder, Loogle and Mathlib grep ran; repository grep finds a pro-etale clopen-idempotent construction, but its site and coefficient-category interface does not apply to the ringed-space module sheaves here. No statement was disputed or changed, and no forced adaptation was needed.

## New nodes

`lem-sc-closed-immersion-algebra-direct-image-exact`, module `Sheaf.AlgebraicGeometry.ClosedImmersionAlgebraDirectImageExact`: finite-colimit preservation for all module sheaves under the direct-image-algebra map of a closed immersion. The proof is the closed-embedding stalk calculation and stalkwise exactness, sourced to Tags 00AE and 01AX, with the ringed-space setup of Tag 0AVW. Searches found pushforward right-adjoint declarations, but no finite-colimit preservation theorem for this closed-embedding module functor.

`lem-sc-clopen-rank-strata-formality`, module `Sheaf.AlgebraicGeometry.ClopenRankStrataFormality`: reconstruction of a termwise pushed-forward zero-differential complex of arbitrary module sheaves on the finite clopen rank fibers. The proof expands the original node's steps 2--4 via characteristic idempotents and single-degree truncation. Searches found Mathlib's single-degree reconstruction theorem, but no finite-stratum module-sheaf assembly theorem. Both nodes retain the parent chapter and unit, and trace their blueprint ancestry through the original reconstruction node. No change record is necessary because no existing statement or definition changed.

## Second reading by K2

1. **Visible changes and signatures.** Compared the delivered target module with the repository version. The target theorem signature and existing declarations are byte-for-byte unchanged; only its proof and private imports changed. The two added modules contain the new declarations listed above, with matching DAG nodes.

2. **Compilation and proof hygiene.** Compiled all three modules together with `lcompile.py --all`; compilation succeeds without warnings. The target module has no `sorry`, and the only remaining sorries are the two named split theorems in the added modules. No axiom, unsafe, opaque, extern, implemented_by, or hollow definition was added.

3. **Statements and dependencies.** Read both split statements against their docstrings and DAG records. Finite-colimit preservation is the exact missing exactness component, and the clopen-strata theorem is a strictly more general formality component with no exterior-power or derived-direct-image assumptions. Their edge cases (empty source, empty strata, rank zero, negative degrees, and arbitrary module sheaves) are covered in the stated proof explanations. The target proof and each node's `proof`, `proof_deps`, and `proof_origin` match the Lean route.

4. **Shortest route and pruning.** The target uses the existing pullback-adjunction finite-limit instance and source-library exact-derived-functor comparison, then the two strictly separated lower statements. The unused `Mathlib.Algebra.Homology.DerivedCategory.TStructure` import was removed from the target and is recorded above; no other old dependency is bypassed.

5. **Unit route.** The finite-stratum splitting and exactness steps remain the realized route of `sk-thm-picard-duality`; the decomposition introduces only lower statements for those steps and does not alter the target or unit statement.

Changed after reading: no Lean proof or statement required repair. Added this second-reading record only; the implementation and DAG metadata already agreed with the compiled proof.
