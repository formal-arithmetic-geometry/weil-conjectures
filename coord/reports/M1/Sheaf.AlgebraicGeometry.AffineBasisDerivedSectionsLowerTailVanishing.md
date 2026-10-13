## What changed

Replaced the target theorem's proof with a complete Milnor-tower calculation. The proof constructs the lower truncation tower, uses eventual isomorphisms in degree `i - 1`, proves the degree-`i` inverse limit is zero, and reflects the resulting abelian-group vanishing back to modules. Added two strictly smaller intermediate statements, each in its own module, for the affine-basis reconstruction and truncation-transition steps.

## Proved and sorry left

Closed the original named hole `AlgebraicGeometry.affineBasisDerivedSections_lowerTail_isZero` by a Milnor calculation conditional on the two new intermediate theorems. One original hole closed, two holes added: this is a decomposition, not an axiom-free proof or a net reduction of holes (local net -1). No further hole was closed by the second reader. The target still depends on `sorryAx`.

Sorries remain in the strictly smaller declarations:

- `AlgebraicGeometry.affineBasisLowerTail_sections_reconstruction` in node `lem-sc-affine-basis-lower-tail-sections-reconstruction`.
- `AlgebraicGeometry.affineBasisLowerTail_sections_step_isIso` in node `lem-sc-affine-basis-lower-tail-sections-step`.

## No longer needed

No original Lean import was removed: the repository version imports only statement and instance dependencies. The following old direct proof dependencies have moved to the reconstruction/transition subclaims and remain needed, with proof-only imports there:

- `lem-sc-derived-k-injective-restrict-open` / `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`.
- `lem-sc-module-cohomology-source-comparison` / `Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison`.
- `lem-pc-ringed-space-truncation-derived-limit` / `Sheaf.AlgebraicGeometry.TruncationDerivedLimit`.
- `lem-pc-derived-functor-commutes-derived-limit` / `Sheaf.CategoryTheory.Triangulated.DerivedFunctorDerivedLimit`.

`thm-sp-truncation-e2` / `Sheaf.CategoryTheory.TruncationHypercohomology` is no longer needed by this argument: successive step triangles and integer induction replace the bounded-below spectral-sequence calculation. It was not an actual import of the repository module, and no claim is made that it leaves the full targets' import closure.

Removed three unused imports from the new transition module: `Sheaf.CategoryTheory.Triangulated.DerivedLimit`, `Mathlib.Algebra.Category.Grp.AB`, and `WeilConjectures.Algebra.Homology.HomotopyCategory.Products`. The reconstruction module retains them for its triangle and product statement. Whole modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped before writing the planned Milnor calculation. The unbounded comparison is expressible as two proper intermediate theorems and a real tower argument, so it was not a reason to abandon the item.

## New nodes

`lem-sc-affine-basis-lower-tail-sections-reconstruction` and `lem-sc-affine-basis-lower-tail-sections-step` are new stage-3 nodes corresponding to the two missing pieces of the stated affine-basis argument.

## Earlier second reading (a previous round; superseded)

The main theorem compiles against the two new intermediate declarations. The new statements are strict subclaims: one gives only the derived-limit reconstruction triangle and the other only eventual transition isomorphisms. The unit route remains represented by the original theorem and its affine-basis dependencies.

## Second reading by M1

1. Compared the existing module with the repository using `diff -u`; only proof imports and the body after `:= by` changed. The theorem signature is byte for byte identical, including universes, hypotheses and conclusion. There are no definitions, forced adaptations or changes to any existing statement. Verdict: pass.
2. All three delivered modules compile individually in dependency order through `lcompile.py --all`, without errors or warnings. Scanned the delivered source: precisely the two named whole-theorem `sorry` proofs listed above remain; no forbidden declaration or hollow definition occurs. Scratch copies with `#print axioms` check all three declarations; the only permitted additional dependency is `sorryAx` for the still-open intermediate statements. The existential connecting map is eliminated locally in a proof; no arbitrary data witness is installed as a definition. Verdict: pass, conditional decomposition.
3. Read both intermediate statements, their docstrings and their nodes. Reconstruction is only a specified Roos triangle, with canonical first and middle maps; stabilization is only a one-step homology isomorphism. Neither restates the original vanishing theorem. Checked the zero complex, empty affine V, arbitrary signed a and n, and the equality boundary n=1-i: the two endpoint indices are then 1 and 2. Homology at -n>=a is zero, while below a source comparison applies. For reconstruction, use the open subscheme V, its affine basis, and local bound zero; no global acyclicity outside V is assumed. Independently searched Lean Finder, Loogle, Mathlib grep and both library roots using reconstruction/transition terminology. Existing QCohTruncationDerivedLimit and DerivedFunctorTruncationStabilization require quasi-coherence, absent here. No direct replacement found. Neither remaining hole closes in a short application: the restriction/cohomology comparisons still need formal transport. Verdict: pass.
4. Read the main calculation from its conclusion downward. The faithful forgetful comparison reduces to the Milnor middle term; integer induction starts at the zero truncation at a and propagates through the one-step isomorphisms. A cofinal eventually zero degree-i tower has zero inverse limit; the degree-(i-1) tower is eventually isomorphic with the stated natural threshold. This is a real reduction, not a restatement. Removed unused transition imports and enumerated every old dependency absent from the new direct proof_deps above. The unit sk-thm-picard-duality has empty realized statement/step arrays in the repository; this below-unit item changes none of its route or unit records. Verdict: pass.
5. Checked the existing node against the main proof and both new nodes against their Lean signatures. Repaired omitted dependency edges in the new nodes, made the transition node's prose statement self-contained, corrected its source to perfect.tex Tag 08D4, and recorded independent searches. The old spectral-sequence step is replaced by the lower-truncation step triangle. Verdict: pass after repair.

Second reading changed dependency metadata, search records, the new transition node's prose/source, unused transition imports, and the report's decomposition/pruning accounting. The existing theorem proof and all delivered Lean theorem signatures are unchanged by the second reader.

Sources checked directly because the Stacks source checkout is absent on this machine: [Tag 0BKT](https://stacks.math.columbia.edu/tag/0BKT), [Tag 0D64](https://stacks.math.columbia.edu/tag/0D64), [Tag 071B](https://stacks.math.columbia.edu/tag/071B), and the successive-truncation triangle argument in [Tag 08D4](https://stacks.math.columbia.edu/tag/08D4).
