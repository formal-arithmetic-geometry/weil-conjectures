## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.sfbAdicImmersion_completedTransport` without changing its signature. The candidate is explicitly `sfbImmersionCompletedModel i I K`: apply the existing completed inverse image to `SfbCompletionNormalization.object X I K`. The algebraic lift is characterized by its generalized-section operations and constant comparisons; no local or perfect model is chosen from an existence theorem.

The already proved `SfbCompletionNormalization.complete_iff` supplies completeness of the normalized input. A finite generating family of the Noetherian ideal allows the completeness clause of `SfbAdicRestriction.adicStratumCompletionUnit` to supply completeness of the fixed candidate. The proof then maps the given residue isomorphism through the exact functor `sfbFixedResiduePull`, composes it with the two residue comparisons, and specializes the uniform slice comparison to K. The same slice equivalence compares every ordinary coefficient complex P.

Added three modules: `AdicImmersionCompletedModel` (two explicit definitions), `AdicImmersionResidueComparison` (the exact fixed-scalar functor and its two comparison squares), and `AdicImmersionSliceComparison` (the slice equivalence and its two compatibility assertions). Added private proof imports to the item module. No existing definition, public signature, source-library declaration or consumer changed. The unit route is retained. The residue functor explicitly uses the existing smaller derived category of fixed-scalar sheaves as its source and the standard completed-coefficient localization as its target; instance selection is scoped to the new declarations and changes no exported attributes.

Remote validation: all four packet modules compiled cleanly in import order. Timings were 6.3 s (construction), 12.7 s (residue), 11.4 s (slices), and 17.1 s (item); each is below the 60-second limit. The original theorem signature was checked byte-for-byte, and the node statement attachments match the Lean declarations.

## Proved and sorry left

Closed the original body hole in `AlgebraicGeometry.Scheme.sfbAdicImmersion_completedTransport` (node `lem-sfb-adic-immersion-completed-transport`) by the displayed Lean assembly. There are zero `sorry` occurrences left in the item module.

Added two holes, both public named theorem bodies in their own modules:

- `AlgebraicGeometry.Scheme.sfbImmersion_residueComparisons`, node `lem-sfb-adic-immersion-residue-comparison`: finite-projection and etale/pro-etale comparison squares for the previously fixed completed pullback.
- `AlgebraicGeometry.Scheme.sfbImmersion_sliceComparisons`, node `lem-sfb-adic-immersion-slice-comparison`: the completed coefficient equivalence on slices and its two compatibility assertions for the same fixed pullback.

This is a decomposition of the original one hole into two strictly narrower functor-comparison steps, not a net proof or an axiom-free completion. Neither lower theorem assumes completeness or an isomorphism presenting a residue, nor concludes the parent's simultaneous existence result. The parent genuinely proves completeness from existing declarations and transports the supplied residue isomorphism by functoriality. All added definitions and the additive/finite-limit/finite-colimit instances are proved constructions with no holes. The existing normalization theorem is reused unchanged.

## No longer needed

No original public import was removed and no existing module or node was withdrawn. The original direct proof dependencies for comparison pullback, immersion limit preservation, constant-ring module equivalence and exact slice restriction are now used by the two narrower comparison steps. They remain needed below those steps; this delivery claims no global pruning. The duplicate normalization construction explored in the sandbox was removed before delivery in favor of the already proved `Sheaf.Paper.SfbCompletionNormalization`.

## Where the brief, the DAG or earlier work was wrong

The original DAG describes a genuine normalization and compatibility argument but did not expose all its interface conversions as directly applicable theorems. In particular its residue and slice comparisons require agreement between actual ringed pro-etale inverse image and the normalized small-site algebraic inverse image, including derived localization representatives. These are the two named remaining steps. The existing normalization module already proves the coefficient and completeness part, so introducing another normalization theorem would duplicate work.

No statement is disputed or weakened. The new comparison assertions use arbitrary commutative Noetherian coefficients and arbitrary complexes, with no field, boundedness or perfectness assumptions. Their natural-language proofs compare the actual coefficient projections and tensor insertions, rather than selecting an arbitrary residue or perfect witness. Edge cases checked in formulating them: empty schemes/slices, zero coefficient rings, I=0 and I=A, and arbitrary unbounded P. These cases use the same exact functor and scalar-extension comparisons.

## New nodes

`def-sfb-adic-immersion-completed-model` records the explicit candidate construction from the existing algebraic inverse-image lift, `SfbCompletionNormalization.object`, and `completedPull`. It leaves no hole. Source: the normalization and inverse-image constructions in Stacks Tags 03A0, 03CY, 099L, and Bhatt--Scholze Lemma 6.5.8.

`lem-sfb-adic-immersion-residue-comparison` isolates the finite-projection and comparison-pullback squares, independent of completeness and of a chosen residue presentation. Its proof first uses `finiteComparison` and the existing normalization projection identities; it then uses the etale/pro-etale pullback square and exact coefficient equivalences. Source: Stacks Tags 03A0, 03CY, 06YY, 099L and 099R, and Bhatt--Scholze Lemma 6.5.8.

`lem-sfb-adic-immersion-slice-comparison` isolates the slice coefficient equivalence, uniformly in K and every P. Its proof uses the AsSmall slice equivalence, immersion limit preservation, canonical finite projections and exact derived localization comparisons. Source: Stacks Tags 03A0, 03CY, 03DJ, 099L and 099R; Bhatt--Scholze Lemma 6.5.8 and Remark 6.5.10. All three nodes belong to the same chapter and unit as the item; no change records are necessary because existing interfaces are unchanged.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
