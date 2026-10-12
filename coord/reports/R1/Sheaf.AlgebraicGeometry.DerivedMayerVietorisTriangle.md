## What changed

Completed and verified the earlier sandbox reduction of
`schemeDerived_mayerVietoris_triangle`. Its signature is unchanged. The proof constructs
a functorial K-injective resolution and the derived adjunctions, applies the short exact
complex presentation, transports Mathlib's distinguished triangle, and proves
quasi-coherence of all three direct-image terms. Both sandbox modules compile.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.schemeDerived_mayerVietoris_triangle`
(node `lem-pc-derived-mayer-vietoris-triangle`). Added one hole:
`AlgebraicGeometry.schemeKInjective_mayerVietoris_presentation`
(node `lem-pc-kinjective-mayer-vietoris-presentation`). This is a decomposition:
one hole closed, one added, net zero. The new statement supplies a short exact complex
and the two arrow comparisons; the original module proves the connecting-morphism,
distinguishedness, derived-adjunction existence, and quasi-coherence steps.
There are no remaining holes in the original module and no holes in definitions.

## No longer needed

Removed direct imports from the original module:
`Sheaf.Algebra.Homology.KInjectiveRestrictOpen`,
`Sheaf.AlgebraicGeometry.DerivedCategory`,
`Sheaf.AlgebraicGeometry.InjectiveRestrictionSurjective`,
`Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, and
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`.
The first and third remain dependencies of the presentation module; the second and
fourth are already available through the public statement imports. Thus they are
not claimed as pruned modules. The proof uses the existing source-library
K-injective resolution construction instead of
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`; that module is not needed by
this route. No mathematical node is claimed to be globally unreachable.

Removed from the original node's direct `proof_deps`:
`lem-sc-derived-k-injective-restrict-open`,
`lem-sc-ringed-space-injective-restriction-surjective`, and
`def-pc-derived-direct-image`. All three remain used through the presentation node;
this is dependency relocation, not global pruning.

## Where the brief, the DAG or earlier work was wrong

The plan did not supply a Lean declaration constructing the short exact direct-image
complex with comparisons for the supplied derived adjunctions. That strictly smaller
step is the new node. Mathlib's `DerivedCategory.triangleOfSES_distinguished` supplies
the next step exactly. The earlier report incorrectly said that no imports were
removed and included a second-reading section; both have been corrected. LeanSearch
is unavailable (Internal Server Error), recorded explicitly in the new node.

## New nodes

`lem-pc-kinjective-mayer-vietoris-presentation` in
`dag/nodes/sec-picard-framework/lem-pc-kinjective-mayer-vietoris-presentation.json`,
stated in `Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation`. It follows
Stacks Tag 08BV before the passage from the short exact complex to a triangle.
It assumes a K-injective representative with injective terms and asserts neither a
connecting morphism nor distinguishedness nor quasi-coherence. Empty or repeated
opens satisfy the same sectionwise gluing and restriction argument. No change
records or statement changes are needed.

## Second reading by R1

1. Compared both delivered modules with the repository (the presentation module is
   new). Restored the existing theorem signature's original line wrapping; its
   signature is now byte-for-byte identical. No existing definitions or public
   imports changed, and no statement-change records are needed.
2. Compiled both modules locally in import order, without errors. Inspected every
   declaration: the sole new sorry is the named presentation theorem, with a
   full source/proof docstring and node; there are no definitions containing sorry
   or forbidden declarations. Explicit scratch `#print axioms` checks for both
   public theorems returned only propext, Classical.choice, Quot.sound and the
   expected sorryAx from open dependencies; the delivery probe also passed.
3. Read the presentation against Stacks Tag 08BV
   (https://stacks.math.columbia.edu/tag/08BV). The sectionwise sequence gives
   injectivity, the middle equalizer and surjectivity by injective restriction;
   empty opens give the identity/zero sequence, repeated opens give diagonal and
   difference, and zero complexes give zero throughout. Arbitrary adjunctions
   are accommodated by their right-adjoint automorphisms; transposing counits
   conjugates the overlap arrows by the same automorphisms. This is a proper
   complex-level subproblem, not a renamed triangle assertion: it leaves no
   boundary, distinguishedness, adjunction existence or QCoh assertion open in
   the main proof. Independent LeanFinder and Loogle queries (injective sections
   and ShortComplex/cochain exactness), plus local searches, found no existing
   direct-image presentation. The existing ringed-space triangle is for extension
   by zero, and ModuleMayerVietoris is a section-cohomology sequence; neither
   supplies this theorem. Closing the presentation requires substantial chain-map
   and derived comparison work, not a short application of an existing result.
4. Checked triangle transport, all three QCoh proofs, and imports. The proof uses
   Mathlib's actual SES boundary and distinguishedness theorem. Proof-only imports
   are plain imports. Expanded No longer needed to enumerate all three removed
   direct DAG dependencies and explicitly record their continued transitive use.
   The unit record's realized lists are empty; no registered unit realization is
   bypassed, and the planned injective/SES route is retained.
5. Checked both node records: proof_deps are the union of their proof-step uses;
   the main node describes the Lean proof and the new node has the required source,
   searches, provenance, blueprint, unit, chapter, status and verbatim Lean
   statement. No node-statement repair was needed.

Changed only signature whitespace and report completeness. The mathematical proof
and new presentation statement passed this reading without changes. This remains
a one-for-one decomposition, net zero holes, with no globally pruned module claimed.
