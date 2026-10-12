## What changed
Proved `AlgebraicGeometry.Scheme.Modules.exists_openCover_split_shortExact` in
`Sheaf.AlgebraicGeometry.Modules.LocalSplittingFiniteFree`, with the existing
signature and visibility unchanged. The private, fully proved helper
`exists_section_spec` constructs a right inverse on an affine spectrum from
projectivity of quotient sections and affine global-section lifting. The main
proof restricts to each affine open, obtains the section, constructs the splitting,
transports it back across the affine scheme isomorphism, and verifies both required
identities by biproduct extensionality.

Replaced the proof import of `Sheaf.AlgebraicGeometry.LocalSectionQuotientFiniteFree`
with proof imports of `Sheaf.AlgebraicGeometry.Modules.AffineExtensionSectionSurjectivity`,
`WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank`, and
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`. These respectively
provide affine lifting, quotient projectivity, and exact restriction. All existing
public imports and copyright are preserved. The second reader updated the theorem
docstring to describe the affine proof actually used; the inline proof comment and
updated DAG explain the unused false-orientation dependency.
Updated only `proof`, `proof_deps`, and `proof_origin` of
`lem-sc-local-splitting-finite-free`. No statement, definition, or other module changed.

## Proved and sorry left
Holes closed: 1, `AlgebraicGeometry.Scheme.Modules.exists_openCover_split_shortExact`
(node `lem-sc-local-splitting-finite-free`). Holes added: 0. No sorry remains in the
item, and no intermediate statement is postponed. This is a proof, not a decomposition.

The final proof compiles without errors or warnings through lcompile.py.
An explicit `#print axioms` check gives exactly `propext`, `Classical.choice`, and
`Quot.sound`, with no sorry axiom, including transitive dependencies. The private
helper is also checked by the delivery probe. The affine cover has index type
`Type u`; empty schemes, zero rings, and rank-zero quotients are included. The
middle-term counit is not assumed invertible. No arbitrary data definition was added.

## No longer needed
Removed proof import and node dependency:
`Sheaf.AlgebraicGeometry.LocalSectionQuotientFiniteFree`,
`lem-sc-local-section-quotient-finite-free`. Comparing TargetsCheck's import closure
before and after replacing this item shows that this is the only project module
that leaves the targets' closure. Its descendants stay reached through other
routes; no claim is made that those modules globally disappear.

The local-section node's dependency
`Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting`
(`lem-weil-pbc-ringed-space-module-exactness-local-lifting`) is not needed along
this item's route; it remains needed elsewhere. No new OpenCoverSplitting module
or equivalent restatement is used. Direct imports of ModuleCat.Projective and
Flat.EquationalCriterion were tested and removed because the three retained proof
imports already provide the required results. The unit's determinant/local-splitting
route is preserved: affine local sections, exactness, the biproduct construction,
and an open cover are all implemented, not bypassed.

## Where the brief, the DAG or earlier work was wrong
STATEMENT-DISPUTED: the unused
`AlgebraicGeometry.exists_local_section_of_shortExact_finiteLocallyFree`
asks for `map S.g ≫ s = id` on the middle term, rather than the required
`s ≫ map S.g = id` on the quotient. Over Spec(k), the split sequence
0 → k → k² → k → 0 has projection q onto the second coordinate. Every proposed
s satisfies s(q(1,0))=0, so q;s cannot be the identity on k². The informal node
states the correct orientation. This delivery does not edit that module and
never invokes its false declaration.

The earlier attempt's split-off theorem merely restated the target and was correctly
rejected. This repair adds no holes and proves the entire theorem, including local
right inverses, using already proved affine results. Search through msearch.py used
LeanFinder (generating-section results, no direct splitting theorem), Loogle
(unknown queried identifier), LeanSearch (service unavailable), and grep; direct
source inspection found Mathlib's ofExactOfSection and existing affine lifting and
projectivity. No new node was necessary. The unit record sk-thm-picard-rr has empty
realized bindings, and its mathematical local splitting step is retained.

## Second reading by N2

1. PASS: diffed the sole delivered module against the repository. The complete existing
   theorem signature is byte for byte identical, including universes, all three rank
   hypotheses, cover, isomorphism direction, and both map identities. No definition or
   visibility changed; no change record is required. The added helper is private and
   fully proved. Only proof imports changed, so downstream interfaces are preserved.
2. PASS: compiled the module locally with lcompile.py. Independently compiled a fresh
   scratch copy with explicit #print axioms for both the public theorem and private
   helper; both use exactly propext, Classical.choice, Quot.sound, without sorryAx.
   No sorry or prohibited declaration occurs. Projective lifting constructs the
   right inverse; naturality needs invertibility only of the quotient counit. The
   splitting and transport back across isoSpec give the stated biproduct identities.
   No definition chooses arbitrary data from an unproved existence theorem.
3. PASS: no split-off statement, new public statement, new node, or new hole exists.
   The private affine lemma is strictly a part of the argument and is fully proved.
   Zero quotient, zero kernel, zero ring and empty scheme require no extra hypothesis:
   projective lifting and affine coverage include them. The rejected local-section
   declaration really has the wrong composition order; the reported vector-space
   counterexample is valid, and neither theorem invokes it.
4. PASS: independently searched LeanFinder for projective surjection splitting and
   Loogle for ShortComplex splitting, and inspected Mathlib's ofExactOfSection and
   the upstream affine sections/rank results. LinearMap.exists_rightInverse_of_surjective
   is an alternative expression of the factorThru step, not a shorter sheaf argument;
   Loogle did not recognize the qualified query. The three proof imports supply affine
   lifting, projectivity/ring transport, and exact restriction, respectively. Existing
   public imports supply notions in the signature. The sole old proof dependency,
   lem-sc-local-section-quotient-finite-free, is listed as unused; its module is pruned.
   sk-thm-picard-rr has empty realized bindings; the determinant step still uses local
   sections, exactness, a biproduct splitting, and an open cover. No unit is bypassed.
5. PASS: read the original and delivered node and both new dependency nodes. Only
   proof, proof_deps, and proof_origin differ; proof_deps equals the union of uses.
   Affine projectivity is obtained through the proved rank criterion, which itself
   uses finitePresentation_projective_sections; affine lifting uses the other named
   dependency. The elementary categorical steps match the Lean proof. No new node
   requires schema validation.

Changed the existing theorem's proof docstring to describe affine lifting and the
actual affine cover instead of claiming application of the removed local-section
lemma. The proof code, signature, imports, and node records needed no repair.
Holes closed: exists_openCover_split_shortExact (1 of 1); holes added: none (0).
