## What changed

Proved `AlgebraicGeometry.RingedSpace.pointwise_truncation_limit_isIso` with its existing
signature and visibility unchanged. Added the fully proved module
`Sheaf.Topology.PointwiseTruncationOpenStabilization`: it constructs the common natural
cutoff, computes all three endpoint vanishings through shift and single-object comparisons,
and applies the long exact sequence of the successive truncation triangle.
The original theorem now uses this stabilization, the existing eventual-isomorphism
inverse-limit theorem and `derivedLimit_stalk_injective`. Private proved helpers handle
composites in a tower and reflection of stalkwise bijectivity. Compatibility and cancellation
of the injective projection prove bijectivity of the map on every stalk.
Only proof imports were changed in the existing module. Updated its node to the actual route.

The source read was Stacks Cohomology, Tag 0D62, `lemma-is-limit-per-point`, and Tag 0D61,
`lemma-cohomology-derived-limit-injective`, available in the local literature mirror.
Both delivered modules compile cleanly with the authorized local compiler.
The unit record `sk-thm-picard-duality` has no realized nodes at this level; no unit step
or statement has been bypassed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.RingedSpace.pointwise_truncation_limit_isIso`
(node `lem-pc-ringed-space-pointwise-truncation-limit-isIso`).
Also fully proved `AlgebraicGeometry.RingedSpace.pointwise_truncation_open_stabilization`
(node `lem-pc-pointwise-truncation-open-stabilization`).
There are no sorries in either delivered module, and no holes added or split off.
This is a proof from existing dependency declarations, including the existing unfinished
`AlgebraicGeometry.RingedSpace.derivedLimit_stalk_injective`; it is not a claim that the
transitive closure is axiom-free yet. That dependency was not edited or duplicated.

## No longer needed

Removed direct proof imports of `Sheaf.Algebra.Homology.LowerTruncationStepTriangle`,
`Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups` and
`Sheaf.Topology.RingedSpaceRGammaDerivedLimit` from the original module.
The lower truncation triangle remains needed by the new stabilization module; Roos remains
needed through `Sheaf.CategoryTheory.DerivedLimitEventuallyIso`; the global-sections/limit
comparison remains needed through `Sheaf.Topology.DerivedLimitStalkInjective`.
These are removed direct imports, not claims of pruning their transitive theory.
`lem-weil-pbc-hom-into-triangle-exact` is unnecessary for this isomorphism theorem: it
belongs to the separate existence half and is removed from this node's proof dependencies.
The direct DAG edges to the lower-step triangle, Roos and the global-sections comparison
are likewise replaced by the dependencies that encapsulate their actual use.
No other node or module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The original node included Hom-into-triangle exactness, which supplies existence of a
compatible morphism, while this theorem already assumes such a morphism.
The needed eventual-isomorphism inverse-limit lemma already exists as
`Sheaf.CategoryTheory.DerivedLimitEventuallyIso`, and avoids reproducing the Roos recursion.
The existing scheme/quasi-coherent uniform stabilization theorem cannot be applied to
arbitrary ringed spaces and the degree-dependent local bounds here.
LeanSearch returned Internal Server Error; it is recorded as unavailable, not as no match.
Loogle rejected the unqualified `IsIso` query; the semantic and source searches were used.
The blueprint ancestor tool reports no imported blueprint ancestor for the assigned split
node; the new node records this null result and the exact source-proof location.

## New nodes

`lem-pc-pointwise-truncation-open-stabilization` (module
`Sheaf.Topology.PointwiseTruncationOpenStabilization`) is the strictly smaller stabilization
step of Tag 0D62. It assumes only the vanishing bound for a family of opens and proves
isomorphisms of two open-cohomology transition maps, without any derived limit or compatible
morphism. It is fully proved. The chosen cutoff also guarantees nonnegative classical
cohomology degrees. Empty families, the zero object, arbitrary negative m or bounds, and
n equal to the chosen cutoff are all covered by the same inequalities. Mathlib semantic
search found only generic truncation/support statements; direct source search found the
single-object comparison used in the proof. No new definition or change record is required.

## Second reading by C3

1. **Visible declarations: pass.** Read the full diff against the repository module.
   The entire signature of `pointwise_truncation_limit_isIso`, from `theorem` to
   `:= by`, is byte-for-byte identical (also checked programmatically). All four
   original public imports remain identical. The added imports in that module
   are proof-only. No existing definition, visibility or statement changes, and
   no forced adaptations or change records are needed.
2. **Kernel proof: pass with existing dependency holes.** Compiled both modules
   together in import order with `lcompile.py --all`: clean, 6.3 and 6.8 seconds.
   A scratch copy printing axioms compiled cleanly. The stabilization theorem has
   exactly `propext`, `Classical.choice`, `Quot.sound`; the original theorem has
   those and `sorryAx`, from pre-existing open dependencies, including
   `derivedLimit_stalk_injective`. Neither delivered file contains `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by` or `extern`. There are no data
   definitions or arbitrary existential witness choices in this delivery.
   The private tower helper uses induction from the identity at N, and the
   stalk helper uses the underlying sheaf criterion and reflection by `toSheaf`.
3. **New statements: pass.** No statements are split off with holes. Read the new
   stabilization signature against its node and Stacks Tag 0D62,
   `lemma-is-limit-per-point`, final paragraph, in the local literature mirror
   `/home/ubuntu/weil-launcher/maint/bp/work/literature/stacks-project/cohomology.tex`.
   Also checked Tags 0D62 and 0D61 on the Stacks website. The arbitrary family B
   needs no basis assumption for this smaller conclusion. The cutoff is a natural
   integer strictly beyond all four bounds; at n=N, the three classical degrees
   m+n, m+n+1 and m+n+2 are nonnegative and exceed the respective b bounds.
   Empty B, zero E, negative m and negative b values cause no exception.
   The shift is q+n+1, giving q-p=-n-1 exactly. Re-searched with LeanFinder for
   "cohomology of derived sections is unchanged between successive sufficiently
   negative truncations": only general complex truncation results, no exact match.
   Searched Mathlib through msearch and the library with rg. Read
   `isIso_rightDerivedFunctor_lowerTruncation_step` in
   `Sheaf.AlgebraicGeometry.DerivedFunctorTruncationStabilization`: its scheme,
   quasi-coherence and uniform functor bound hypotheses do not apply here.
4. **Route and pruning: pass.** Read both proofs from the top down. The three
   endpoint zeros give two successor isomorphisms via the existing lower-step
   triangle and `DerivedCategory.isIso_homologyMap_mor₂`. Eventual isomorphisms
   kill the first derived limit; finite composites supply the degree-m
   injectivity required by Tag 0D61. Compatibility gives a bijective composite
   through the injective projection; cancellation proves surjectivity and the
   composite proves injectivity of the map from E. No existence of c is assumed
   without the explicit binder. All removed old proof-dependency edges are
   accounted for under No longer needed: lower-step triangle, Roos, the
   derived-sections/limit comparison, and Hom-into-triangle exactness. The first
   three remain encapsulated dependencies; only the fourth is unused here.
   `dag/units/sk-thm-picard-duality.json` has empty realized statement and step
   lists; its route is unchanged. No global module pruning is claimed.
5. **Nodes: pass.** Compared the existing node with its repository version:
   changes are confined to proof, proof_deps and proof_origin. Read the new
   node's self-contained statement, source, proof steps, dependency union,
   actual search records, blueprint record, created fields and verbatim Lean
   signature. Each triangle, shift, single-object comparison and exactness step
   follows the declarations cited by its nodes (including Mathlib matches).
   The new node is strictly the local stabilization step, not a relabelling of
   the derived-limit isomorphism theorem, and its proof is fully closed.

Second reading changed only this report, adding the independent checks and exact
axiom results. No Lean or node repair was necessary. Holes closed: the one
original `AlgebraicGeometry.RingedSpace.pointwise_truncation_limit_isIso` hole;
holes added: none. The additional stabilization theorem is fully proved.
