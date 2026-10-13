## What changed

Completed the proof of `AlgebraicGeometry.Scheme.exists_finite_extension_of_depth_two`
without changing its signature or any existing public interface. Added proof-only imports
of `DepthTwoPushforwardCoherence`, `FiniteStructureAlgebraDepth`,
`RelativeSpectrumAffineRealization`, and `AffineMorphismRelativeSpec`.

The proof uses the actual direct image algebra of `f` followed by the open inclusion.
The existing affine-realization theorem constructs its relative spectrum. The finite
section maps and the algebra-isomorphism equation prove finiteness directly. An explicit
restriction algebra isomorphism and the existing affine structure-algebra equivalence
produce the required scheme isomorphism and its equation over U. The boundary depth
comparison completes the assembly. Two new modules isolate the remaining mathematical
arguments; their statements have complete source-based proofs in their docstrings.
The item's node now records this exact route.
A private abbreviation expands to the existing `Under.mk` direct-image algebra
construction; it introduces no public notation or interface change. Both private
restriction/isomorphism helpers have complete proofs.

Validation: all three sandbox modules compile cleanly through lcompile.py. The required
deliver3.py --no-push dry run printed OK: compilation, the axiom probe and static
preflight pass, with only the second-reader section pending for the next worker.
Nothing was pushed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_finite_extension_of_depth_two`
(`lem-sbc-depth-two-finite-extension`). There is no sorry in the item's module or its
private helpers. This is a decomposition, not a proof with only the three standard axioms:
one original hole closed, two named holes added, net -1 before downstream pruning.

Added holes, each the entire proof of one public theorem in a separate module:

- `AlgebraicGeometry.Scheme.depth_two_pushforward_coherence`,
  node `lem-sbc-depth-two-pushforward-coherence`, module
  `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoPushforwardCoherence`.
- `AlgebraicGeometry.Scheme.depth_two_of_finite_structure_algebra`,
  node `lem-sbc-finite-structure-algebra-depth`, module
  `Sheaf.AlgebraicGeometry.Morphisms.FiniteStructureAlgebraDepth`.

The first theorem asserts properties of a fixed, explicitly constructed algebra; it
constructs no scheme or restriction isomorphism. The second is a general depth transfer
for a supplied finite morphism and a supplied algebra isomorphism; it constructs no
extension and makes no restriction assertion. Thus neither restates the original theorem.
The finite-scheme construction, finiteness argument, restriction comparison and final
assembly are actual Lean proofs using these strictly smaller statements.

## No longer needed

None. The original node had no proof dependencies, and the original module had no
proof-only imports to remove. No pre-existing node or module is claimed pruned. The two
invalid split modules of the earlier attempt remain absent. All four newly added
proof-only imports supply declarations used by the proof. No coherence-extension,
double-dual, or Hartogs modules are imported speculatively.

## Where the brief, the DAG or earlier work was wrong

The original DAG names no declarations for either of its non-elementary proof steps.
The new coherence theorem isolates its first step, and the general finite-algebra depth
transfer isolates the last part of its second step. The existing relative-spectrum and
affine structure-algebra declarations supply the rest.

The earlier attempt discarded all information connecting E to X, then asserted a
restriction isomorphism for an arbitrary E. That is false for U = L, E empty and X
nonempty. Here the algebra isomorphism to the actual pushforward of X is retained
throughout, and the restriction isomorphism is proved from it, not assumed.

Edge cases checked mathematically before stating the new lemmas: U = L makes boundary
conditions vacuous and the canonical algebra recovers the finite affine cover. An empty
cover gives the zero algebra, whose depth is infinity, and its relative spectrum is
empty. If U is empty, the boundary hypothesis remains substantive and the canonical
algebra is zero. A disconnected cover and a nonintegral or nonnormal base cause no
change in the local double-dual argument. The transfer lemma uses a supplied algebra
isomorphism and works with no etaleness assumption; a zero stalk has no points above
it. In particular it cannot identify an unrelated empty scheme with a nonempty cover.

The unit `sk-prop-input-spreading` still uses the same depth-two extension input; no
unit statement or step is bypassed. The generic relative-spectrum and affine
structure-algebra nodes are used as tools for the construction prescribed by 0EY6.
No statement corrections, forced adaptations, or change records are needed.

Searches were run using msearch.py (recorded in searches.jsonl). LeanSearch returned
HTTP 500 and is recorded as unavailable. Loogle returned quasi-coherence infrastructure
but no boundary extension result; the finite-depth query returned no hits. Mathlib grep
found no relevant boundary-coherence or finite-depth comparison result. Whole-library
searches found the affine realization and structure-algebra equivalence, both used.
The existing depth-over-quotient theorem concerns surjective scalar change, not the
finite semilocal comparison needed here. Blueprint searches found no duplicate nodes.

## New nodes

`lem-sbc-depth-two-pushforward-coherence` is in
`dag/nodes/sec-smooth-base-change/lem-sbc-depth-two-pushforward-coherence.json` and records
coherence, finite affine section maps and boundary stalk depth for the actual canonical
algebra. Its source is Stacks 0EY6(1), the depth assertion in the proof of (2), and the
0E9I Hartogs identification, with the double-dual proof written out.

`lem-sbc-finite-structure-algebra-depth` is in
`dag/nodes/sec-smooth-base-change/lem-sbc-finite-structure-algebra-depth.json` and records
the depth transfer for any supplied finite realization of an algebra. Its source is
Stacks 0AUK as used in 0EY6(2). It explicitly retains the algebra isomorphism and does
not assert any restriction isomorphism. Both nodes have complete Lean signatures,
source-based numbered proof plans, and three kinds of actual Mathlib search.


## Second reading by T3

1. Interface preservation: PASS. Read the complete diff of the original module and
   its node against the read-only repository. The existing theorem signature and
   docstring are byte-for-byte unchanged. The only existing-module additions are
   four plain proof imports and three private helpers; its original public imports
   remain unchanged. No existing definition, target, visibility, statement, or
   statement dependency changes. No change record or forced adaptation is required.
2. Proof and axioms: PASS as a decomposition. Independently compiled all three
   delivered modules with lcompile.py --all, without errors or warnings. Scanned
   the delivered sources: precisely the two reported public theorems have sorry,
   each as its entire proof; no forbidden declaration or hollow definition occurs.
   Compiled separate scratch copies with #print axioms for all six declarations.
   Both private isomorphism helpers and the explicit direct-image abbreviation use
   only propext, Classical.choice, Quot.sound. The original theorem and the two
   split theorems additionally use sorryAx, exactly as expected. The structure
   algebra is the explicit Under.mk of the actual composite morphism, and the
   restriction isomorphism is constructed componentwise, not chosen from a mere
   unproved existence assertion. Scheme witnesses are eliminated within the
   theorem's proof; no data definition chooses an arbitrary unproved witness.
3. Split statements: PASS. Read both Lean signatures, docstring proofs and complete
   node records. Checked the coherence/depth argument against Stacks 0EY6 and
   Hartogs 0E9I, and the finite-algebra depth comparison against 0AUK:
   https://stacks.math.columbia.edu/tag/0EY6,
   https://stacks.math.columbia.edu/tag/0E9I,
   https://stacks.math.columbia.edu/tag/0AUK.
   The first lemma concerns a fixed direct image algebra and asserts no extension;
   the second accepts a supplied finite morphism and an algebra isomorphism and
   asserts only depth transfer. Neither restates the original existential result.
   For U = L the boundary estimates are vacuous. Empty covers give zero modules
   of infinite depth and empty relative spectra. For U empty, the given cover is
   empty, so the canonical algebra is zero. For the transfer lemma a zero stalk
   gives an empty fibre; a disconnected finite algebra is handled by the minimum
   over its maximal ideals. The kernel argument works over a nonnormal base and
   does not use integrality. Finite generation and Nakayama ensure that the regular
   pair is a regular sequence on a nonzero kernel. Independent searches, recorded
   in searches.jsonl, used leanfinder for coherent reflexive restriction, loogle
   for regularity under localization, and grep for coherent/reflexive and semilocal
   depth/stalk comparisons. Also searched both library roots for Hartogs and depth
   localization results. Hits provide special cases or underlying infrastructure,
   not either new theorem. Neither hole can be closed in a few minutes from these
   declarations; the existing Hartogs results assume a regular integral base.
4. Route and pruning: PASS. Read the two existing relative-spectrum modules used
   by the proof. Finiteness follows directly from the finite affine section maps
   and the algebra-isomorphism equation. Restriction to U uses the canonical
   restriction identification; full faithfulness supplies an isomorphism over U
   with the exact required equation. All four added proof imports are used. The
   old proof_deps was empty, so No longer needed is complete and nothing is
   pruned. Read dag/units/sk-prop-input-spreading.json: its depth-two extension
   step is preserved, and no unit is bypassed. Its realized arrays are already
   empty in the repository; this delivery neither edits them nor claims to repair
   that pre-existing unit bookkeeping gap.
5. DAG/Lean agreement: PASS. The existing node's only differences are proof,
   proof_deps and proof_origin. Its four dependencies are exactly the coherence,
   affine realization, affine structure-algebra equivalence and depth-transfer
   declarations used by the Lean proof. The new nodes have their source, complete
   numbered proof plans, searches, creation/blueprint provenance, chapter/unit,
   and verbatim Lean statements; their definitions and module paths agree with
   the files. Their open non-elementary steps are accurately recorded as open
   mathematical work, rather than asserted to be elementary or already proved.

Second-reading changes: appended this independent review and the axiom/search
results to the report; no Lean or DAG repairs were necessary. The delivery remains
one original hole closed and two holes added, a decomposition with net -1 before
pruning, not a completed proof with only standard axioms.
