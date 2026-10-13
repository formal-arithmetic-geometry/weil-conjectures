## What changed

Replaced the sole sorry in `AlgebraicGeometry.affineMorphism_hom_out_of_perfect`
with a complete Lean reduction. The public theorem's signature and visibility are unchanged.
The proof obtains the perfect dual and tensor-Hom isomorphism from
`perfect_rhom_tensor_comparison`, applies `torIndependent_perfect_tensor_baseChange`,
transports invertibility to internal Hom, and applies derived sections and the final comparison.

Added the proved private helper `baseChangeMap_naturality`. It constructs the natural
transformation before transposition from the exact choices occurring in
`schemeDerivedBaseChangeMap`; naturality of the adjunction Hom equivalence proves the square.
This uses no new hole and preserves the fixed canonical map.
The extra heartbeat budget is local to this helper; the recovered item compiled in 25.0 s.

Added `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization`, with one named theorem
for the remaining comparison of maps. It gives source and target isomorphisms and an exact
factorization through RΓ of sheaf base change on internal Hom. It assumes no Tor independence
and asserts no invertibility of base change. It isolates the compatibility argument in
parent steps 3 and 4; it is not a renaming or repackaging of the upper IsIso claim.
Updated the parent's proof, proof_deps and proof_origin and supplied the new node.
No existing definition, public signature or public import changed; no forced adaptations.

## Proved and sorry left

Closed the original direct hole:
`AlgebraicGeometry.affineMorphism_hom_out_of_perfect`
(`lem-pc-affine-morphism-hom-out-of-perfect`). There is no sorry in the item module.
The proof is complete from existing declarations plus the new comparison theorem.

Added exactly one direct hole:
`AlgebraicGeometry.affineGlobalHomBaseChange_factorization`
(`lem-pc-affine-global-hom-base-change-factorization`) in the new module.
Its proof is exactly `by sorry`; its docstring contains the five-step argument with the
source and fixed-map compatibility. The separate private naturality helper is proved.

This is a decomposition: one upper hole closed and one lower hole added, net zero direct
holes, not a proof of the entire transitive import closure. In particular the imported
`torIndependent_perfect_tensor_baseChange` and `exists_globalHomPullbackComparison`
remain existing upstream obligations; this delivery neither changes nor conceals them.
Both delivered modules compile cleanly with the required lcompile workflow.
The recovered sandbox was checked against the current theorem signatures and the fixed
mate definition of `schemeDerivedBaseChangeMap`; the comparison module compiled in 2.9 s
and the item in 25.0 s. The delivery dry run printed OK, with only the second reader
section deferred as required by this worker brief; nothing was pushed.

## No longer needed

Removed these seven proof-only imports from the item module:
`AffineDerivedPullbackTensorTilde`, `AffineQCohDerivedEquivalence`,
`DerivedDirectImagePreservesQCoh`, `DerivedPullback`, `DerivedPullbackTensorQCoh`,
`GlobalDerivedHom`, and `RingedSpaceDerivedDirectImageComposition`
(all under `Sheaf.AlgebraicGeometry`).
The first, second, third and seventh remain needed for the new comparison theorem and are
imported there. Global Hom and pullback definitions remain visible through the original
public `AffineGlobalHomBaseChangeMap` import. The representation-level QCoh tensor theorem
is not directly invoked by the item: the comparison node uses the existing perfect-source
RHom quasi-coherence theorem instead. It is still an upstream tensor-base-change dependency.

The corresponding original direct proof dependencies are removed from the parent's
proof_deps and replaced by the new comparison node and the declarations actually used.
The removed direct node dependencies are:
`lem-pc-derived-pullback-tensor-qcoh`,
`lem-pc-derived-direct-image-preserves-qcoh`, `def-pc-global-derived-rhom`,
`lem-pc-ringed-spaces-derived-direct-image-composition`,
`lem-pc-affine-qcoh-derived-equivalence`,
`lem-pc-affine-derived-pullback-tensor-tilde`, and `def-pc-derived-pullback`.
This lists removal from the parent's direct proof route, not removal from its import closure.
No whole node or module is claimed globally pruned: those affine/QCoh comparisons are still
needed below the new lemma or below the existing tensor-base-change theorem. The unit route
is retained: perfect dual, tensor base change, perfect pullback comparison, affine sections.

## Where the brief, the DAG or earlier work was wrong

The original node's source field and proof references call this theorem Tag 0AVW.
The actual theorem is Stacks Tag 0AA7, `lemma-affine-morphism-and-hom-out-of-perfect`,
case (1), at https://stacks.math.columbia.edu/tag/0AA7 . Tag 0AVW instead concerns the
affine direct-image equivalence. The statement and intended perfect-dual route are correct;
no target statement has been changed. The existing source field was left untouched because
stage-3 edits to existing nodes are restricted to proof fields and lean records.
The new node cites the correct tag, and the parent's proof_origin records the correction.

The stated affine equivalence and tilde/pullback theorem give object/functor comparisons,
not the final equality with the particular evaluation- and unit-normalized global Hom map.
That compatibility is now an explicit lower obligation rather than an implicit transport.

Mathlib search found underived adjunction ingredients and generic naturality, no exact
scheme global Hom factorization. LeanSearch returned Internal Server Error and is recorded
as unavailable, not as a mathematical negative result. DAG, project and blueprint searches
found no existing factorization with this statement.

Edge cases for the new comparison were checked in the mathematical argument: zero M or K
and the empty scheme produce zero objects; identity g gives the unit-compatible identity
comparison; arbitrary nonflat g is permitted because the comparison lemma assumes no Tor
independence and makes no IsIso assertion about sheaf base change. K is unbounded throughout.
The canonical internal-Hom pullback isomorphism uses perfectness of M, not flatness of g.

## New nodes

`lem-pc-affine-global-hom-base-change-factorization`:
`Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization`, declaration
`AlgebraicGeometry.affineGlobalHomBaseChange_factorization`. It records exactly the missing
identification of maps, with a source/target isomorphism factorization through the fixed
sheaf base-change arrow on RHom(M,K). The parent supplies invertibility of that middle
arrow by an independent, fully written Lean argument. The statement's universes and
localization instances match those of the parent, and it adds no new condition on M or K.
No change record is required: no existing interface or definition changes.


## Second reading by K4

1. Interface: PASS. Diffed the existing module against the read-only repository and
checked the theorem signature byte for byte, including every derived-category instance,
qcqs hypothesis, Tor-independence hypothesis and IsIso conclusion. The existing docstring,
public imports, visibility and definitions are unchanged. No change record or forced
adaptation is needed. The only existing-node fields changed are proof, proof_deps and
proof_origin.

2. Proof and trust: PASS as a decomposition. Compiled both delivered modules in import
order using lcompile.py: 4.2 s and 35.1 s, no errors or warnings. Scratch-copy axiom checks
on baseChangeMap_naturality, affineMorphism_hom_out_of_perfect and
affineGlobalHomBaseChange_factorization give only propext, Classical.choice, Quot.sound
and sorryAx. The naturality helper has no local hole: its sorryAx comes from existing
derived-pullback/adjunction dependencies. The single delivered sorry is the named
factorization theorem reported above. No forbidden declaration, compiler bypass,
new definition, or arbitrary existential data choice occurs. The helper uses exactly
the normalized choices already in schemeDerivedBaseChangeMap. The perfect dual is
determined by its recorded equality with RHom(M,O_X), and a and b are destructured
inside a proof, not used to define new data.

3. Split statement: PASS. The factorization is a compatibility assertion without hTor
or any IsIso conclusion for the base-change arrow; it cannot substitute for the
independent tensor-base-change argument. Its a is the affine extension/pullback and
composition comparison; b is sections of the perfect-source internal-Hom pullback
isomorphism. Reviewed its five-step docstring, matching node and hypotheses. Identity
base change gives the unit-compatible comparison, zero M or K and the empty scheme
give zero objects, and a nonflat g is allowed: only perfect-source Hom pullback must
be invertible, not sheaf base change. No boundedness assumption is introduced for K.
Checked the canonical map construction against Stacks
[0AA7](https://stacks.math.columbia.edu/tag/0AA7) and the evaluation-mate definition in
[08I3](https://stacks.math.columbia.edu/tag/08I3). Repeated LeanFinder, Loogle and Mathlib
grep searches with different terms (affine sections/extension, Beck-Chevalley and mate
naturality), and searched project and upstream Lean sources. Found generic adjunction
naturality and underived sheaf adjunctions, no existing derived affine global Hom
factorization. The private helper in ProperFlatRightAdjointBaseChangeHbeta is an
analogous naturality proof, not an accessible factorization theorem. The remaining
comparison needs construction and normalization of both isomorphisms; it cannot be
closed in a short proof from an existing declaration.

4. Route and pruning: PASS. Read the imported perfect tensor-Hom and tensor-base-change
statements and followed the proof top down: choose the perfect dual, apply tensor
base change, use mate naturality to transport invertibility, then apply sections and
the factorization. All seven removed imports and all seven removed direct node
dependencies are now explicitly listed in No longer needed. Dependencies used in the
new factorization remain there, and no globally pruned module is claimed. The unit
sk-thm-picard-duality has empty realized statement and step lists; this item is below
the unit level. Its intended dual/tensor/base-change/affine-sections route is retained.
All new proof dependencies are private imports or already publicly available through
unchanged statement imports.

5. DAG: PASS. Checked the new node's source, chapter, unit, blueprint lineage, creation
record, search records, split status and Lean record. Its Lean statement matches the
new module verbatim. Each node's proof_deps equals the union of its proof-step uses.
The parent records the actual perfectness, adjunction, tensor-base-change, canonical
mate and factorization dependencies; its proof_origin records the correct Stacks tag
without silently altering the existing source or statement.

Second reading changed only this report: added this independent verdict and explicitly
enumerated the seven removed direct proof-dependency nodes. No Lean or node repair
was necessary. One original hole closed, one strictly smaller compatibility hole added;
net zero direct holes, with existing transitive obligations still open.
