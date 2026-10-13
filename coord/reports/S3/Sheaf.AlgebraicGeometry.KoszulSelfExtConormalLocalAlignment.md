## What changed

Replaced the sorry in
`AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_local_alignment`
with a compiled reduction. A new geometric lemma produces compatible comparisons
on one chosen cover. The original module proves the global gluing step: compatibility
of inverse components, gluing of both directions, verification of both inverse
identities by local equality, restriction to every supplied neighborhood, and
construction of the correcting automorphisms. The private helper
`iso_of_compatible_cover` is proved without a sorry.

No existing declaration signature, definition, or public import changed.
The unit's realized lists are empty, and its statement and route remain untouched.
The generic gluing theorem is a tool for sheaf morphisms, not a replacement of
any step of the Picard-duality unit.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_local_alignment`
(node `new-w4-koszul-self-ext-local-alignment`).
Added one hole in
`AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_compatible_cover`
(node `new-s3-koszul-conormal-compatible-cover`). No other sorry remains in the
delivery. This is a decomposition with net zero holes, not a complete proof of
the geometric comparison. The remaining lemma stops before global gluing: it
produces only one compatible cover rather than handling arbitrary prescribed
neighborhoods and correcting an arbitrary family of isomorphisms.

Both modules compile with lcompile.py. The chosen-cover lemma was checked on
empty V, degree zero, degrees greater than the generator length, and the zero
quotient: these cases impose no invalid positive-rank assumption. A nonzero local
ring is used only at an actual point of Z.

## No longer needed

Removed the following direct proof imports from the original module:

- Sheaf.RingTheory.KoszulProjectiveResolution
- Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification
- Sheaf.Paper.DerivedInternalHomRestrictOpen
- Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel
- Sheaf.AlgebraicGeometry.AffineConormalFrame
- Sheaf.RingTheory.KoszulConormalBasis
- Sheaf.RingTheory.KoszulGeneratorChainMap

Their seven DAG nodes remain in the new geometric lemma's proof plan, so none is
claimed as globally pruned. The original node now depends directly only on the
new compatible-cover node and `lem-weil-pbc-glue-sheaves-of-modules`.
All existing public imports are retained because they support the signature.

## Where the brief, the DAG or earlier work was wrong

The old one-step plan combines chart construction, chart comparison, global
gluing, and correction of arbitrary local isomorphisms. The available finite-free
and conormal-frame statements give existence of frames, but do not assert their
normalized compatibility. In particular the local-isomorphism theorem in
KoszulSelfExtConormalLocalComparisonCore does not imply compatibility.
The generator-chain-map theorem explicitly records its exterior-power component
only at the top degree r; its proof constructs all degrees, but the stated
interface alone does not give every degree-n formula required in this plan.
This is a remaining interface issue for the geometric-cover worker, not a reason
to assume that arbitrary supplied frames agree.

Stacks 0BQY was read online: its displayed zero-differential Hom identification
supports the chart calculation, while its main statement concerns Yoneda exterior
products. The comparison-of-generators argument in the node is agent-written
elaboration, not an explicit assertion of that tag. Stacks 062I was also read;
its first exact-sequence calculation gives the conormal basis. The local Stacks
source is absent on this machine. Search tools found general sheaf gluing tools
but no normalized Koszul comparison theorem.

## New nodes

`new-s3-koszul-conormal-compatible-cover`, in
`dag/nodes/sec-picard-framework/new-s3-koszul-conormal-compatible-cover.json`,
records the pre-gluing regular-chart comparison step. Its module is
`Sheaf.AlgebraicGeometry.KoszulSelfExtConormalCompatibleCover`; its source and
full natural-language argument are in the theorem docstring. Blueprint search
for "Koszul comparison" returned no existing blueprint node. No change record
is needed because all existing interfaces are unchanged.

## Second reading by S3

1. I compared both delivered modules with the repository versions. The existing
   public theorem signature is byte-for-byte unchanged; the only interface addition
   is the separately recorded split-off compatible-cover theorem.
2. I compiled both modules with `lcompile.py --all`. They compile without errors.
   The local-alignment theorem has no `sorry`; the split-off compatible-cover theorem
   has the one documented `sorry`, and no definitions contain `sorry`.
3. I checked the split-off statement against the edge cases described in its
   docstring (empty open, degree zero, degree beyond the generator length, and zero
   quotient). It is a strict pre-gluing reduction and is not a restatement of the
   parent theorem. No duplicate declaration was found by repository searches.
4. I checked the proof route and pruning. The alignment proof uses the compatible
   cover and the sheaf-module gluing theorem, while the seven former direct proof
   imports are removed. The Picard-duality unit's realized route remains untouched.
5. I checked the DAG updates: the alignment node now records the two actual proof
   dependencies and the new compatible-cover node records its split theorem,
   declaration, source, and proof plan. Verdict: the delivered proof is sound as a
   decomposition, with the geometric comparison hole explicitly preserved.

I added this second-reading record only; no Lean statement or definition required
repair.
