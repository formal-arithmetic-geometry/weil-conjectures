## What changed

The existing declaration `AlgebraicGeometry.Scheme.Modules.exists_universally_mono_free`
has exactly its original signature and public imports. Its proof now obtains a finite free
quotient of `dual M` and constructs the embedding as the explicit composite of
`SheafOfModules.bidual M`, `dualMap β`, and `SheafOfModules.homObjFreeUnitIso`.
The properties of that particular composite come from the local dualization lemma.

The second reader replaced the preliminary clause-based split in `QuasiAffineEmbeddingAux`
with two separate modules, one per new statement:

- `Sheaf.AlgebraicGeometry.Modules.QuasiAffineFiniteFreeQuotient` states global finite
  generation, with no embedding or base-change conclusion.
- `Sheaf.AlgebraicGeometry.Modules.DualFiniteFreeQuotientEmbedding` states the properties
  of the actual transpose of a supplied epimorphism. It works on any scheme and has no
  global-generation or Noetherian hypothesis.

Both new imports in the original module are proof-only `import`s. The first new module
retains a proof-only import of the original denominator-clearing dependency; the second
publicly imports `Dual` because the new signature mentions duality and its actual maps.
The existing node's proof and dependencies now describe this Lean reduction.
No existing definition, declaration signature, or visibility changed; no change record
or forced adaptation is needed.

## Proved and sorry left

Hole closed in the item's module:
`AlgebraicGeometry.Scheme.Modules.exists_universally_mono_free`
(node `new-sbc-quasi-affine-locally-free-embedding`).

Two holes added, each a public named theorem with a complete natural-language proof:

- `AlgebraicGeometry.Scheme.Modules.exists_epi_free_of_isFiniteLocallyFree`, in
  `QuasiAffineFiniteFreeQuotient` (node `new-sbc-quasi-affine-embedding-existence`).
- `AlgebraicGeometry.Scheme.Modules.dual_free_quotient_embedding`, in
  `DualFiniteFreeQuotientEmbedding` (node `new-sbc-quasi-affine-embedding-pullback`).

This is a decomposition: one upper hole closed and two smaller holes added, a local
net of minus one. The target is not independently sorry-free. No hole was closed in
these two intermediate statements. The preliminary lemmas
`exists_mono_free_with_locally_free_cokernel` and
`mono_pullback_of_locally_free_cokernel` were never landed and are not delivered.
There is no data definition chosen from an unproved existence theorem: the quotient
witness is eliminated inside a proof, and the embedding is an explicit composite.

## No longer needed

None of the repository's imports or old dependency nodes is pruned. The sole old
proof dependency `lem-pc-section-clearing-denominators` is used transitively by the
finite free quotient node and its module still stays in the target's import closure.
The target's direct proof dependencies are now the two new nodes. The sandbox-only
`QuasiAffineEmbeddingAux` was removed; it is not a pruned library module.

## Where the brief, the DAG or earlier work was wrong

The first worker's existence lemma retained almost all of the target's conclusion;
the report also called the upper hole proved without explaining the negative hole net.
Its docstring's assertion that local presentations glue did not explain the extension
of basis sections. The target node was not updated, and both new nodes referred back
to the target instead of stating their own hypotheses. The new modules had shared one
file despite the one-new-statement-per-module instruction. These faults are repaired.

The second reader searched independently for quotients by finite free sheaves and
transposes of locally split surjections. Loogle found an arbitrary free Yoneda
coproduct epi, not a finite globally free quotient. LeanFinder found local generators
and presentations, not either new result. Grep found algebraic finite-presentation
lemmas and unrelated categorical dual constructions. LeanSearch returned Internal
Server Error, recorded as unavailable without claiming a negative result. Queries and
actual result digests are recorded in the new nodes from this sandbox's searches.jsonl.
Local searches of `lean/Sheaf` and `lean/WeilConjectures` also examined `Dual`,
`InternalHomFree`, `Bidual`, `ClearDenominators`, `LocalSplittingFiniteFree`,
`AmpleTwistGlobalGeneration`, and `FiniteLocallyFreeTensorExact`.
The ample-twist theorem needs an absolute ampleness witness; the available local-splitting
theorem requires constant ranks and a supplied short exact sequence, so neither directly
closes the remaining statements. The proved dual and finite-free dual isomorphism APIs
are used in the actual upper reduction.

## New nodes

`new-sbc-quasi-affine-embedding-existence` states a finite free epimorphism onto a
finite locally free module on V. Its proof uses a finite principal affine cover and
`lem-pc-section-clearing-denominators` to extend local generators. This is solely the
global-generation part of the original argument, with no existential embedding hidden
in it. Its Lean record points to `QuasiAffineFiniteFreeQuotient`.

`new-sbc-quasi-affine-embedding-pullback` states local properties of a specified composite
for an already supplied epimorphism onto the dual of a finite locally free module.
Affine local splitting gives the locally free cokernel, and pulling back local left
inverses gives universal monicity. This is the local linear algebra part of the argument,
independent of Noetherianity and quasi-affineness. Its Lean record points to
`DualFiniteFreeQuotientEmbedding`.

## Second reading by C3

1. Compared the delivered target module with the repository using diff. The signature
   of `exists_universally_mono_free`, its universe, all hypotheses, the finite index
   `ULift.{u} (Fin r)`, its categorical cokernel condition, and the quantification over
   all scheme pullbacks are byte-for-byte unchanged. Only its proof and two proof-only
   imports differ. There are no existing definitions or other modules adapted. Verdict:
   interface preserved.
2. Compiled all three final modules in import order through lcompile.py. The original
   module contains no sorry; exactly the two listed auxiliary theorems have a single
   whole-body sorry each. No forbidden declaration or attribute is present. A scratch
   copy printed axioms of all three declarations: only propext, Classical.choice,
   Quot.sound, and the expected sorryAx from the two open lemmas. The delivery tool
   also runs its all-declaration axiom probe before pushing. No definition contains a hole or
   an arbitrarily chosen witness. Verdict: a valid conditional reduction, with its
   remaining holes explicit.
3. Read Stacks Project Tag 0EKP, proof of (2) to (3), at
   https://stacks.math.columbia.edu/tag/0EKP. The existence statement has precisely the
   Noetherian ring, arbitrary open, and finite locally free module needed for the finite
   principal cover and global section extension. Its proof now explains why multiplying
   by a power of the defining function preserves generation. In the local lemma, the
   epimorphism onto the dual splits after restricting to affine trivializing opens; its
   projective kernel becomes finite free after further shrinking. Transposition and
   biduality identify the displayed map, including its finite-free dual comparison,
   with the split inclusion. For pullback, the inverse-image cover and pulled-back left
   inverses suffice; flatness of the scheme morphism is not assumed. Tested the arguments
   on the empty open/empty scheme, zero module, r=0, and varying local ranks. For r=0,
   epimorphy forces the locally free dual, hence M, to be zero; the conclusions still
   hold. Independent searches are described above. Verdict: true intermediate results,
   each a proper part of the construction, not a relabelled target.
4. The upper proof uses the already proved dual-local-freeness, biduality, and finite-free
   dual-comparison APIs, then the two geometric components. The explicit composite is
   the map whose properties the new local lemma states. The denominator-clearing route
   is retained through the quotient node. No old dependency is bypassed. Opened
   dag/units/sk-prop-input-spreading.json: its realized.statement and all realized.steps
   entries are empty, and this item is not the unit statement; neither the unit nor any
   chapter route changes. Imports for signatures are public; newly added proof-only
   dependencies in the target are plain imports. Verdict: route retained, pruning list
   complete (none).
5. Opened the parent and both new JSON records. Replaced the parent's old proof and
   proof_deps with the two Lean applications. Replaced the new nodes' target-dependent
   hypothesis references by self-contained statements and definition dependencies,
   eliminating the potential dependency back-edge. Their signatures are copied verbatim
   from the new modules, their proof_deps are the union of their steps' uses, and source,
   provenance, search records, creation data, chapter and unit match the delivery.
   Verdict: the DAG agrees with the final Lean reduction.

Second reading changed the preliminary split to finite free quotients plus explicit
transposition; separated the new modules; expanded both docstring proofs; repaired the
parent and new nodes and actual search records; and corrected the report's hole accounting.
