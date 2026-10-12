## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.exists_local_finiteFree_truncation_zero`
to flatness of the degree-zero opcycles, with the original signature unchanged.
The target module now constructs the finite global presentation from the supplied
isomorphisms of Q.X (-1) and Q.X 0 with finite free modules. It uses the existing
source affine-sections criterion to obtain finite local freeness, chooses a local
basis, changes its finite index type to ULift (Fin r), and explicitly transports
that basis to the canonical truncation through pullback and cokernel isomorphisms.
Only right exactness of pullback is needed for the final comparison.

Added `Sheaf.AlgebraicGeometry.FlatModelOpcyclesFlat` for the strictly smaller
flatness step. Its statement has no local trivialization, rank or truncation
conclusion. Its proof in words handles C without assuming quasi-coherence: on a
fixed affine neighbourhood its stalks are filtered colimits of section modules
flat over that affine ring. The new module imports the existing planned algebraic
and stalk dependencies. Updated both DAG proof records to describe this route.

All delivered modules compiled through lcompile.py, without warnings. No existing
signature, definition or public import changed. No other existing module was adapted.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_local_finiteFree_truncation_zero`
(node `lem-pc-flat-model-finite-free-truncation-zero`): its proof is complete Lean.
The two private helpers `finitePresentation_opcycles_zero` and
`finiteLocallyFree_of_flat_finitePresentation` are proved without sorry.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.isFlatOver_opcycles_zero_of_quasiIso`
(node `lem-pc-flat-model-opcycles-flat-zero`), in its own new module, with proof
exactly `:= by sorry` and a complete sourced proof in words. This is a one-to-one
decomposition, not a claim that the original theorem is now independent of sorry.
There are no sorries left in the original module and no other holes added.
Existing imported statements retain their own proof status.

Edge cases checked for the new statement: an empty scheme gives a vacuous flatness
condition; rank-zero terms and the zero module remain flat; d = 0 is the usual flat
module resolved by a bounded-above free complex. Acyclic negative tails are allowed.
The point and neighbourhood hypotheses belong only to the final local-freeness
argument, not to the new flatness statement. No quasi-coherence assumption on C
was added. The construction of the actual complex is still Mathlib truncGE.

## No longer needed

Removed the direct import `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`
and the planned dependency `lem-weil-pbc-finite-projective-standard-free-cover`.
The proof also no longer needs that branch's
`Sheaf.RingTheory.FiniteProjectivePrimeLocalFree`
(node `lem-weil-pbc-finite-projective-prime-local-free`). Both are replaced by
`WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine`'s proved affine
criterion, already recorded as `lem-pc-affine-sections-finite-locally-free-criterion`.
They are pruned from this route; other users may still need them.

The old direct import `Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion` is moved
into the new flatness module. Its node is still needed for the remaining flatness
step and is not claimed as pruned. An experimental explicit import of
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels` was removed after confirming
that the source import already exposes the required cokernel API. No further
original dependency branch is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The two original dependency signatures are algebraic: neither directly states the
scheme-level flatness or the neighbourhood/truncation comparison. This was missing
Lean glue, not a false statement. The existing affine-sections finite-local-freeness
criterion supplies the second step without a separately imported standard cover.
The last comparison needs preservation of cokernels, rather than full exactness
of restriction.

LeanSearch returned Internal Server Error; the actual unsuccessful request is
recorded as unavailable in searches.jsonl. LeanFinder, Loogle, Mathlib source grep
and searches of both library roots were used. The unit record
`sk-thm-picard-coherence` has empty realized bindings; its route and statement were
not changed.

WANTED: local copies of Stacks more-algebra.tex (Tag 0653, label
lemma-last-one-flat) and algebra.tex (Tags 00NX and 00HT), for the new flatness node.
The assigned checkout lacks those source files. The current statements and proofs
of Tags 0653 and 00NX were checked directly on the Stacks website. The sheaf
application is recorded with proof_origin.by = agent.

## New nodes

`lem-pc-flat-model-opcycles-flat-zero`, in
`dag/nodes/sec-picard-framework/lem-pc-flat-model-opcycles-flat-zero.json`, states
flatness of Q.opcycles 0 over the identity. Its argument passes to stalks, uses the
bounded-above K-flat tensor comparison and the existing flat-opcycles criterion,
then returns to affine sections. It is strictly the flatness part of the parent:
finite presentation, local trivialization and transport to the canonical
truncation are proved in the parent. It inherits the parent's chapter and unit.
The three search kinds are recorded, with LeanSearch unavailable. No change record
is needed because no existing interface changed.

## Second reading by M1

1. **Interfaces: PASS.** Read both delivered modules and diffed the existing module
   against the repository version. The signature and docstring of
   `exists_local_finiteFree_truncation_zero` are byte-for-byte unchanged. All three
   existing public imports are unchanged; added proof imports are plain imports.
   The delivery changes no existing definition or statement and has no forced adaptations.
2. **Proof and axioms: PASS as a decomposition.** Independently compiled both files
   with `lcompile.py --all`. Scratch copies with `#print axioms` show only `propext`,
   `Classical.choice`, `Quot.sound` for both private helpers, and those axioms plus
   `sorryAx` for the parent and `isFlatOver_opcycles_zero_of_quasiIso`. The single new
   hole is exactly the named theorem reported above. No axiom declaration, unsafe,
   opaque, implemented_by, extern, or hollow definition is introduced. In particular,
   the presentation comes from an explicit cokernel construction; no arbitrary object
   is chosen from an unproved existence theorem.
3. **Split statement: PASS.** Its conclusion is only flatness of the actual opcycles;
   finite presentation, finite local freeness, the neighbourhood and rank, and the
   canonical-truncation comparison are proved in the parent. Read the sourced proof
   in words and checked [Stacks Tag 0653](https://stacks.math.columbia.edu/tag/0653)
   and [Tag 00HT](https://stacks.math.columbia.edu/tag/00HT). Fixing an affine V,
   the affine-pair hypothesis gives A-flat sections on every smaller affine W;
   their filtered colimit is the stalk, and localization transfers flatness to its
   stalk ring. Thus no quasi-coherence of C is silently needed. The finite-free
   Q terms make its opcycles quasi-coherent, enabling the converse affine argument.
   Checked the empty scheme, rank-zero terms, d = 0, and an unbounded negative
   acyclic tail. Independent LeanFinder and Loogle searches and rg searches of
   Mathlib and both library roots found no duplicate. The proved categorical
   `ObjectProperty.flat_opcycles_of_exactAt` is another algebraic substep, but
   does not supply this scheme-level quasi-isomorphism/stalk comparison. The
   affine connective-truncation and truncation-kernel lemmas have additional
   universal-vanishing or Tor-amplitude hypotheses, so do not directly close it.
4. **Route and pruning: PASS.** Checked the explicit finite presentation, equal-affine
   evaluation of IsFlatOver, and every isomorphism in the final composite. Pullback
   preserves cokernels; the proof does not assume preservation of kernels. The
   standard-free-cover branch is replaced by the proved affine finite-local-freeness
   criterion. The old Tor criterion remains needed in the split flatness argument
   and is explicitly not claimed pruned. FiniteDescent supplies the used affine
   finite-presentation theorem. All proof-only imports remain plain imports. Read
   `dag/units/sk-thm-picard-coherence.json`: its realized bindings are empty and its
   statement and route remain untouched. Closing the scheme flatness hole requires
   substantial stalk and tensor transport, not a short application of the searched
   declarations; no further hole was added during this reading.
5. **DAG: PASS after repair.** Matched the new Lean signature, docstring, source,
   chapter/unit, creation record, blueprint origin and searches to its node. Checked
   the parent's proof steps against the Lean reduction. The parent omitted the
   already existing node `lem-weil-pbc-finite-presentation-affine-sections` for its
   explicit use of `finitePresentation_sections_of_isFinitePresentation`; added
   it to step 2 and proof_deps. Added the independent Loogle localization search
   to the new node. No node statement or unit record was changed.

Second reading changed only DAG dependency/search bookkeeping and this report;
no Lean changes. Holes closed: one original hole. Holes added: one strictly smaller
flatness hole. This remains a one-to-one decomposition, with no net hole reduction
claimed and no claim of a sorry-free target proof.
