## What changed

Audited the queued upstream-review #1428 repair against the current source, DAG,
landed E4 change record, and both direct callers. The current module already has
its corrected statement and a complete proof. Simplified the proof's final stalk
transport to `rwa [hw] at hp` instead of rewriting hp and returning it.
No signature, visibility, docstring, definition, import, or proof route changed.
The initial module compiled cleanly in 2.7 seconds through lcompile.py.

## Proved and sorry left

Holes closed by B2: zero. Holes added: zero. The assigned module had zero sorries
at the start and has zero remaining.

AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core
(node lem-sbc-stalk-normalization-depth-two-section-flat-core) is already proved:
lift each source point over x to the test pullback, descend stalk flatness through
a flat local (hence faithfully flat) map, and restrict to the open finite-flat
target locus. Both imported proof dependencies have complete proofs in the
current source. The delivery axiom probe checks the compiled transitive proof.
This delivery is validation of an already landed repair, not new proof progress.

## No longer needed

None. Both proof-only imports are used: FiniteFlatTargetLocus supplies openness,
and WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic supplies
Module.Flat.of_flat_of_faithfullyFlat. The three public Mathlib imports supply the
Noetherian, finite, and flat vocabulary of the signature. No modules or nodes are
pruned. The unit route and current two-step DAG proof remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The brief says the module still contains sorry, but the checked-out source has
none. coord/repairs.txt still lists the old false normalization assertion from
upstream review #1428. The landed record
coord/changes/stalk-normalization-depth-two-section-flat-core.md already repairs
that assertion to the true descent-and-openness theorem with an explicit flat
pullback hypothesis. The current DAG agrees with that theorem and its proof.

The normalization caller GaloisCover.stalk_normalization_depth_two_section_flat
passes hZ (the rational generic-section point) to
GaloisCover.exists_stalk_normalization_split_formal_test, obtains a split formal
test, and uses its split-cover isomorphism to establish pullback flatness before
applying this core. Thus the old cone counterexample does not supply the current
flat-pullback hypothesis. The other caller, PuncturedLocalPurityFiniteFlatFiber,
obtains pullback flatness by identifying the pullback with a finite etale
extension. Depth two alone is not used to imply flatness in this core.

Edge cases: an empty source makes the fibre condition vacuous; x still lies in
the target locus. An empty test cannot satisfy the explicit point b hypothesis.
No surjectivity of t is assumed: the specified point b lifts every z over x via
the scheme pullback point-existence theorem. A locally Noetherian target need
not be quasi-compact, as the finite-flat target-locus theorem is local on it.

The separate literature unit file is absent from this clone. Read the stored
unit record sk-prop-input-spreading: the formal splitting calculation and final
flatness descent remain parts of its last step; its realized arrays are empty.
Searches through msearch.py (leanfinder and loogle) recovered the stalk-flatness
criterion and faithfully-flat APIs without an exact shorter scheme theorem;
rg in Mathlib and the project confirmed the existing source algebra descent
lemma. No new source-dependent statements or arbitrary witness definitions were
introduced. No forced adaptations are needed.


## Second reading by B2

1. Interface: PASS. Read the complete repository and sandbox modules and their
   unified diff. The sole change replaces `rw [hw] at hp; exact hp` with
   `rwa [hw] at hp`. The existing theorem signature, visibility, all imports,
   docstrings, and definitions are byte-for-byte unchanged. The earlier E4
   interface correction is already landed and is not part of this delivery.
2. Proof: PASS. Independently compiled the sandbox module through lcompile.py
   without errors or warnings (2.7 seconds). A scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`
   compiled in 2.5 seconds and reported exactly propext, Classical.choice, and
   Quot.sound: no sorryAx. Read every proof step: the equality hz.trans hb.symm
   supplies the common pullback image; pullback.condition gives the flat
   composite; the first projection is flat by base change and its stalk map is
   local, hence faithfully flat. The existing algebra descent theorem gives
   flatness of p's stalk, and hw transports it to z. Finally the restriction
   stalk isomorphism and Flat.of_stalkMap prove flatness over W. There is no
   sorry, forbidden declaration, or data chosen from an unproved theorem.
3. Split statements: PASS, vacuous. No new declaration, node, or hole is added.
   Read the two imported proofs, including the tensor-injectivity argument in
   Module.Flat.of_flat_of_faithfullyFlat and the finite closed-image argument in
   isOpen_setOf_finite_flat_stalks. Empty source gives the whole target locus;
   empty T cannot supply b. A globally surjective test is unnecessary because
   the specified b lifts each z over x. No strengthening is needed.
4. Route and pruning: PASS. Both proof-only imports are needed at their explicit
   applications; the public imports provide the signature's scheme properties.
   Searched project morphism modules for flat descent/base-change routes and
   Mathlib's scheme Flat module for composition/pullback descent: no shorter
   applicable scheme theorem was found. The proof already takes the existing
   algebra descent and finite target-locus route. No old proof dependency is
   removed. Read sk-prop-input-spreading's stored statement and seven steps:
   its final formal splitting and descent route is retained by the unchanged
   normalization caller. Its realized arrays are empty and are unchanged.
5. DAG: PASS. Read lem-sbc-stalk-normalization-depth-two-section-flat-core whole.
   Its Lean signature matches the locally Noetherian target, finite p, flat t,
   flat pullback, and specified point b over x. Step 1 uses
   lem-weil-pbc-flat-algebra-faithfully-flat-descent; step 2 uses
   lem-sbc-finite-flat-target-locus. These are exactly the recorded proof_deps,
   and the proof_origin describes the actual argument. No new-node checks or
   node edits are necessary.

Second reader changes: appended this independent review only; no further Lean
repair was needed. This delivery closes zero holes and adds zero holes. The
single theorem was already proved before the first worker's proof simplification.
