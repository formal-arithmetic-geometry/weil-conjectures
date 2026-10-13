## What changed

Proved AlgebraicGeometry.exists_derivedDirectImage_internalHom_comparison in
Sheaf.AlgebraicGeometry.DerivedDirectImageInternalHom without changing its signature.
Two proved private categorical helpers construct tensor-Hom adjunctions and the
natural evaluation mate. The returned duplicate internalHomMate_exists is replaced
by internalHomMate_of_tensorComparison, genuinely generalized to accept any natural
transformation from tensor D ⋙ F to F.prod F ⋙ tensor C, without invertibility.
The scheme application supplies t.hom. GlobalHomAdjunctionIso only provides the
isomorphism-based private helper, and importing it would create a cycle; verified
with tools/import_direction.py. No downstream module is adapted.
The scheme witnesses come from DerivedAdjoint, CanonicalDerivedTensorHom, and
DerivedPullbackMonoidalModel. The inverse tensorators of the monoidal model form
the required tensor comparison, with naturality proved by cancellation.
Updated the existing node's proof route and dependencies. No public imports changed.
The static check of new top-level proof-context commands requires a change record:
coord/changes/DerivedDirectImageInternalHomProofContext.md. It documents the
unchanged exported signature and no effect on importers; no adaptations are made.

## Proved and sorry left

Closed: AlgebraicGeometry.exists_derivedDirectImage_internalHom_comparison
(node lem-pc-sheaf-rhom-projection-formula), the module's only original sorry.
Added holes: none. Remaining holes in the delivered module: none.
The proof uses the library's existing canonical-data existence results; this does
not assert that all their transitive dependencies are sorry-free.
Both private helpers are proved. No new theorem or definition contains sorry. The generalized private mate theorem
uses only naturality of the tensor comparison; its inverse is never used.

## No longer needed

Removed direct proof imports:
- Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction
  (lem-sc-derived-internal-hom-adjunction): canonical natural equivalences supply
  precisely the tensor-Hom data needed here; tensor symmetry is unnecessary.
- Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct
  (lem-pc-derived-pullback-tensor-product): use the already stated canonical
  monoidal model. The tensor-product theorem remains a transitive dependency of
  that model, so this is removal of a direct proof edge, not global pruning.
- Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
  (lem-pc-ringed-spaces-derived-adjoint-general): the existing scheme adjunction
  already applies to the exact chosen scheme functors.

No claim is made that these modules disappear from every other target's closure.

## Where the brief, the DAG or earlier work was wrong

The original plan's tensor-Hom declaration supplies natural equivalences rather
than the actual adjunction witnesses in this signature; Adjunction.mkOfHomEquiv
constructs those witnesses. The general ringed-space adjunction only existentially
supplies a left-derived functor, while DerivedAdjoint states the adjunction for the
chosen derivedPullback. DerivedPullbackTensorProduct is formulated on K-flat
representatives, while DerivedPullbackMonoidalModel supplies the actual tensorators
for the shared derived tensor. These are interface mismatches, not mathematical
errors, and are resolved using existing declarations with no signature changes.

Repair of return X-b3441: the first delivery duplicated the isomorphism-based
private internalHomMate_exists in GlobalHomAdjunctionIso. This was not acceptable
merely because it was private. The helper now proves the stronger result for a
possibly noninvertible tensor comparison, under the distinct name
internalHomMate_of_tensorComparison. This is a change of hypotheses, not a rename
of the same statement. The original public theorem and its full mate equation
are unchanged. tools/import_prune_check.py is rerun explicitly in addition to
the required dry run.

The local Stacks TeX file is unavailable. No new mathematical assertion is left
unproved; the categorical argument is reused from the library's proved helpers.
Mathlib searches run: LeanFinder for internal-Hom comparison of a tensor-preserving
left adjoint, Loogle for Adjunction.mkOfHomEquiv, and grep for internal-Hom
comparison/adjunction. The search results are generic/category-theoretic; no exact
scheme comparison theorem was found. The blueprint unit's realized lists are
empty, and its route and statement were not changed.

Validation: single-file lcompile.py compilation, including the unchanged full
mate equation. The second reading restored the existing theorem docstring; the
updated implementation route is recorded here and in the DAG. A scoped heartbeat allowance is used for scheme witness
elaboration; the file compiles below the 60-second limit.


## Second reading by Y3

1. **Interface comparison: pass.** Read the repository and sandbox modules in full
   and compared them with `diff -u`. Extracted the existing theorem from its name
   through `:= by` and checked byte-for-byte equality. The morphism f remains
   arbitrary, both HasDerivedCategory assumptions and universes are unchanged,
   and all five existential witnesses and the mate equation for every L, M, A,
   alpha remain identical. All four public imports are unchanged. No downstream
   module is delivered or adapted. The proof-context change record covers the
   local options and section variables; it had stale helper names and the old
   isomorphism binder, which I corrected. Restored the existing theorem docstring.

2. **Proof and axioms: pass with existing open dependencies.** Compiled the
   delivered module using lcompile.py with no warnings or errors (26 seconds).
   Refreshed a scratch copy from the actual delivered source and printed axioms
   of internalHomMate_of_tensorComparison, tensorAdjunctionCore, and
   exists_derivedDirectImage_internalHom_comparison. Both private helpers use only
   propext, Classical.choice, Quot.sound; the public theorem additionally uses
   sorryAx through the existing imported results. No local sorry, axiom, unsafe,
   opaque, implemented_by, extern, or kernel-check bypass occurs. The private
   CoreHomEquiv definition explicitly constructs its equivalence and both
   naturality proofs. The comparison components are explicitly transposes of
   evaluation; no data definition is filled from an arbitrary existence witness.
   The chosen tensor-Hom family has the representative characterization and
   IsCanonicalDerivedTensorHom.unique. The adjunction and monoidal model are
   eliminated inside this existential theorem rather than exported as definitions.

3. **Split statements and mathematical reading: pass; none split off.** No new
   public statement, node, or hole is added. In the generic helper, checked the
   variance b:L'->L, d:M->M', and the pullback counit direction F(R(L))->L.
   The mate law first specializes at identity and then transports along alpha
   using ex/ey naturality and adjunction naturality. Injectivity of ey reduces
   the two-variable naturality square to t naturality and counit naturality.
   The generalized tensor comparison is genuinely a NatTrans, with no inverse
   hypothesis; identity functors recover the usual evaluation transpose, and a
   zero comparison in additive examples gives the zero mate. Empty categories
   introduce no extra existence requirement because the component family is empty.
   The scheme application uses the inverse monoidal tensorators in the required
   F(A tensor B)->F(A) tensor F(B) direction. Both tensor-Hom adjunctions use the
   inverse of the pinned equivalences, so their homEquiv inverses reduce to ex/ey
   exactly as the original displayed equation requires.

4. **Shortest route, imports, and unit: pass.** Ran independent LeanFinder,
   Loogle and Mathlib grep searches with queries recorded in searches.jsonl.
   LeanFinder found closed-category adjunction APIs, not this bifunctorial mate
   equation; Loogle did not recognize the abbreviated CoreHomEquiv name. Read
   Mathlib Adjunction/Mates.lean: mateEquiv handles a fixed square but does not
   directly supply this complete two-variable statement for arbitrary H and J.
   Searched lean/Sheaf, lean/WeilConjectures and the upstream source. The closest
   helper is GlobalHomAdjunctionIso's private isomorphism-based theorem; it is
   inaccessible and its module depends on this item. The small CoreHomEquiv
   adapter applies Mathlib's constructor to the three-variable naturality law.
   The three replacement proof imports are each used for an actual witness.
   Every old proof dependency is listed under No longer needed. These are direct
   edges removed, not claims of whole-target-closure pruning. Reran
   tools/import_prune_check.py against the repository original and delivery: exit
   zero, including the duplicate-theorem check that refused return X-b3441. Read
   dag/units/sk-thm-picard-duality.json: realized.statement and the sole step's
   realization are empty. The unit statement and route are unchanged; this proof
   still constructs the same internal-Hom arrow used in the sheafy trace route.

5. **DAG agreement: pass after repair.** Compared the node JSON with the
   repository. Only proof, proof_deps and proof_origin differ. Read the three
   replacement dependency interfaces and their nodes: DerivedAdjoint supplies
   exactly a; CanonicalDerivedTensorHom supplies ex/ey and their naturality;
   DerivedPullbackMonoidalModel supplies m and its tensorators. The proof_deps
   list is exactly the union of the three steps' uses. Changed the third step's
   elementary flag to false: the mate/naturality argument is substantial and is
   fully proved in the module, not a two-line consequence. No new-node fields or
   statement-change record is required, because no new hole or exported statement
   has been introduced.

Changes made in this second reading: restored the existing theorem docstring;
corrected the change record to name internalHomMate_of_tensorComparison and its
NatTrans hypothesis; corrected the DAG elementary flag; refreshed the scratch
axiom checks and added this review. The Lean proof itself required no repair.
Closed hole: AlgebraicGeometry.exists_derivedDirectImage_internalHom_comparison.
Added holes: none. This is one local hole closed, not a decomposition.
