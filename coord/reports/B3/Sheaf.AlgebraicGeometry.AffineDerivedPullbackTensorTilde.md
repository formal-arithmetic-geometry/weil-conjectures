## What changed

Proved both open-restriction comparisons in
Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde.
All six existing public theorem signatures and all public imports are unchanged.

AlgebraicGeometry.derivedPullback_openRestriction_iso follows from composition of
left-derived tensor pullbacks and the identification of open pullback with exact
restriction. The private composition proof checks invertibility on K-flat resolutions
and transports it to every derived object. It uses only the supplied local derived
category instances, rather than assuming instances for every scheme.

AlgebraicGeometry.derivedTensor_openRestriction_iso uses the existing total-complex
comparison derivedPullback_tensorProduct and derived bifunctor comparison
derivedPullback_tensor_comparison_exists for U.ι. It then transports the comparison
through the proved open-pullback/exact-restriction isomorphism. Added their two modules
as proof-only imports, together with the left-derived uniqueness API.

Reworked the existing affine pullback natural comparison using the proved private
counitComparison and baseChangeCounitComparison helpers. Reworked affine object
transport using the proved private mapIso_trans_nonempty and tensorIso_trans_nonempty
helpers. These generic categorical proofs avoid repeatedly checking long concrete
whiskering and tensor expressions. No definition was changed and no proof was moved
into another file. Retained the original affine derived equivalence argument for
preservation of quasi-isomorphisms. Updated the existing DAG node to match this route.

## Proved and sorry left

Closed 2 of 2 original holes:
- AlgebraicGeometry.derivedPullback_openRestriction_iso.
- AlgebraicGeometry.derivedTensor_openRestriction_iso.

Both belong to lem-pc-affine-derived-pullback-tensor-tilde. Added no holes and no nodes.
There is no sorry left in the delivered module. The four already proved affine
comparison declarations remain proved, and every new private helper is proved.
These are proofs from existing library declarations, whose own remaining holes are
separate stage-3 items, rather than claims that the transitive closure is sorry-free.

The complete delivered module compiled without errors or warnings in 56.2 seconds
through lcompile.py. The required deliver3.py --no-push printed OK: the delivery compiles and passes
preflight except for the second reading, which the second reader writes. Nothing was
pushed. The first separate appended axiom probe exceeded 60 seconds. The final dry run
completed without that diagnostic and printed OK (commit 7b85fa35bf); local compilation,
the appended axiom probe and preflight therefore passed. The second reading remains
for the designated second reader.

## No longer needed

Sheaf.AlgebraicGeometry.TensorPullbackAdjunction is unnecessary: the proof uses
nonempty_tensorPullbackAdjunction from the already imported TensorPullback module.
Accordingly, lem-pc-module-pullback-adjunction is removed from the direct proof dependencies.

No original import is removed. The old direct proof dependency
`def-pc-tensor-complex-sheaves` is no longer directly invoked: tensor restriction now
uses `lem-pc-derived-pullback-tensor-product` and
`lem-pc-derived-pullback-tensor-comparison-descent`. The tensor-complex construction
remains a transitive dependency of those computations, so no module is claimed pruned.
The earlier attempt's proposed pruning of AffineQCohDerivedEquivalence is superseded:
the final proof retains its quasi-isomorphism transport. Its direct localization
exactness helper and the longer quasi-coherent-kernel helper are unnecessary in the
final proof, so neither is included. No unit-level statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The saved attempt closed only pullback restriction and its full file timed out.
Tensor restriction can use the existing derived pullback tensor-product and bifunctor
comparison declarations without a new intermediate statement; import-direction checks
confirm that neither new proof import creates a cycle.

The expensive affine comparison is repaired by proving its categorical composition
for generic functors and specializing it once. The affine object transport is similarly
proved generically. Profiling an isolated affine comparison showed kernel checking
fall from approximately 37 seconds for the previous concrete composition to about
11 seconds with generic helpers. The whole file, with both original holes closed,
then compiled within the mandatory 60-second limit. No limit, compiler option, tool,
or dependency definition was changed to evade the check. Diagnostic scratch files
are not part of the delivery.

Sources read: the existing node and dependency signatures, the unit record
sk-thm-picard-f-representable, and Stacks Tags 08DW and 08DX online because the referenced
literature/stacks-project/perfect.tex is absent on this machine. The tensor restriction
route is the specialization to an open inclusion of the library's Tag 079U argument.

## Earlier second reading (a previous round; superseded)

1. Compared the complete module with the repository baseline. All six existing
   public theorem signatures are byte-for-byte identical; the existing public imports,
   docstrings, options and definitions are unchanged. Only proofs, proved private
   helpers and three proof-only imports were added or revised. No change record is needed.
   Verdict: pass.
2. Read every proof and helper. The composition comparison is invertible on K-flat
   representatives and then on all derived objects by localization and naturality;
   open pullback is exact restriction by adjoint and derived-functor uniqueness.
   The tensor comparison transports the existing natural bifunctor isomorphism.
   Generic affine helpers only compose actual isomorphisms. No arbitrary witness is
   used to define new data, no hollow definition or forbidden declaration is added,
   and the file has no sorry. Independently compiled the file without errors or
   warnings in 57.8 seconds. Checked the six public declarations with an appended
   scratch axiom probe in 45.6 seconds: five use only propext, Classical.choice
   and Quot.sound; derivedTensor_openRestriction_iso additionally uses sorryAx
   through existing imported dependencies. No new hole is introduced. Verdict: pass.
3. No statements were split off, no holes or nodes were added. The private helpers
   are all proved, and the identity, empty-open, whole-open and zero-complex cases
   require no extra hypotheses: all comparisons are categorical isomorphisms.
   Verdict: pass.
4. Searched the sheaf and upstream algebraic-geometry libraries and Mathlib's
   derived-functor API for composition and restriction routes. The independent-
   universe restriction theorem imports this very module, so using it would create
   a cycle. The global composition theorem requires a family of derived-category
   instances for every scheme; the private proof correctly uses only the three
   supplied instances. The existing tensor comparison is the shorter available
   route and was used. Each proof-only import supplies a used declaration; all
   original imports remain needed. The unit record is unchanged (its realized
   statement and step lists are empty in the baseline); no unit route is bypassed.
   Verified the pruning of TensorPullbackAdjunction and the removed direct DAG dependency.
   Verdict: pass.
5. Compared node records: only proof, proof_deps and proof_origin changed. The
   proof_deps list is exactly the union of the recorded steps' uses and matches the
   Lean route, including the tensor comparison and open-pullback adjunction.
   There are no new nodes to validate. Verdict: pass.

The returned review identified one unused proof-only import. The repair removes
TensorPullbackAdjunction and its direct DAG dependency, since the proof uses
Scheme.Modules.nonempty_tensorPullbackAdjunction from TensorPullback through
DerivedPullback. The second-reading account records this verified pruning;
no theorem signature or proof body changed. The repaired module independently
compiled cleanly through lcompile.py in 44.6 seconds.

## Second reading by B3

1. Compared the delivered module with the read-only repository version, including
   each existing declaration's full signature. All six public theorem signatures
   are byte-for-byte identical. The diff adds proved private helpers and three
   proof-only imports, closes the two restriction proofs, and refactors affine
   proofs without changing their conclusions. Public imports, definitions,
   docstrings and options are unchanged. No change record is required. Pass.
2. Read all helpers and public proof bodies. Independently compiled the current
   module through lcompile.py: clean, 45.5 seconds. A scratch copy with #print axioms
   for all six public declarations compiled cleanly in 44.7 seconds. Five use only
   propext, Classical.choice and Quot.sound; derivedTensor_openRestriction_iso also
   uses sorryAx from existing imported proof dependencies. No sorry or forbidden
   declaration occurs in the delivered Lean file. The composition comparison uses
   K-flat resolutions only inside its proved proposition, and no new definition
   selects data from an unproved mere existence theorem. Pass.
3. No statement is split off, no new public statement or DAG node is introduced,
   and every private helper is proved. Checked the argument for empty and whole
   opens, identity morphisms, and zero complexes: it uses no nonemptiness, boundedness
   or flatness assumption beyond the original signatures. Counit invertibility,
   localization and functorial transport are valid in these cases as well. Pass.
4. Searched the repository's sheaf/upstream algebraic-geometry files and Mathlib's
   derived-functor API for composition, open restriction and uniqueness. The existing
   global composition result requires instances for every scheme, which the current
   signatures do not supply. The independent-universe restriction result imports
   this item. The related open-pullback helper is private and requires an additional
   derived-category instance. Thus none replaces the proved local helpers directly.
   Tensor restriction uses the existing total-complex and descent comparisons.
   All added imports supply used declarations; TensorPullbackAdjunction is already
   absent and nonempty_tensorPullbackAdjunction comes from TensorPullback. The report
   names the sole removed old direct proof dependency, def-pc-tensor-complex-sheaves,
   while retaining its transitive construction. No original import or module is
   pruned. The unit's realized record is unchanged (empty statement list and one
   empty step list), and the affine derived-equivalence route is retained. Pass.
5. Compared the existing node JSON with its baseline: only proof, proof_deps and
   proof_origin change. The dependency list equals the union of all step uses.
   Each step describes the actual Lean argument, including restriction via local
   composition and adjoint uniqueness, tensor descent, affine K-flat comparison,
   and quasi-isomorphism transport. No new-node fields require checking. Pass.

This second reading changed only this report by appending the independent review
and its current compiler/axiom evidence. No Lean or node repair was needed.
