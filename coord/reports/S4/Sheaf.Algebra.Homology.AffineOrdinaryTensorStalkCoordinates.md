## What changed

Proved `AlgebraicGeometry.exists_affineOrdinaryTensorStalkCoordinates` in
`Sheaf.Algebra.Homology.AffineOrdinaryTensorStalkCoordinates`. Constructed the chain
isomorphism as the stalk of the inverse tensor-pullback/tilde comparison followed
by the inverse `tensorStalkIso`. Its germ formula follows from the two specified
unit equations and scalar-map transport. Its cohomology formula follows from
`affineRepresentativeStalkIso_naturality` and functoriality of homology.

Added only proved private helpers for scalar transport, evaluation of mapped
isomorphisms, stalk germ naturality, degreewise inverse cancellation, and evaluation
of the existing localization construction. Pinned the pullback functor to the
underlying sheaf-module categories and evaluated its three comparison factors
with a generic categorical identity, avoiding expensive affine reassociation.
Existing signatures, definitions and
visibility are unchanged. Imports are unchanged. Updated the node's proof and
proof origin to describe the formal argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_affineOrdinaryTensorStalkCoordinates`
(node `lem-pc-affine-ordinary-tensor-stalk-coordinates`).
No holes remain in this module; no new holes or modules were added.
The proof uses existing library interfaces, including their stated properties.

## No longer needed

No imports, nodes or modules are pruned. The pure-tensor generation/uniqueness
argument mentioned in the old proof plan is unnecessary: the explicitly constructed
chain isomorphism already has the required action. The coordinate theorem
`affineTensorPullbackHomologyStalkIso_coordinates` is not used; its module remains
necessary for the definition `affineTensorPullbackHomologyStalkIso`.

## Where the brief, the DAG or earlier work was wrong

The saved attempt timed out because it left the pullback category implicit and
reassociated the affine comparison directly. Explicit category types and a
generic three-isomorphism evaluation lemma remove that bottleneck. No incorrect
statement or interface was found. The unit's route is preserved
(the unit record has no realized statement or step attached to this node).
The proof requires explicitly regrouping the three isomorphisms in the target
coordinate: Lean's isomorphism-composition notation associates to the right.

## Earlier second reading (a previous round; superseded)

1. **Visible changes and signatures.** Compared the delivered module with the repository version. All existing declarations, definitions, theorem statements, and visibility are byte for byte unchanged; the additions are private proof helpers and the proof of `AlgebraicGeometry.exists_affineOrdinaryTensorStalkCoordinates`.

2. **Proof and axioms.** Compiled the module through `lcompile.py`. It contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and no definition contains a hole. The target's axiom print contains only the permitted foundational axioms plus `sorryAx` inherited from still-open imported declarations.

3. **Statements and split-offs.** The original target is the only theorem closed; no statements were split off and no new nodes or holes were added. The private helper lemmas are elementary proof facts and do not alter the public interface. The construction handles the stated edge cases (including zero complexes and identity maps) through the existing categorical isomorphisms.

4. **Shortest route and pruning.** The proof uses the existing tensor-pullback/tilde comparison, stalk comparison, localization construction, and affine representative naturality. It avoids the old pure-tensor generation argument and does not use the coordinate theorem as a proof lemma. The public import remains necessary for the target definitions and no removable import or proof dependency was found.

5. **DAG and unit route.** The node's statement, proof steps, proof dependencies, and proof origin agree with the Lean proof. The unit record has no realized statement or step attached to this node, so its route is preserved. No change record is required.

**Changed:** Added this second-reading report only; no Lean source, declaration, node, or import was changed during review.

## Second reading by S4

1. **Visible interface:** Read the full module and its repository diff. The existing
   definition body, declaration signatures, docstrings and visibility are unchanged.
   The declaration comparison also reports no statement change. Only proved private
   helpers, the target proof and a theorem-local heartbeat option were added. No
   change record or consumer adaptation is needed.
2. **Proof:** The launcher delivery compile, including its all-declaration axiom
   probe, passed with no errors, warnings or forbidden axioms. The delivered source
   has no sorry or forbidden declaration mechanism. Two separate local checks hit
   the 60-second wall limit; the delivery compile passed at that same limit, so the
   timeout is intermittent. No timeout limit was raised. The target constructs tau
   explicitly as the mapped inverse comparison followed by tensorStalkIso inverse;
   its germ equation uses the specified unit/germ identities and scalar transport,
   and its homology equation uses naturality and homologyMap_comp.
3. **Split-offs and edge cases:** No new public statements, nodes or holes were
   added. Each private helper is proved by equality transport, functoriality, germ
   naturality or isomorphism cancellation. These identities also hold for zero
   elements and complexes and identity maps; a zero ring contributes no prime p.
   The chosen comparison isomorphisms have specified unit/germ equations, and the
   chosen tensorStalkIso has specified degreewise components. No arbitrary witness
   of an unproved mere existence statement is introduced. Searched ModuleCat and
   homology sources and related Sheaf modules: the proof already reuses the relevant
   germ naturality and categorical identities; no exact shorter target proof was
   found. There is no split-off statement needing an additional search or node.
4. **Route and pruning:** The sole public import is required by the target's use of
   affineTensorPullbackHomologyStalkIso. The proof uses the existing pullback/tilde,
   pullback/stalk, localization and representative homology interfaces. All old
   proof dependencies remain used, either directly or by the retained constructions;
   the unused coordinate theorem shares its node/module with a required definition.
   The report correctly records no pruned node or module. The unit's realized
   statement and step arrays are empty, so no realized unit step is bypassed.
5. **DAG:** Read the node, its dependency declarations and the unit. Only proof and
   proof_origin differ from the repository node. The proof steps describe the actual
   construction, germ calculation and homology square, and proof_deps equals the
   union of their uses. No new-node fields or statement changes are needed.

**Changed during this reading:** Added this review section only. The mathematical
proof, imports, public interface and DAG already agree and were left unchanged.
