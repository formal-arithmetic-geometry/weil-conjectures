## What changed

Proved `AlgebraicGeometry.exists_canonical_from_model` by identifying the model's
module functor with tensorPullback, comparing the two left-derived counits, and
conjugating the inverse model tensorator. Its degreewise equation follows from
the pinned module tensorator; its coordinate equation follows from counit
factorization, naturality, tensor composition and cancellation. Naturality is
Mathlib's monoidal transport.

To resolve the repeated complete-file timeouts, the three existing definitions
`pullbackTensorTotal`, `pullbackTensorModelMap`, and
`IsCanonicalPullbackTensorComparison` reuse existing named tensor instances.
All three are definitionally equal to their previous versions: the scratch
`DefinitionEqualityAudit.lean` compiled all three equality checks by
`with_unfolding_all rfl` against the original compiled module in 28.6 seconds.
All signatures, universes, visibility and target statements stay identical.
The definition-change record, including all 511 users and current holders, is
`coord/changes/canonical-pullback-tensor-instance-sharing.md`.
No other existing module is adapted.

Added six proved private helpers within this module: localizationTensor_isIso,
tensorTransport_equation, quotient_kFlat_of_acyclic, tensorTransport_natural,
counitTransfer_isIso, and sharedCounit_leftDerived. Existing private counit and
localization-map proofs use these helpers to avoid repeatedly constructing
large specialized proof terms. This is not a split of the module.
Updated both existing DAG nodes to match the completed transport proof and
its direct dependencies. No new module or node was created.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.exists_canonical_from_model`
(node `def-pc-derived-pullback-tensor-comparison-model-transport`).
Added zero holes. Every private helper is proved; no sorry remains in the item.
The existing existence assembly and canonical uniqueness proofs are retained.
Dependencies are used as recorded in the DAG; this delivery does not claim
axiom elimination for the entire target closure.

The complete optimized module compiled without warnings in the scratch
full-module check (49.5 seconds) and in the item's required lcompile check
(54.4 seconds).
The definition-equality audit also compiled without warnings.
The required delivery dry run returned exit code 0 and printed:
`OK (dry run): commit 336e547537 compiles and passes the preflight except for
 the second reading, which the second reader writes; nothing pushed.`
The final pruned module passed the compile and axiom probe in that dry run.
The independent second reading remains the next worker's task; it is not
written by this worker.

## No longer needed

Removed `import Sheaf.Algebra.Homology.KFlatResolution` and the direct
`lem-pc-kflat-resolution` proof dependency of the canonical-comparison node.
The proof uses `SingleComplexBaseChange.nonempty_coordinates`, whose own proof
still uses K-flat resolutions. Thus the resolution module remains transitively
needed; no claim of removing it from the entire target closure is made.
No other planned module, node or import is pruned. The unit's realized lists
are empty; the existing coordinate route is preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had a correct isolated transport proof, but its complete
module and the original baseline exceeded the 60-second limit. Merely retrying
those versions did not validate a delivery. Reusing the already recorded named
tensor instances, and proved generic helpers, gives a complete compiling module.
No tool, timeout or check was changed or bypassed. Profiling was confined to
scratch files; no debug option or profiling command enters the delivery.
No false statement or changed target meaning was found. The node text that
called the transport unformalized is updated to the completed Lean argument.

## Second reading by U2

1. **Interfaces and meaning: pass.** Read the complete repository and delivered
   modules and their diff. All eight existing declaration signatures, including
   the two existing private signatures, are byte-for-byte unchanged; the six new
   declarations are private proved helpers. Only the three definition bodies
   named in `coord/changes/canonical-pullback-tensor-instance-sharing.md` change.
   Verified that the optimized bodies in `DefinitionEqualityAudit.lean` exactly
   match the delivery after renaming, then independently compiled its three
   `with_unfolding_all rfl` checks against the original compiled module (22.9 s).
   Thus the total complex, localization tensor map and canonical predicate are
   definitionally unchanged. No target statement, public visibility or other
   module changes. The change record contains all 510 recorded downstream users
   and the item (511 rows); conversion preserves their meaning without adaptations.

2. **Kernel proof: pass.** Independently compiled the complete delivered module
   with lcompile (49.7 s), with no errors or warnings. No sorry, axiom, unsafe,
   opaque, implemented_by, extern or disabled kernel check occurs in the file;
   no line exceeds 100 characters. A scratch full-module copy with `#print axioms`
   for all fourteen declarations compiled in 55.2 s when run alone. Every
   declaration, including `exists_canonical_from_model`, the six new helpers and
   canonical uniqueness, uses only propext, Classical.choice and Quot.sound,
   except `exists_canonicalPullbackTensorComparison`, which additionally uses
   sorryAx through the still-open upstream monoidal-model existence proof. An
   earlier scratch axiom run timed out; its successful isolated rerun is the
   evidence used here. No data definition or arbitrary witness is added: τ and
   the chain isomorphism are witnesses inside a proved existence theorem.

3. **Split statements: pass; none added.** The delivery closes the existing hole
   `AlgebraicGeometry.exists_canonical_from_model` and introduces zero holes,
   zero public intermediate statements and zero nodes. Read each proved private
   helper: the tensor equation cancels the natural automorphism and tensorator;
   K-flatness uses acyclic preservation and the braiding; counit invertibility
   transfers along the unique left-derived comparison. None excludes zero
   complexes or identity morphisms. There is no restatement with a new sorry.

4. **Route and pruning: pass.** The proof first uses Mathlib functor
   extensionality, leftDerivedUnique/leftDerivedNatTrans_app, cancellation and
   monoidal transport; it then substitutes the actual model equations. Checked
   hμ pins the module tensorator, hφ supplies every summand equation, and heq
   supplies the coordinate equation for all K-flat P,N. The δ inverse on the
   tensor input and δ hom on the outputs have the correct orientation.
   Independent LeanFinder search for transported oplax naturality returned
   transport_δ and OplaxMonoidal.δ_natural, already used by the proof. Loogle's
   public index did not recognize the transport identifier; local Mathlib and
   lean/Sheaf searches confirmed the existing components and no shorter exact
   scheme-specific theorem. All remaining direct imports provide signatures,
   definitions or the K-flat pullback proof; no proof-only public import was
   added. The sole removed old proof dependency is lem-pc-kflat-resolution,
   fully listed under No longer needed with its direct module import. It remains
   transitively needed through nonempty_coordinates. Read the unit record
   sk-thm-picard-semicon: its realized statement and step lists are empty; the
   existing K-flat coordinate route and unit statement remain untouched.

5. **DAG agreement: pass.** Read both complete node records and their diffs.
   Only proof, proof_deps and proof_origin change. Each proof_deps list equals
   the union of its proof steps' uses. The transport node records functor
   identification, counit comparison, conjugation, degreewise pinning and
   naturality; the canonical-comparison node records existence assembly and
   the retained uniqueness argument. These match the Lean proof. Existing
   statement, source, unit, chapter and lean signature records are unchanged;
   there are no new-node field obligations.

Second reading changed only this report: added the independent review and its
compile, conversion and axiom evidence. No Lean, node or change-record repair
was needed. Holes closed: exists_canonical_from_model (one). Holes added: none.
