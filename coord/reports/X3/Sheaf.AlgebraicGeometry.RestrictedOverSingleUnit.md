## What changed

Proved AlgebraicGeometry.Etale.restrictedOverSingle_unit without changing its
signature, docstring, or public imports. Eight proved private helpers express the
single-complex unit comparison, cancellation of the two inverse-image unit
comparisons, and their heterogeneous equality transports. The proof first
transports D₀.map_id to the identity in Over W. At that identity, the actual
pullback transition is the identity by its projections. The existing
upperStarComp_id_left and upperStarComp_id_right laws cancel the coefficient
comparisons, and naturality at singleObjXSelf identifies the degree-zero
single-complex comparison. The final equality restores the specified
restrictedOverDiagram.map_id transport by proof irrelevance.

Change record: coord/changes/restricted-over-single-unit-local-transparency.md.
The static checker classifies the local irreducibility command as an interface
change; the record lists all downstream users and explains that nothing is exported.
No downstream adaptation is required.

The existing DAG proof route and proof dependencies already describe this
calculation; no node changes or new imports are necessary. The source imports
already expose the proved inverse-image coherence lemmas used here.

## Proved and sorry left

Closed: AlgebraicGeometry.Etale.restrictedOverSingle_unit
(node lem-sbc-restricted-over-single-unit), the module's sole sorry.
Added: none. Remaining in the delivered module: none.
All eight private helper theorems are proved. This is a proof, not a decomposition.

## No longer needed

None. The sole public import Sheaf.AlgebraicGeometry.RestrictedOverSingleData
is required by the unchanged statement and its definitions. No planned node or
module is bypassed, and no proof-only import was added.

## Where the brief, the DAG or earlier work was wrong

The previous attempt was blocked by the unpublished RestrictedOverSingleData
object file. The server's published build now contains it; the baseline and the
complete proof compile there through lcompile.py. Direct rewriting of D₀.map_id
fails because the map occurs in the source type as well as in the equality
transport. Heterogeneous equality handles this dependence without changing the
statement. Expanding the whole diagram functor was unnecessary; the completed
proof uses its map_id law directly. The kernel check of the explicit comparison
construction is relatively expensive (the successful compile took 51.8 seconds).
The proof also covers empty schemes, zero sheaves, and identity structure maps:
no nonemptiness, injectivity, or cofilteredness hypothesis was introduced.

## Second reading by X3

1. Interface: compared the complete delivered module with the repository module
   using diff, and compared the existing theorem signature byte for byte. The
   statement, universes, hypotheses, docstring and sole public import are identical.
   No definition is changed. The local irreducibility setting is recorded in the
   change record; it is not an exported attribute. Verdict: pass.
2. Proof: read all eight private helpers and the public proof. The coefficient
   cancellation uses upperStarComp_id_left and upperStarComp_id_right from the
   upstream Etale.UpperLowerStar.Coherence module, already imported through
   RestrictedOverSingleData and RawAffineRestrictedCohomology. The HEq helpers
   eliminate actual equalities, not assumed equalities of unrelated morphisms.
   The pullback identity follows from both projections, and single_unit follows
   from degree-zero naturality after cancelling singleObjXSelf.hom. No forbidden
   declaration or sorry appears in the delivered module. Compilation and the
   full delivery axiom probe passed in the required deliver3.py dry run.
   Verdict: pass.
3. Split statements: none were added; all private helpers are proved. Checked
   identity maps, the zero sheaf, and empty schemes: the proof uses no extra
   nonemptiness or finiteness assumption. An empty I has no i to supply, exactly
   as in the original statement. Independent Loogle search for
   HomologicalComplex.singleMapHomologicalComplex returned a newer generic
   natural-transformation compatibility lemma, but rg of the pinned Mathlib and
   upstream sources confirms that it is absent here. Existing pinned component
   lemmas support the short degree-zero proof. Verdict: pass.
4. Route and pruning: read RestrictedOverSingleData, the raw coefficient
   construction, and the upstream unit laws. The sole import is necessary for
   the unchanged signature. The old proof dependency
   lem-weil-pbc-inverse-image-composition remains used, so No longer needed is
   complete. Read dag/units/sk-lem-failure-field.json: its realized statement and
   step lists are empty, and this local unit calculation changes no unit route.
   Verdict: pass.
5. Nodes: read lem-sbc-restricted-over-single-unit.json and its inverse-image
   composition dependency. The existing proof describes the same projection,
   coefficient, single-complex and equality-transport calculation; proof_deps and
   proof_origin remain accurate. There are no new nodes. Verdict: pass.

Changed the change record's Users table from a single row containing the whole
closure to one row per module, and checked holders against the local claim files.
Compiler experiments and the final verdict are recorded below; no experimental
Lean changes were accepted into the delivered module set.

Compiler verdict for point 2: PASS after the required delivery dry run. Earlier
standalone attempts exceeded lcompile.py's fixed 60-second limit, both locally
and on its normal server fallback, including the first scratch axiom check.
The subsequent deliver3.py --no-push run printed OK at commit 294118e6c2:
the original complete module compiled, the full axiom probe passed, and the
preflight passed. No proof or definition was changed to obtain that success.
The earlier timeouts are retained here as evidence of sensitivity to compile
conditions, rather than represented as a failed final validation.

Read the kernel profiler and unfolding counters from scratch checks of the
original helper groups and target calculation. The seven lower helpers compile
in about 9 seconds; adding restricted_identity_heq takes about 32 seconds.
A diagnostic scratch copy with that helper's body temporarily replaced by sorry
isolates roughly 39 seconds of kernel checking in the public target's transport.
Kernel diagnostics show repeated expansion of pullback.map, rawAffineRestrictedMap,
identity scheme morphisms and equality recursors in that transport, and concrete
AddCommGrpCat structure expansion in the identity calculation. These scratch
copies are outside lean/ and are not delivery files or new holes.

Tried proof-only reductions in scratch: direct coefficient cancellation from
D₀.map_id and restrictedOverDiagram.map_id, a general transported single-complex
comparison, combining the identity calculation into the target, explicit hom
unfolding, aligning the scheme objects, and a general family transport theorem.
Every complete experimental version exceeded 60 seconds. No statement, definition,
import or node was changed to make compilation easier, and the compile limit
was not increased. No experimental proof replaces the first worker's proof.
The successful dry run validates the original proof. The second reading changes
only this report and the Users table in the existing change record; it accepts
none of the experimental Lean rewrites. No imports or modules are pruned.

Final validation: deliver3.py --no-push passed twice, at 294118e6c2 and
2899eee45c, with the unchanged first-worker Lean proof and the corrected Users
table. The delivery probe calls Lean.collectAxioms on the public theorem and
reports forbidden axioms; both checks passed. Separate #print axioms scratch
copies, including one with the delivery probe appended, still hit the 60-second
limit, so an explicit printed axiom list is not claimed. A trial that renamed
private helpers also timed out and was not accepted. The normal module's compile
cost remains a material limitation for the maintainer's global build to verify.
