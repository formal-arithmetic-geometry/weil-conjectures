## What changed

Completed `WeilConjectures.limit_tower_over_local_system` with its original signature.
The proof applies single-ring descent to the prescribed R-system and the concrete
cokernel of the empty matrix over S. It applies small-universe single-ring descent
to the resulting S-system, supplied S′/S presentation, and matrix presenting M.
Essential finite type composition makes the middle stages essentially of finite
type over Z. Two directed upper tails, their final inclusion functors and composite,
natural structure maps, colimit restrictions and tensor restrictions are assembled
in Lean. The prescribed base diagram and cocone are retained definitionally.

Added `Sheaf.RingTheory.LimitModuleSmallOverSystem`, containing the named construction
obligation `RingHom.exists_limit_module_small_over_system`. It descends one algebra
and module in the independent module universe, using countability and Shrink; it
is strictly a part of the two-algebra tower argument. The tower imports this module
and `LimitModuleEssentiallyFinitePresentationOverSystem` for its proof. The unused
proof import of the latter in the wholly sorry small-universe module was removed.

This repair takes the reviewer's alternative of rebasing after the complete F2
repair landed. The actual landing is `20261014T020509-L-3810807`, reviewed by X-66eb4,
recorded in the existing descent node's `reviewed_proof` and the ledger at 02:05 on
2026-10-14. The landed repair removes the false arbitrary-D core and wrapper. Its
existing joint descent theorem now applies the ring localization construction,
then constructs matrix cokernels on an existential later tail, and finally restricts
ring data by finality. Its signature and visibility are unchanged.

The sandbox includes exact copies of all four landed dependency modules and their
matching nodes for compilation of the complete repaired set. They are unchanged
from the rebased repository and introduce no adaptation or interface change here.
The earlier proposed `LimitModuleRingDataWithBaseChange`, its node, the stale core
and wrapper changes, and their change record are removed from the delivery set.
This avoids replacing or duplicating F2's landed correction. Reports are synchronized
at report.md and coord/reports/P2/Sheaf.Paper.LimitTowerOverLocalSystem.md.

## Proved and sorry left

Closed the item's one hole, `WeilConjectures.limit_tower_over_local_system`
(`lem-weil-pbc-limit-tower-over-local-system`), by a complete Lean assembly proof.
No sorry remains in the item's module. Added one hole:
`RingHom.exists_limit_module_small_over_system`
(`lem-weil-pbc-limit-module-small-over-system`) in
`Sheaf.RingTheory.LimitModuleSmallOverSystem`.
This is a decomposition, one upper hole closed and one smaller hole added; it is
not claimed as a proof from only the three permitted final axioms.

The earlier added ring-only hole `RingHom.exists_limit_module_ring_data_with_base_change`
(`lem-weil-pbc-limit-ring-data-with-base-change`) is withdrawn on this rebase.
The corrected dependency modules retain two already-landed holes, not added here:
`RingHom.exists_limit_module_localization_ring_data`
(`lem-limit-module-localization-ring-data`) in
`Sheaf.RingTheory.LimitModuleLocalizationRingData`, and
`RingHom.exists_limit_module_presentation_cokernel_data`
(`lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module-data`)
in `Sheaf.RingTheory.LimitModuleModuleDataConstruction`.
The copied `LimitModuleModuleData` has no sorry: its colimit-only theorem and least-tail
helper remain proved. Both false interfaces stay retired, not counted as proofs.

## No longer needed

Removed `import Sheaf.RingTheory.LimitModuleEssentiallyFinitePresentationOverSystem`
from `Sheaf.RingTheory.LimitModuleSmallOverSystem`. Its body is wholly sorry; the
existing descent is used only in its natural-language proof plan. Its node retains
that planned proof dependency for the next worker.

With the complete F2 repair landed, the proposed module
`Sheaf.RingTheory.LimitModuleRingDataWithBaseChange` and node
`lem-weil-pbc-limit-ring-data-with-base-change` are not needed and are withdrawn.
The tower uses the existing joint descent, whose ring construction already supplies
these comparisons. The stale core/wrapper and caller alterations from the previous
packet are likewise withdrawn; exact landed sources replace them for validation.
The retired core and wrapper nodes are not independent proof steps anymore, as the
landed F2 records explain. No unit statement or realized step is bypassed; colimit
restriction is implemented by Mathlib's final-functor API. No claim is made that a
still-reachable library module has left the targets' closure.

## Where the brief, the DAG or earlier work was wrong

E2/G1: The constant nonzero field example with D(0)=0, D(n)=K for n≥1,
s=0 and t=1 refutes the arbitrary-D core. F2's complete landed repair retires that
interface and constructs modules from the matrix on a later tail of a supplied
ring colimit. This packet rebases on that complete correction rather than claiming
validation against a hypothetical corrected compiled dependency.

C4: The previous packet's caller node described a proof absent from its source set.
The rebased caller and its matching node now both use
`exists_limit_module_localization_ring_data`, followed by
`exists_limit_module_presentation_cokernel_data` and final restriction. Both complete
landed source modules are present in the sandbox and compiled with the tower.
The unused proposed ring-only split is withdrawn because this landed construction
already provides its content.

H9: Removed the specified unused import in the small-universe module and compiled
without it. F2/F3: Replaced both stale reports, corrected import ownership, reduced
the added-hole list to the actual remaining hole after rebase, and replaced the
unsupported dependency-validation claim with the actual landed repair above.
The second-reading section below checks the complete rebased set, not the previous
three-file packet.

The existing descent has additive stages in universe max u v, whereas the tower
requires universe v. The remaining single-algebra obligation isolates that mismatch
under the available essential finite type integer-base hypothesis. The finite-type
module-diagram theorem does not preserve the supplied matrix dimensions and assumes
finite type rather than essential finite type. Searches and the full countability,
ULift and Shrink proof plan remain recorded in the small-universe node/docstring.

## Forced adaptations

None in this rebased delivery: every copied dependency source is byte-for-byte equal
to the landed repository source. C4's forced caller adaptation was already included
in F2 landing `20261014T020509-L-3810807`. Its report records the original error at
line 152:4, `error(lean.unknownIdentifier): Unknown identifier
exists_limit_module_module_data`, against the corrected dependency, and the necessary
replacement proof imports and ring/module/final-tail assembly. This packet does not
resubmit or claim a new adaptation of a currently compiling caller.

## New nodes

`lem-weil-pbc-limit-module-small-over-system` records one-algebra descent with additive
stages in the independent universe of N. Compose essential finite type maps over Z;
countable polynomial quotients and their localizations give countable finite matrix
cokernels. Transport through Shrink and ULift preserves the semilinear, tensor and
colimit clauses. The module is `lean/Sheaf/RingTheory/LimitModuleSmallOverSystem.lean`.
No new change record is needed because existing interfaces are unchanged.

## Earlier second reading (a previous round; superseded)

Rechecked this repair against the complete landed F2 set, whose four source modules
and matching node copies are unchanged from the repository. The false arbitrary-D
core and wrapper are absent. The caller's proof obtains ring localization comparisons,
constructs modules on a later matrix tail, and restricts the ring colimit by finality;
its node records those actual dependencies. The tower retains its exact original
signature and realizes the same two-descents and cofinal-restriction route.

Checked the remaining split for zero rows, zero columns, singleton directed systems,
and independent universes: countable rings and finite cokernels are small in every
universe, with no u≤v assumption. This statement descends only one algebra and module,
and is strictly smaller than the tower theorem. Its docstring and node give the
source and complete proof plan. The small-universe module's unused import is removed;
the tower's added imports are used in its proof. No axiom, unsafe declaration or
hollow definition is introduced. Compilation checks the complete six-module set,
including the four landed repair modules, rather than using a stale dependency overlay.

## Second reading by P2

1. Interfaces: PASS. Diffed every sandbox Lean module against the repository.
   `limit_tower_over_local_system` has exactly its original signature and docstring;
   only its proof, two private proved helpers and two plain proof imports are added.
   All four copied F2 dependency modules are byte-for-byte identical to the repository,
   as are their seven node records. The existing tower node changes only `proof`,
   `proof_deps` and `proof_origin`. No definition or public import changes, no forced
   adaptation, and no change record is needed.

2. Proof and trust: PASS as a decomposition. Compiled the complete six-module set
   with lcompile.py in import order (all exit 0, no warnings). The tower has no sorry.
   The only new sorry is the entire named theorem
   `RingHom.exists_limit_module_small_over_system`; the two other named sorries are
   unchanged F2 holes. There is no definition with sorry or data extracted from an
   arbitrary unproved existence theorem, and no prohibited declaration mechanism.
   A scratch module printed the axioms of the tower, the new split, the existing
   joint descent and its two open construction dependencies: each uses only
   `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`. Existential witnesses
   are eliminated inside theorem proofs; no public data definition is introduced.

3. New statement: PASS. Read the full independent-universe single-descent signature,
   its docstring and its new node. Its inputs match the existing joint descent except
   for the essential finite type integer-base assumption and the independent additive
   universe. ULift permits the original descent, composition makes each stage ring
   essentially of finite type over Z, and fractions of a countable finitely generated
   subalgebra are countable. Finite-vector cokernels are therefore small in every
   universe. Conjugation by Shrink equivalences preserves functoriality, semilinearity,
   the supplied matrix dimensions and pure-tensor formulas; lifting test cocones
   establishes the smaller-universe colimit. For t=0 the cokernel is zero; for s=0
   it is finite free. For a singleton index the tail is unchanged. Non-antisymmetric
   directed preorders also work, since parallel arrows are equal. No u≤v assumption,
   nonzero module assumption or positive rank is silently used. This descends only
   one upper algebra and module and leaves the two-ring tower assembly to the item.
   It is strictly smaller than the item and has its own node and complete proof plan.

   Repeated searches with different wording through msearch.py LeanFinder, Loogle and
   grep, and searched the project and upstream sources with rg. Loogle found
   `Module.Finite.small` and `Module.Finite.shrink` in Mathlib; these can shorten the
   future transport proof but do not establish the requested descent. The project's
   `Module.exists_finitePresentation_module_diagram` requires finite type stages over
   Z, rather than essential finite type, and does not return the prescribed matrix
   dimensions. No duplicate statement was found. Closing the entire transport theorem
   is not a few-minute repair, so the one split remains explicitly listed above.

4. Route and pruning: PASS. Opened the original tower node and the unit's realized
   record. Checked each returned clause against the two descent signatures: the
   first application uses the concrete empty-matrix cokernel, hBsfinite follows by
   `Algebra.EssFiniteType.comp`, and the second supplies all top-ring/module clauses.
   Auxiliary component equalities are converted to hom equality by extensionality.
   The two natural transformations use the returned transition compatibility, with
   the required reversed equality for naturality. Directed upper tails are nonempty
   and directed; Mathlib's filtered finality criterion applies because the preorder
   category is thin. Finality transports precisely the given base and middle cocones.
   Every tensor clause is selected from the corresponding returned comparison and
   restricted along the second tail. The base diagram and base cocone remain the
   prescribed ones, definitionally. The original three proof dependencies all remain
   in use; none is missing from `No longer needed`. The proof imports are used, and
   the unused descent import of the new wholly-sorry module is absent. No unit
   statement or realized step is removed or bypassed; no newly pruned module is claimed.

   Read the source constructions in [Stacks 00QV](https://stacks.math.columbia.edu/tag/00QV),
   [00QX](https://stacks.math.columbia.edu/tag/00QX) and the presentation/tower paragraphs
   of [00R7](https://stacks.math.columbia.edu/tag/00R7). The proof follows the two local
   algebra descents, finite matrix descent and localization/tensor comparison route.
   The countability and universe transport are an explicit additional argument,
   not an assertion that Stacks discusses Lean universes.

5. Metadata: PASS. The tower node's three steps describe the actual empty-matrix
   descent, independent-universe descent and final restriction; their uses have
   exactly the recorded proof_deps union. The new node has its source, statement
   dependencies, three search kinds, split status, worker/item/group/date provenance,
   blueprint origin, matching chapter/unit and verbatim Lean signature. Its planned
   dependency on joint descent is retained even though that import is correctly
   absent from the wholly-sorry module. The unchanged copied nodes agree with the
   complete landed F2 sources. One hole closed and one added is net zero and is
   reported as a decomposition, not a proof using only the final permitted axioms.

Second-reading changes: added this independent, point-by-point review and recorded
fresh searches and explicit axiom evidence. No Lean proof, signature or node needed
repair; the correct rebased construction was retained.
