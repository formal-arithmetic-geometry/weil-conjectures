## What changed

Filled `Algebra.isGeometricallyRegular_of_faithfullyFlat` in
`Sheaf.RingTheory.GeometricallyRegularDescent`, preserving its signature and docstring.
Added proof-only imports `Mathlib.Algebra.Algebra.Shrink` and
`Mathlib.Algebra.Field.Shrink`.
The proof follows [Stacks Tag 07NH](https://stacks.math.columbia.edu/tag/07NH),
read online because the local literature source was absent. It descends Noetherianity
using the existing Mathlib leaf, then descends regularity after each finite purely
inseparable extension using `IsRegularRing.of_faithfullyFlat`. Tensor commutativity
and cancellation implement the base-change identification. Shrinking the extension
handles the independent universes of A and B, preserving all field-extension data.
Updated the existing node's proof and proof dependencies to record these steps.
Local compilation passes without warnings; no new modules or declarations.

## Proved and sorry left

Closed the one hole `Algebra.isGeometricallyRegular_of_faithfullyFlat`
(node `lem-weil-pbc-geometrically-regular-descent`). No sorries remain in the item,
and no holes were added. This is a proof from existing dependencies, rather than
a new decomposition. The imported `IsRegularRing.of_faithfullyFlat`
(node `lem-weil-pbc-regular-ring-faithfully-flat-descent`) still has its existing
sorry in the repository; it is not modified by this delivery.

## No longer needed

No baseline imports removed. The second reader removed the redundant new import
`Mathlib.RingTheory.Finiteness.Small`: its theorem is already available through
the existing imports. Removed `lem-weil-pbc-flat-module-base-change` from this node's
proof dependencies: the existing faithfully-flat tensor-product instance already
provides both flatness and faithfulness. No dedicated Sheaf module for flat base
change is used. All other planned dependencies remain used; no other nodes or
modules are pruned by this proof.

## Where the brief, the DAG or earlier work was wrong

The earlier proof-dependency list included `lem-weil-pbc-flat-module-base-change`
although no proof step cited it. The revised list equals the union of step uses.
The informal plan omitted the separate Noetherian conjunct of the Lean definition
and its algebra-dependent field-extension universe; the proof supplies Noetherian
descent and transports a finite extension through `Shrink` without changing any
statement or definition. The unit's own statements and steps are preserved.


## Second reading by J3

1. **Visible statements unchanged: PASS.** Diffed the delivered Lean file and node
   against the repository. The only Lean changes are the theorem body and two
   proof-only imports. The existing signature and docstring are byte-for-byte
   unchanged; no definitions or declarations were added. The field, two commutative
   algebras, scalar tower, faithful flatness, hypothesis and conclusion still match
   [Stacks Tag 07NH](https://stacks.math.columbia.edu/tag/07NH), read online.
   No change record is needed.
2. **Proof and axioms: PASS, conditional on the existing dependency.** Local
   compilation is clean. A scratch copy with `#print axioms` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The last is expected
   from the unchanged `IsRegularRing.of_faithfullyFlat`. There is no local `sorry`,
   forbidden declaration, or data chosen from an unproved existence theorem.
   `Shrink` uses Mathlib's proved smallness theorem and algebra equivalence.
3. **Split statements: PASS (none).** No new statements, modules, nodes or holes
   were split off. Read the existing regular-ring descent statement and
   [Tag 07NG](https://stacks.math.columbia.edu/tag/07NG): it applies to the
   faithfully flat tensor extension without any extra local or finite-type
   assumption. Read [Tag 033E](https://stacks.math.columbia.edu/tag/033E) and the
   node's Mathlib match: taking the module to be A and using the right-unit
   equivalence gives precisely Noetherianity of A.
4. **Route and pruning: PASS after one import repair.** The Noetherian conjunct is
   proved directly with Mathlib. For K/k finite purely inseparable, finite-module
   smallness permits shrinking into `max u w`; field, finite-module and purely
   inseparable structures are preserved. The tensor equivalences carry regularity
   successively to `K tensor B`, `B tensor K`,
   `B tensor_A (A tensor K)`, and `(A tensor K) tensor_A B`. The existing
   faithful-flat base-change instance supplies exactly the algebra structure used
   by regular-ring descent. The final commutation gives `K tensor A`.
   Checked Mathlib's regular-ring files, upstream RingTheory and Sheaf for a
   shorter existing descent route, and repeated msearch with the alternative
   query "regular ring descent along a faithfully flat extension"; none found.
   Removing each new import in scratch copies showed that both Shrink imports
   are necessary but `Finiteness.Small` is redundant, so it was removed.
   `## No longer needed` covers the sole removed old proof dependency.
   Read `dag/units/sk-thm-p1.json` and its `realized` fields: this item and the
   pruned flat-module node are below the unit's realized route; its statement and
   every realized step remain unchanged. No module is claimed pruned.
5. **DAG matches Lean: PASS.** The first node step names the exact Noetherian
   descent Mathlib leaf. The second records the finite purely inseparable test,
   universe shrink, tensor identifications, faithfully-flat base change and
   existing regular-ring descent. `proof_deps` is exactly the union of step uses;
   `proof_origin` names 07NH and the explicit Noetherian step 033E. The diff changes
   only the allowed proof fields. There are no new nodes to audit.

Changed only the redundant proof import and the report. The proof itself required
no repair. One existing hole is closed, zero added; this does not certify its
still-open regular-ring descent dependency.
