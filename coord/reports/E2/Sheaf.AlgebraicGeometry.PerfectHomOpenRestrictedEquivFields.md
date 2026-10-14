## What changed

Proved `AlgebraicGeometry.perfect_hom_open_restricted_equiv_fields_exists` in
`Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedEquivFields`, with its existing
signature and public imports unchanged. Added a proof-only import of
`Sheaf.AlgebraicGeometry.RelativeMVInverseOpenIso`. Yoneda is already available
through the existing imports; the second reader removed its redundant import.

Three proved private helpers perform the argument: `representingIso` identifies the
representing object by Yoneda; `openPushPullIso` transports open restriction of the
push-pull object; `restrictedHomEquiv` transposes the resulting object isomorphism
and proves its naturality. The final theorem applies this construction uniformly
to every stage and to the apex. The adjunctions are the existing pinned
`relativeMVAdj` constructions. No arbitrary object is chosen from an unproved
existence statement, and no definition, statement, or public visibility changes.

Updated the item's DAG proof, proof dependencies, and proof origin to match the
compiled proof. The unit `sk-thm-picard-semicon` has no realized nodes for its
statement or steps, so this route removes no unit realization.

Sources checked: [Stacks 079W](https://stacks.math.columbia.edu/tag/079W) for the
unbounded pullback/direct-image adjunction and
[Stacks 08FE](https://stacks.math.columbia.edu/tag/08FE) for restriction of derived
direct image. Mathlib supplies Yoneda, pullback-square pasting, and the
projection-preserving `IsPullback.isoPullback`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.perfect_hom_open_restricted_equiv_fields_exists`
(node `new-perfect-hom-open-restricted-equiv-fields`).

No sorry remains in the delivered module. No new holes or modules are added.
This is a proof from existing declarations, not a decomposition. The three
private helpers have complete proofs. The file compiles without warnings in
10.9 seconds through `lcompile.py`; the delivery dry run checks the axiom probe
and preflight as well.

## No longer needed

The second reader removed the redundant proof-only import
`Mathlib.CategoryTheory.Yoneda`; the existing imports already expose the Yoneda
declarations, as confirmed by compiling without this import.

Removed the planned proof-dependency edge to
`new-perfect-hom-open-restricted-core` /
`Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedCore`. That module is never
imported here; it instead imports this item through
`Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedMaps` and applies this item's
theorem in its own proof. This is removal of a cyclic DAG proof dependency,
not a claim that the core module is globally unreachable or should be deleted.

No original Lean import was removed: both public imports supply the unchanged
statement and the proof. A temporary proof-only import of
`Sheaf.AlgebraicGeometry.DerivedAdjoint` was removed after switching to the
pinned adjunction already exposed by `RelativeMVInverseOpenIso`.

No other nodes or modules from the original plan are pruned. No transition-map,
cocone-map, or QCoh proof is needed for these four fields.

## Where the brief, the DAG or earlier work was wrong

The original DAG cites `new-perfect-hom-open-restricted-core` as this item's sole
proof dependency. Its Lean proof already invokes this item's theorem, so importing
it would create an import cycle. Moreover the original proof text mentions
assembling transition and cocone compatibility fields, which this structure does
not contain. The updated plan identifies the representing objects by Yoneda and
uses existing open comparisons to prove exactly the four fields actually stated.

No statement is disputed. The argument works for the empty open, zero objects,
arbitrary preorder indexing, and arbitrary cocones: it uses no colimit witness,
perfectness, or quasi-coherence. No interface changes or forced adaptations.


## Second reading by E2

1. **Unchanged interfaces — PASS.** Compared every delivered Lean module (one)
   and the existing node against the read-only repository with `diff -u`.
   Independently compared the complete structure text and theorem signature:
   byte-for-byte unchanged. No existing definition or public visibility changes;
   additions are three private, fully proved helpers and a proof-only import.
   The existing-node edits are confined to `proof`, `proof_deps`, `proof_origin`.
   No change records or forced adaptations are needed.
2. **Kernel proof — PASS.** Independently compiled the module through
   `lcompile.py`, without errors or warnings. Scanned for sorry and forbidden
   declarations/options: none. A scratch copy with `#print axioms` for all three
   helpers and the public theorem compiled; every declaration uses exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   The helpers construct their isomorphisms from Yoneda and explicit existing
   comparisons. The final choices select equivalences from the fully proved
   `restrictedHomEquiv`, not arbitrary objects from unproved existence results.
3. **Split statements and edge cases — PASS.** No statement is split off and
   no holes are added. Read all three helpers: the Yoneda equivalence has the
   correct orientation and testing-object naturality; the pasted pullback
   isomorphism preserves the projection to B; the last inverse adjunction
   yields precisely the required Hom equivalence. Empty opens, zero objects,
   the identity open, and arbitrary preorder indexing require no extra
   assumptions. No perfectness or colimit hypothesis is smuggled in.
4. **Route and pruning — PASS after import repair.** Searched the current
   Lean library by representing-object, restricted-Hom and comparison names,
   and inspected Mathlib Yoneda for shorter existing constructions. The proof
   already uses Mathlib fully faithful Yoneda and the library's explicit
   comparisons; no matching shorter upstream theorem was found. Tested a
   scratch copy without `Mathlib.CategoryTheory.Yoneda`: it compiles, so removed
   that redundant proof-only import. Retained both public imports because they
   supply the unchanged statement. The report accounts for the only original
   proof dependency, `new-perfect-hom-open-restricted-core`: it depends on this
   item via the maps module, so the old edge was cyclic. This does not claim
   global unreachability. Read `dag/units/sk-thm-picard-semicon.json`:
   `realized.statement` and its sole `realized.steps` entry are empty; this
   delivery bypasses no realized unit node.
5. **DAG agreement — PASS.** Read the updated proof steps, each dependency's
   Lean record, and the modules defining the comparisons and pinned adjunction.
   The five dependencies cover the supplied data, restriction, adjunction,
   pullback-open comparison and iso transport used in the proof. Their union
   equals `proof_deps`; `proof_origin` records this route. No new nodes need
   validation.

Second reading changed only the redundant Yoneda import and this report.
One original hole is closed:
`AlgebraicGeometry.perfect_hom_open_restricted_equiv_fields_exists`; zero holes
are added. The construction and all signatures are retained.
