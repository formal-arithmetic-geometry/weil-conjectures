## What changed

Replaced the sorry in `AlgebraicGeometry.singleComplexOpen_unit_square_factorization`
with the pinned Hom-equivalence compatibility, inversion of that equivalence, and
naturality of the five-factor open-square comparison. The theorem's signature and
existing docstrings are unchanged. Added the proved private categorical helper
`map_comp_square_factorization` in the same module to perform the functoriality and
associativity calculation without repeatedly unfolding scheme-module instances.
The node now records these three steps.

Replaced the unused public import
`Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso` with the direct public
import `Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData`, which supplies
`singleComplexOpenPullbackIso` used by the existing statement. The sole importer,
`SingleComplexOpenPullbackCounitHomotopyFactorization`, imports the removed module
itself already. No dependent module needs adaptation. The import-interface change record is
`coord/changes/single-complex-open-unit-square-import-pruning.md`.

## Proved and sorry left

Closed: `AlgebraicGeometry.singleComplexOpen_unit_square_factorization`
(node `lem-pc-k3-open-unit-square-factorization`), the module's only original hole.
Added no holes and no intermediate public statements. No sorry remains in this
module or is added by this delivery. This is a proof, not a decomposition.
Its existing dependencies can still depend on sorry; no claim is made that the
entire upstream import closure is already axiom-free.

The homotopy counit normalization uses `exists_schemeDerivedAdjunction` with the
same additivity, epsilon and derived-functor proof as the named pinned adjunction.
All calculations hold for arbitrary homotopy complexes, including zero complexes,
and for empty opens: no invertibility of the right-derived unit, nonemptiness,
boundedness, tensor comparison cancellation or extra geometric assumption is used.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso`.
That module and its tensor restriction comparison definitions (node
`def-pc-open-pinned-single-tensor-restriction-iso`) are not needed by this proof.
The resulting direct import closure also avoids
`Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso` (node
`def-pc-tensor-pullback-composition-iso`) through that removed import;
no assertion is made that these modules disappear from all targets, since the parent
factorization still uses them independently. The original proof dependency on
`def-pc-t2-open-pinned-adjunction` is retained. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The proposed mathematical argument fits the existing interfaces. The node's
statement additionally introduces a tensor restriction comparison t, but t occurs
in neither the Lean conclusion nor the argument for this intermediate identity.
Its import was therefore unnecessary here; no statement or definition was changed.

The initially attempted direct scheme-specific rewrites spent their heartbeat
budget unfolding category-instance aliases. Performing the same associativity and
functoriality argument in a proved private helper with abstract categories resolves
that elaboration issue, without changing any definition or the compile time limit.
Source checked: [Stacks Tag 08HY](https://stacks.math.columbia.edu/tag/08HY),
the counit description of the canonical base-change map. No new nodes were required. The public-import change has the record named above.

Validation: the completed proof compiled through `lcompile.py`; the delivery dry
check also compiles the final module and checks the unchanged signatures and axioms.
The linter suppression is scoped to the theorem and preserves its original unused
F₀ let binder. The larger heartbeat budget concerns elaboration of pinned choices;
the 60-second single-file compilation limit is unchanged.

## Second reading by R3

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; the only interface change is the declared import pruning recorded above. Verdict: passed.
2. Compiled the module and sandbox import order with `lcompile.py`; there are no errors or warnings, no `sorry`, axiom, unsafe, opaque, extern, or implemented_by declarations. Verdict: passed.
3. Checked the proof against the imported adjunction compatibility and categorical naturality calculation, including zero complexes and empty opens. The theorem proves the unchanged node statement, and no new statement was introduced. Verdict: passed.
4. Checked the shortest available route and imports. The private abstract categorical helper is used only for the associativity/naturality rewrite; `OpenPinnedSingleDegreeZeroCounitIso` is unused and was pruned. The node proof and proof_deps match the Lean proof, with no old dependency removed from the unit route. Verdict: passed.
5. Checked the DAG node and unit route: the node records the three proof steps, source, origin, and unchanged statement; the realized unit route remains intact. Verdict: passed.

Changed after this reading: no proof or statement changes. Added this second-reading record only; the import-pruning change remains documented in its change record.

Independent axiom check: a scratch copy with `#print axioms
AlgebraicGeometry.singleComplexOpen_unit_square_factorization` compiled in 41.6 seconds
and listed exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The final dry run printed OK. The unit `sk-thm-picard-semicon` has no realized nodes
listed for its statement or step; this below-unit reduction changes none of its route.
The sole direct importer already publicly imports the removed dependency itself.
