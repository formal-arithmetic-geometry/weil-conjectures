## What changed

Proved `AlgebraicGeometry.unramified_baseChange_restrict_open` in
`Sheaf.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen`, with its signature unchanged.
The original locally-finite-type/formally-unramified route is implemented entirely from Mathlib.
Base change uses `MorphismProperty.pullback_snd`; restriction uses the existing finite-type
instance and `IsZariskiLocalAtSource.resLE`. The diagonal instances finish both conclusions.
Removed the proof-only import `Sheaf.AlgebraicGeometry.Thickening`.
Publicly import `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` for the statement,
and privately import `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified` for the proof.
Updated the node's fifth step, proof dependencies and proof origin to match the local argument.
The module docstring retains its sources; the theorem's proof description records the locality step.

## Proved and sorry left

Proved `AlgebraicGeometry.unramified_baseChange_restrict_open`
(node `lem-weil-pbc-unramified-base-change-open`), the only original sorry. No sorry remains,
and none was introduced. Local single-file compilation passes with no warnings.

## No longer needed

Removed import/module `Sheaf.AlgebraicGeometry.Thickening`.
This proof no longer needs nodes `def-sbc-first-order-thickening` and
`lem-weil-pbc-open-immersion-monomorphism`; these were used only by the explicit lifting
argument replaced by locality. All other original proof dependencies remain used, either
through Mathlib's instances or the local restriction lemma. No unit statement or step is bypassed:
this node is below the realized nodes of `sk-thm-p1`.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The DAG's lifting argument was unnecessary because
Mathlib already supplies the local property and its generic restriction theorem. Its fifth
proof step now records that route. Loogle, LeanFinder and grep searches confirmed the existing
Mathlib support; direct searches of the source library found no theorem with this full signature.
No new nodes or interface changes were needed.

## Second reading by W2

1. Compared the complete module with the repository version. PASS: the existing theorem
   signature is byte for byte identical, with no definitions or added declarations.
   Only imports, proof documentation and the proof body differ; no statement change record
   is needed. The public-import correction is documented in
   `coord/changes/unramified-base-change-open-proof-import.md`.
2. Compiled the module locally without errors or warnings. PASS: no sorry remains and no
   prohibited declaration or implementation escape is present. A scratch copy with
   `#print axioms AlgebraicGeometry.unramified_baseChange_restrict_open` reports only
   `propext`, `Classical.choice` and `Quot.sound`.
3. PASS: no statements were split off and no new nodes were added. Both arbitrary base
   change and arbitrary compatible open restrictions are covered, including empty opens
   and identity restrictions; no nonemptiness, finiteness or surjectivity assumption enters.
4. Read the pinned Mathlib instances for finite-type base change and restriction,
   the open-diagonal/formally-unramified implications, and `IsZariskiLocalAtSource.resLE`.
   Searched the library and Mathlib by base-change, restriction and diagonal terminology;
   the existing short argument uses these APIs directly. PASS: the old dependency set minus
   the new set is exactly the two nodes already listed under No longer needed. The node
   is below the realized nodes of `dag/units/sk-thm-p1.json`; its unit route is preserved.
   Fixed the proof-only public import: `FormallyUnramified` is now a plain import and
   `FiniteType` supplies the public statement vocabulary. The four importing project
   modules already import their own statement vocabulary and receive no changed signature.
5. Compared the node JSON structurally. PASS: only `proof`, `proof_deps` and `proof_origin`
   change; the dependency list equals the union of step uses. Checked the retained nodes'
   Mathlib matches against the proof's instances. No new node or new sorry needs metadata.

Second reading changed only the import visibility described above and this report;
retained the checked proof and its node metadata.

Change record: `coord/changes/unramified-base-change-open-proof-import.md`
(import visibility only; required by the delivery preflight).
