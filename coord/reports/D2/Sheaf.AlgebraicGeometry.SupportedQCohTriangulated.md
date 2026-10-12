## What changed

The item module factors the original supported quasi-coherent predicate through the transparent
abbreviation `supportedProperty` and assembles its three closure obligations with
`ObjectProperty.IsTriangulated.mk`. The second reading proved integer-shift closure directly
using the existing Mathlib shift sequence, quasi-coherence invariance under isomorphisms, and
injectivity of the induced stalk isomorphism. No import was added or removed.

## Proved and sorry left

Closed with no `sorryAx`: `AlgebraicGeometry.supported_qcoh_stableShift`
(node `lem-pc-supported-qcoh-stable-shift`).

The original `AlgebraicGeometry.supported_qcoh_isTriangulated` hole is replaced by a proof
assembling the three closure obligations, but it still depends on the two remaining holes:
`AlgebraicGeometry.supported_qcoh_containsZero` (`lem-pc-supported-qcoh-contains-zero`) and
`AlgebraicGeometry.supported_qcoh_closedMiddle` (`lem-pc-supported-qcoh-closed-middle`).
These are strict, independently needed components, not a restatement of the target. Against
the read-only local original, one upper hole is closed and two lower holes are added: a
partial decomposition, not a complete proof of triangulated closure. The launcher reports
that the server baseline already contains the three-way decomposition; against that baseline,
this reading closes one of its three holes and adds no hole. The ledger determines progress.

## No longer needed

None. The old target node has an empty `proof_deps`, so there is no omitted old dependency.
Both public imports occur in the statements: the scheme derived category definitions and the
triangulated object-property classes. No module is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier report overstated the closure proof and its docstrings were incomplete. The DAG
plan describes four mathematical arguments with no proof dependencies; it does not provide
four separate Lean declarations. The upstream `DerivedCategory.homologyProperty` instances
can express the same generic reduction, but still require the supported quasi-coherent sheaf
property's closure instances. They do not already prove either remaining scheme-level hole.
The delivery tool's server baseline differs from the read-only local snapshot and already has
the three closure holes; this reading proves shift closure rather than resubmitting them.

## New nodes

`lem-pc-supported-qcoh-contains-zero` records the zero-object obligation, still open.
Its docstring explains zero homology, the empty presentation, and zero stalks.

`lem-pc-supported-qcoh-stable-shift` records shift closure, now proved using Mathlib's shift
sequence and isomorphism transport. Its proof metadata follows the implemented proof.

`lem-pc-supported-qcoh-closed-middle` records the remaining middle-term obligation.
Its docstring gives the kernel/cokernel extension argument and exact stalk argument.

Change record: `coord/changes/supportedProperty.md`.

## Second reading by D2

1. Compared the item module with the read-only repository using diff. The signature of the
   only pre-existing theorem, `supported_qcoh_isTriangulated`, is byte for byte identical.
   Its original docstring was restored. The new abbreviation is transparent and reproduces
   the original predicate exactly; its addition is documented in the change record. Pass.
2. Compiled the module and a scratch copy with `#print axioms` for all four theorems using
   only lcompile.py. Shift closure uses only `propext`, `Classical.choice`, and `Quot.sound`.
   The other three additionally use `sorryAx` precisely through the two named open theorems.
   There is no forbidden declaration, hollow definition, or choice of an undetermined witness.
   Pass with the two explicitly recorded mathematical obligations remaining open.
3. Checked the three obligations against the original property, including empty T, T = X,
   zero objects, all integer shifts (including negative shifts), and distinguished triangles.
   They are true, independently needed components, each strictly smaller than the target.
   Searched with leanfinder, loogle, launcher grep, and rg using zero-object, shift-isomorphism,
   weak-Serre-class, and kernel/cokernel terminology. Inspected the upstream homologyProperty
   file: its generic closure instances require additional sheaf-property closure instances,
   so neither remaining obligation is duplicated by an applicable existing declaration.
   Expanded sources and complete natural-language proofs in the new docstrings. Pass.
4. Kept the direct top-down route and proved its shift component with the existing Mathlib
   declarations. The two imports are needed by signatures. The original proof_deps is empty;
   `No longer needed` is complete. Inspected sk-thm-picard-duality.json: this node is not a
   realized unit statement or step (the realized lists are empty); no unit route is bypassed.
   Pass; no pruning is claimed.
5. Checked node names, declarations, chapter, unit, signatures, proof steps, and proof_deps.
   Updated shift proof and origin to the actual Mathlib-based proof and recorded the new
   Lean signatures verbatim. The target node uses the three closure nodes actually referenced
   by its proof. Pass.

Changes by this reading: proved `supported_qcoh_stableShift`; repaired sources and proof
handoff docstrings; restored the original target docstring; removed the unnecessary linter
option and replaced `letI` with `let`; corrected the shift node and the report/change record.
