## What changed

Proved `AlgebraicGeometry.Scheme.Divisor.module_local` without changing its signature or
public imports. The proof follows all six steps of the node: a finite-support complement,
valuation comparison, explicit section linear equivalences, compatible over-site sheaf
isomorphisms, an evaluation cocone defining the injective fractional stalk map, and the
zero-divisor section equality. All supporting lemmas are private and proved in this module.

Added the proof-only import
`WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf`; its existing proved no-poles
and regular-section lemmas replace a fresh formalization of the DVR gluing computation.
Updated the node's proof descriptions to record the actual Lean constructions.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.Scheme.Divisor.module_local`.
No sorry remains in the delivered module, and no new holes or modules were added.
This is a proof from existing library dependencies, including
`Scheme.smooth_connected_curve_local_rings`, which remains an upstream item.
The delivery makes no claim to close the transitive axioms of that dependency.

Validation: repeated single-file compilation through lcompile.py, with no warnings.
The empty open is handled explicitly, as are zero rational sections, zero and negative
divisor coefficients, and arbitrary choices of uniformizer. Properness is not assumed.

## No longer needed

Removed the proof-only imports `Sheaf.Topology.PresheafModuleStalkFunctor`,
`WeilConjectures.AlgebraicGeometry.Curve.Divisor`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`.
The latter two are redundant because their declarations are available through the existing
public imports and the no-poles source module. Their mathematical declarations remain used.

The custom stalk-functor module and node `def-weil-pbc-module-stalk` are not needed by this
proof: it uses the existing stalk, colimit and linearity APIs instead. Removed this node
from the proof dependencies. The general gluing node `lem-sc-function-field-sections-glue` is also no longer a proof dependency: the proof uses the already-proved specialized no-poles theorem in `Curve.DivisorIdealSheaf`, whose proof glues local representatives directly rather than applying the declaration recorded for that node. The source FunctionField module remains transitively imported; no claim is made that it leaves the target closure. All other planned mathematical dependencies are retained.
The unit route is unchanged; its realized statement/steps list for this node is empty.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or interface error was found. The original plan omitted the
already-proved no-poles section criterion in Curve.DivisorIdealSheaf. The section map needs
the explicit divisorFunctionAlgebra module instance: the default pointwise function-module
instance is a different action. No signature adaptations were required.

## Second reading by K2

1. Compared the delivered module with the repository version. The public theorem statement and all existing declarations are unchanged byte for byte; only the proof and proof-only import differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings or local `sorry`. Printed axioms of the theorem and all eight private helpers in a scratch copy: only `propext`, `Classical.choice`, `Quot.sound`, and (for the target and the two helpers using the open local-rings theorem) upstream `sorryAx`. No forbidden declarations or hollow definitions were added. The integral instance chosen from the upstream theorem is a proposition, not arbitrary witness data; section equivalences and stalk maps are explicit constructions or determined by their pointwise/germ formulas. Verdict: pass.
3. Read all eight private helpers and the final conjunction proof. Checked empty opens, zero sections, integer powers with zero/negative coefficients, arbitrary uniformizers, generic points, and restriction to intersections for stalk representatives. No new public statement or split-off hole was added. Searched the library for local generator, stalk embedding and integer-order-power declarations; the existing no-poles theorem is the shorter source route already used. Verdict: pass.
4. Checked pruning: the removed proof-only imports are not needed by the current proof; the remaining imports supply the public definitions and used declarations. The old stalk-functor dependency is absent from the proof. Verdict: pass.
5. Compared the old and new node records. Repaired the retained general gluing dependency: its declaration is unused, since the proved upstream no-poles theorem performs the gluing directly. The six mathematical steps, node statement and statement dependencies stay unchanged; the actual source specialization and stalk API now appear in the proof record. The union of step uses equals proof_deps. Read dag/units/sk-def-pic.json: its realized statement/steps lists are empty and its route is unchanged. Verdict: pass after repair.

Changes: restored the extra space before `:= by` so the existing signature is byte-for-byte identical; removed `lem-sc-function-field-sections-glue` from the proof dependencies and step uses, rewrote step 2 to describe the proved source route, and removed the stale custom-stalk-node citation from step 5. Updated the pruning report and proof origin. The compiled Lean proof is unchanged.
