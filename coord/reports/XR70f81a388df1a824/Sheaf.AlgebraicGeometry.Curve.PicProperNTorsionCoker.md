## What changed

Restored the module's original proof import boundary and decomposition route. The landed
repair had replaced the private `Sheaf.AlgebraicGeometry.Curve.PicardDecomposition` import
with a direct source-library import, which changed the import closure seen by downstream
modules and triggered duplicate global instances. The module now uses the existing Sheaf
Picard decomposition wrapper again; the theorem statement and docstrings are unchanged.
The proof was checked after a harmless binder cleanup.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker` compiles with no local `sorry`.
No new declarations or holes were added.

## No longer needed

The direct proof import `WeilConjectures.AlgebraicGeometry.Curve.Picard` introduced by the
landed delivery is removed. The source-library decomposition is reached through the existing
Sheaf wrapper. No DAG dependency is removed from the original route.

## Where the brief, the DAG or earlier work was wrong

The landed delivery treated the source-library decomposition import as interchangeable with
the Sheaf wrapper. It is not interchangeable for downstream import closure: the global probe
reported duplicate instances while importing an unrelated tensor module. Restoring the
original private import boundary repairs that failure. The permitted single-file compiler
passes for the repaired module.

## New nodes

None.

## Second reading by XR70f81a388df1a824

1. Compared the scoped Lean module and DAG node with the reference repository and the
   delivered diff. The theorem signature, hypotheses, conclusion, docstring, and
   mathematical target are unchanged. The repair restores the original private Sheaf
   decomposition import, addressing the reported downstream duplicate-instance failure.
   Pass.
2. Compiled the touched Lean file with `python3 /home/ubuntu/weil-launcher/lcompile.py`
   within the 60-second limit. It completed successfully in 2.1 seconds. A source scan
   found no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; no new
   declarations or holes were added. Pass.
3. Read the proof from the target downward. It uses the existing Picard decomposition,
   degree-zero divisibility, and first-isomorphism calculation; the explicit `clear`
   only removes unused witnesses and does not alter the argument. The edge cases and
   nonzero characteristic hypothesis remain exactly as stated. Pass.
4. Checked imports and pruning against the node and report. The direct source-library
   Picard import from the failed delivery is absent; the original Sheaf wrapper and all
   dependencies used by the proof are retained. The DAG proof route and target metadata
   agree with the Lean file. Pass.
5. Verified the reported compiler failure: the repaired import boundary avoids the
   duplicate generated instance encountered by the importer probe. JSON syntax is valid,
   and the repair introduces no workaround axioms or altered targets. Pass.

Changes by the second reader: retained the landed repair's import restoration and made
   only the harmless explicit binder cleanup already present in the sandbox; added this
   independent review and `.check` marker.
