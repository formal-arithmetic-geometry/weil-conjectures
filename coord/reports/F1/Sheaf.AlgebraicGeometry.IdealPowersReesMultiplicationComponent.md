## What changed

Repaired `Sheaf.AlgebraicGeometry.IdealPowersReesMultiplicationComponent` after the
import-prune return. The three generic affine helper declarations (`image_range_affine`,
`product_range_affine`, and `hom_zero_of_affine`) are now local proof facts inside the
component theorem, so this module no longer declares statements already present in
`Sheaf.AlgebraicGeometry.AffinePushforwardIdealProduct`. Their proofs and all uses are
unchanged. The theorem signature and public imports are unchanged.

## Proved and sorry left

`AlgebraicGeometry.idealPowersReesMultiplication_component` remains proved. No `sorry`
was added and no `sorry` remains in the delivered module.

## No longer needed

The former top-level duplicate helper declarations are no longer needed as module
interfaces; they are local facts used only by the component proof. The plain import
`Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient` from the repository version was
removed because the proof does not use it; the added helper imports are proof-only.

## Where the brief, the DAG or earlier work was wrong

The prior delivery exposed three private helpers as declarations whose statements
already occur in `AffinePushforwardIdealProduct`; the landing checker correctly rejected
those duplicates. Localizing them preserves the proof while removing the duplicate
interfaces. The existing declarations are private in their source module, so they cannot
be referenced by name from this module; the local facts are therefore retained for the
same elementary arguments.

## Earlier second reading (a previous round; superseded)

Repair checked locally: the theorem interface is unchanged, the duplicate affine helper
statements are local proof facts, and the component theorem compiles without new holes.
No node or public import was changed.

## Second reading by F1

1. Compared the delivered module with the repository version. The theorem statement and
all existing declaration signatures are byte-for-byte unchanged; only the proof, local
helpers, and proof-only imports differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors and contains no
`sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof introduces
no new declarations requiring DAG nodes. Verdict: pass.
3. Checked the proof route and searched the library for duplicate helper statements. The
three affine facts are local and the existing target statement is unchanged and true;
the node's recorded statement and dependencies agree with the code. Verdict: pass.
4. Checked pruning. The former `ModulePullbackIdealQuotient` import is unused and was
removed; all remaining imports are used by the proof. The unit route is preserved: the
component theorem still realizes `sk-thm-p1` through the stated affine multiplication
argument. Verdict: pass.
5. Checked the node metadata against the Lean declaration, including `proof`,
`proof_deps`, and `proof_origin`; they match the implemented route, with no split-off
statements or new nodes. Verdict: pass.

Changed the proof-only import set and shortened one long line; no public interface,
target statement, definition, or DAG statement was changed.
