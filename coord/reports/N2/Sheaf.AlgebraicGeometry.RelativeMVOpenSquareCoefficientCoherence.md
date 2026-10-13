## What changed

Added the proof-only import of `Sheaf.AlgebraicGeometry.CanonicalRelativeMVOpenSquareCoefficientCoherence` and proved `relativeMV_open_square_coefficient_coherence` by rewriting its five supplied comparison hypotheses and applying the canonical specialized identity. Added the canonical intermediate theorem module and its DAG node; that theorem remains the sole proof hole.

## Proved and sorry left

The target declaration `AlgebraicGeometry.relativeMV_open_square_coefficient_coherence` is proved. The new declaration `AlgebraicGeometry.canonical_relativeMV_open_square_coefficient_coherence` remains `sorry`, with node `new-canonical-relative-mv-open-square-coefficient-coherence`.

## No longer needed

No imports or stated proof dependencies were removed. The direct low-level coordinate-change import is needed by the new canonical intermediate theorem.

## Where the brief, the DAG or earlier work was wrong

The planned proof route omitted the substantial component expansion required to specialize `coefficient_square_coordinate_change`; this was split into the strictly simpler canonical specialization theorem.

## New nodes

`new-canonical-relative-mv-open-square-coefficient-coherence`: canonical coefficient coherence with all arbitrary comparison data eliminated; its module is `Sheaf.AlgebraicGeometry.CanonicalRelativeMVOpenSquareCoefficientCoherence`.

## Earlier second reading (a previous round; superseded)

The canonical intermediate theorem is the strictly simpler specialization needed after rewriting the five hypotheses. The target statement and its hypotheses are unchanged, and the unit route through coefficient-square coordinate change is retained.

## Second reading by N2

1. Compared both delivered modules against the repository versions. The target theorem's signature and all existing declarations are unchanged; the only target change is its proof and a proof-only import. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`; compilation succeeds. The target has no local `sorry`; the canonical intermediate theorem is the sole listed split-off `sorry`, with its node and proof docstring. Verdict: pass.
3. Checked the canonical specialization statement against the coordinate-change theorem and its edge cases (equal or empty opens and zero coefficients). It is a strict specialization with comparison data eliminated, and is not duplicated elsewhere in the library. Verdict: pass.
4. The proof follows the shortest available route after rewriting the five hypotheses: apply the canonical specialization theorem. The target keeps the RelativeMVMaps import; no obsolete imports were found. Verdict: pass.
5. Updated the target DAG proof and proof dependencies to name the canonical intermediate node actually used by the Lean proof. The unit route through coefficient-square coordinate change is retained by that node. Verdict: pass.

Changed the report and target DAG proof metadata only; no Lean statements or definitions were changed.

## Second reading by N2

1. Compared both delivered modules against the repository versions. The target theorem's signature and all existing declarations are unchanged; the only target change is its proof and a proof-only import. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`; compilation succeeds. The target has no local `sorry`; the canonical intermediate theorem is the sole listed split-off `sorry`, with its node and proof docstring. Verdict: pass.
3. Checked the canonical specialization statement against the coordinate-change theorem and its edge cases (equal or empty opens and zero coefficients). It is a strict specialization with comparison data eliminated, and is not duplicated elsewhere in the library. Verdict: pass.
4. The proof follows the shortest available route after rewriting the five hypotheses: apply the canonical specialization theorem. The target keeps the RelativeMVMaps import; no obsolete imports were found. Verdict: pass.
5. Updated the target DAG proof and proof dependencies to name the canonical intermediate node actually used by the Lean proof. The unit route through coefficient-square coordinate change is retained by that node. Verdict: pass.

Changed the report and target DAG proof metadata only; no Lean statements or definitions were changed.
