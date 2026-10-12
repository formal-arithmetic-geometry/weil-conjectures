## What changed

Proved `AlgebraicGeometry.RingedSpace.moduleSheaves_abelian_enoughInjectives` in
`Sheaf.Topology.RingedSpaceModuleEnoughInjectives`, preserving the existing
signature, universes, definitions and public imports. Mathlib supplies the abelian
instance. The proved upstream `SheafOfModules.isGrothendieckAbelian`, specialized
to `moduleRings X`, supplies the Grothendieck instance, and Mathlib's
`IsGrothendieckAbelian.enoughInjectives` supplies enough injectives. Added only
proof imports of the upstream module and Mathlib's enough-injectives module.
Updated the existing node's proof, proof_deps and proof_origin accordingly.

## Proved and sorry left

Proved the sole theorem
`AlgebraicGeometry.RingedSpace.moduleSheaves_abelian_enoughInjectives`
(node `lem-sc-ringed-space-module-sheaves-enough-injectives`).
No sorry remains, no new sorry or split-off statement is introduced.
The final scratch-copy `#print axioms` check shows only `propext`,
`Classical.choice` and `Quot.sound`; in particular no `sorryAx` remains in its closure.

## No longer needed

Removed the original proof-only import
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions` and its node
`prop-pur-kinjective-resolutions-exist` from the proof dependencies.
The first worker's replacement proof-only import
`Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian` and its node
`lem-pur-ringed-site-grothendieck-abelian` are also unnecessary for the final proof.
The two old proof dependencies were checked: the Mathlib leaf
`lem-sp-grothendieck-enough-injectives` remains used; only
`prop-pur-kinjective-resolutions-exist` is pruned from the original node.
These modules may still be reached by other target branches.
Both existing public imports remain because they supply the public statement's
interface; the two new plain imports supply only proof instances and theorems.

## Where the brief, the DAG or earlier work was wrong

The original DAG route extracted the Grothendieck property from the stronger
K-injective resolution theorem. The first worker shortened this to the existing
open ringed-site Grothendieck theorem, but missed the proved upstream theorem
`SheafOfModules.isGrothendieckAbelian`. The second reading found it by searching
both library roots and replaced that open dependency. No statement or definition
error, change record or new node was needed.

## Second reading by N1

1. Compared the delivered Lean module and node with their repository versions.
   The existing theorem signature is byte for byte unchanged. No definition,
   universe or public import changes; only proof imports, proof, explanatory
   docstring and the permitted node proof fields change. Verdict: pass.
2. Compiled locally without errors or warnings. Checked all delivered Lean text:
   no sorry, axiom, unsafe, opaque, implemented_by or extern. A scratch copy with
   `#print axioms` lists exactly propext, Classical.choice and Quot.sound after
   the repair. The first worker's version had sorryAx through its open
   Grothendieck dependency; the repaired proof does not. Verdict: pass.
3. No new statements or split-off theorems. Inspected the upstream proof of
   `SheafOfModules.isGrothendieckAbelian`, Mathlib's module-sheaf abelian instance
   and Grothendieck enough-injectives instance. The site is Opens X, small in u,
   and moduleRings X has exactly the required ring and module universes.
   The arbitrary ringed-space hypothesis includes the empty space and the zero
   structure ring; no nonemptiness or locality premise is introduced. Verdict: pass.
4. Searched lean/Sheaf, lean/WeilConjectures and Mathlib's module-sheaf sources
   for Grothendieck and enough-injectives declarations. Found the shorter proved
   upstream route and used it. The original proof_deps difference is completely
   listed above. Read dag/units/sk-thm-curveestimate.json: realized.statement is
   thm-sc-proper-cohomology and realized.steps is empty; no unit realization is
   bypassed. The existing public interface is preserved, and new imports are
   proof-only. Verdict: pass after repair.
5. Read the old and new node proof, proof_deps and proof_origin, and the records
   of the two retained Mathlib leaves. The final node records the upstream
   theorem specialization explicitly and lists the two Mathlib leaves used.
   No new nodes require validation. Verdict: pass after repair.

Changed during second reading: replaced the open Grothendieck dependency with
proved upstream `SheafOfModules.isGrothendieckAbelian`; updated the proof-only
import, proof explanation, node proof fields and report. No other module changed.
