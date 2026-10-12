## What changed

Proved `CochainComplex.nonempty_tensorRestrictExtendScalarsIso` without changing its
signature or docstring. Its proof assembles a natural module comparison into a bicomplex
isomorphism and applies the existing source-library `HomologicalComplex₂.mapTotalIso`.
Added the proof-only imports of `TensorRestrictExtendScalarsModule` and
`WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap`.

The new module `Sheaf.Algebra.Homology.TensorRestrictExtendScalarsModule` proves
`ModuleCat.exists_tensorRestrictExtend_module_natural` using Mathlib's `cancelBaseChange`,
restriction of the linear equivalence, and two tensor inductions for naturality.
Updated the parent node's proof and dependencies to match this implementation.

## Proved and sorry left

Closed the single original hole: `CochainComplex.nonempty_tensorRestrictExtendScalarsIso`
(node `lem-pc-tensor-restrict-extend-scalars`).
Also proved `ModuleCat.exists_tensorRestrictExtend_module_natural`
(node `lem-pc-tensor-restrict-extend-module-natural`). No holes added or left in the delivery.
The intermediate module theorem is proved, so this is a proof rather than a decomposition.

## No longer needed

No original imports were removed; all three public Mathlib imports support the statement.
Removed the earlier sandbox's proposed `Sheaf.Algebra.Homology.RestrictScalarsTotal`
module and `new-restrict-scalars-total` node: the source library already proves the
comparison as `HomologicalComplex₂.mapTotalIso`. Neither is part of this delivery.
Removed the two proposed intermediate sorries; the naturality comparison is now proved.
The parent no longer has direct proof dependencies on `def-weil-module-base-change` and
`def-weil-pbc-module-tensor-product`; those notions remain needed in the new module node.
Removed the redundant proof-only import `Mathlib.LinearAlgebra.TensorProduct.Tower`
from the new module: `ChangeOfRings` already imports it publicly.
No existing library module is claimed to leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt missed the existing source-library totalization comparison, left
placeholder node statements, used node IDs inconsistent with the Lean docstrings, and
recorded the module name incorrectly. All are repaired. Its second-reading section was
removed because that belongs to the independent reader.

Checked the source at https://stacks.math.columbia.edu/tag/06Y1: its proof uses the tensor
base-change identity; the explicit module/naturality argument expands that identity.
The unit `sk-thm-picard-duality` has no realized step bypassed by this local tensor proof.
The module construction uses no flatness or nonzero assumptions: zero modules and zero
rings obey the same tensor formulas. Totalization uses coproduct preservation, so it
works for unbounded complexes. The module helper constructs the equivalences explicitly;
no arbitrary data is selected from an unproved existence theorem.

## New nodes

`lem-pc-tensor-restrict-extend-module-natural`, in
`dag/nodes/sec-picard-framework/lem-pc-tensor-restrict-extend-module-natural.json`, records
the proved natural module comparison. It contains its full statement, the two tensor
induction argument, actual Mathlib searches, and the exact Lean signature.
No interface change record is needed: existing signatures and public imports are unchanged.


## Second reading by M2

1. Compared the existing module with the repository using `diff -u`. Its only changes
   are two plain proof imports and replacement of the theorem's `sorry` by a proof.
   The existing declaration signature, docstring, universe, visibility and original
   public imports are byte-for-byte unchanged. There are no changed definitions,
   target statements or forced adaptations. Verdict: pass.

2. Compiled both modules in import order through `lcompile.py --all`, including after
   removing the redundant import (2.9 and 3.0 seconds). There are no compiler errors
   or warnings, no `sorry`, no axioms or unsafe/opaque/extern/implemented_by declarations,
   and no definition chooses an unproved witness. In a scratch copy, `#print axioms`
   for `ModuleCat.exists_tensorRestrictExtend_module_natural` and
   `CochainComplex.nonempty_tensorRestrictExtendScalarsIso` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`. The existential module comparison is
   explicitly constructed from a proved linear equivalence. Verdict: pass.

3. No statements are split off with holes. Read the new module theorem and its node;
   it is a strictly smaller, fully proved module-level comparison, not a renamed
   complex theorem. Its two tensor inductions reduce naturality to B-linearity of f.
   Checked the inverse formula and balancing against Mathlib
   `TensorProduct.AlgebraTensorModule.cancelBaseChange` and its pure-tensor lemmas.
   For the identity ring map the formulas reduce to cancellation of the unit tensor;
   for zero modules or zero rings both maps are the unique maps of zero modules.
   No flatness or nonzero hypothesis is needed. Read the proof of
   [Stacks Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1): the stated tensor identity
   is its input for arbitrary complexes, without a K-flatness assumption on this
   identity itself. Independent LeanFinder search for a projection formula with
   naturality found adjunction ingredients only; Loogle `"cancelBaseChange"` found
   the equivalence already used and one-factor naturality. Searched the library and
   upstream sources for projection formulas, base-change tensor comparisons and
   cancellation; no existing simultaneous bundled comparison replaces the helper.
   Verdict: pass.

4. Read the bicomplex assembly downward from the target: the inner isoOfComponents
   uses naturality with f = identity and g = dK, and the outer one uses f = dL and
   g = identity. The symmetric direction of each equality is correct. The inverse
   of `HomologicalComplex₂.mapTotalIso` followed by `total.mapIso` has the target's
   direction. Read that existing source-library definition and Mathlib's restriction
   colimit-preservation instance: they handle arbitrary direct-sum total complexes,
   including unbounded ones and their differential signs. Both new proof imports
   are used. The helper's Tower import was redundant through ChangeOfRings and was
   removed. The original three public imports provide its statement's notions.
   The two removed direct proof dependencies are both listed in No longer needed;
   they remain dependencies of the module comparison. Read the unit record
   `sk-thm-picard-duality`: its realized statement and step lists are empty and no
   realized unit node is bypassed by this reduction. Verdict: pass.

5. Compared both node proof steps, proof_deps and proof_origin with the actual Lean.
   The parent's dependencies are the natural module comparison and the total tensor
   definition; the helper's are the existing Mathlib-backed scalar-extension and
   module-tensor definitions. Its new node has source, complete proof steps, searches,
   creation data, blueprint ancestry, chapter, unit and Lean attachment. Corrected
   its Lean statement field to reproduce the multiline signature verbatim. The
   existing node's only edited fields are permitted stage-3 fields. Verdict: pass.

Second reading changed only the redundant Tower import, the new node's verbatim Lean
signature, and this review/report. The mathematical proofs required no repair.
One original hole closed; zero new holes; no library module pruned.
