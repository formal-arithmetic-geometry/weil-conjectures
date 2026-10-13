## What changed

Repaired the returned duplicate `CategoryTheory.resolutionSES`: removed the local
copies of `resolutionSES`, `resolutionOfExact`, and `homologyZeroIso` and added
`import all Sheaf.Paper.TorLongExactFirstVariable`. Lean resolves the existing
private helpers through this proof-only import; no visibility or signature of
any existing declaration changed. Updated the parent DAG proof metadata to name
the existing theorem's module and node.

The existing kernel inclusion remains fully proved using the fully proved
`CategoryTheory.tor_kernel_boundary_horseshoe_comparison` in the new comparison
module, homology exactness, and transport through the Tor isomorphisms.
Both delivered modules compile through `lcompile.py --all` without warnings.

## Proved and sorry left

Closed the one existing hole in
`CategoryTheory.tor_kernel_boundary_construction_exact_left_kernel`
(node `lem-sc-p1-tor-kernel-boundary-construction-exact-left-kernel`).
Added zero holes. The new
`CategoryTheory.tor_kernel_boundary_horseshoe_comparison`
(node `lem-sc-p1-tor-kernel-boundary-horseshoe-comparison`) is fully proved.
There are no `sorry`s in either delivered module and none were split off.

## No longer needed

Removed the duplicate local resolution and degree-zero homology helpers.
Removed the direct proof import `Sheaf.Algebra.Homology.FreeResolutionSesSplit`:
the existing `resolutionSES` supplies that construction. The horseshoe node
`lem-weil-pbc-free-resolution-ses-split` remains needed transitively through
`Sheaf.Paper.TorLongExactFirstVariable`, so it is not globally pruned.

Removed redundant direct imports:
`Mathlib.Algebra.Homology.HomologicalComplexAbelian`,
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`,
`Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed`, and
`Mathlib.CategoryTheory.Monoidal.Closed.Braided`.
The earlier proof draft's `Mathlib.Algebra.Homology.HomologySequenceLemmas`
import is also unnecessary. These results are available through the imports
retained by the proof. No project node or module becomes globally unnecessary.
The unit's realized statement and proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The first delivery copied a theorem already stated word for word in
`Sheaf.Paper.TorLongExactFirstVariable`. Its description as reuse was inaccurate:
it duplicated the proof. The repair imports and applies the original private
theorem using Lean's `import all` instead. The previous second reading overlooked
this duplication and must be renewed after this repair.

## New nodes

`lem-sc-p1-tor-kernel-boundary-horseshoe-comparison` records the fully proved
signed comparison step. It proves equality of connecting maps, strictly below
the desired kernel inclusion, and contains no holes. No new node was added by
this repair. No change record is needed: no existing interface changed and no
forced adaptation was necessary.

## Second reading by T1

1. Compared the item's complete diff against the repository. The existing theorem
   signature is byte-for-byte identical; its sole sorry is replaced by a proof.
   The comparison module is new. No existing definition, visibility, statement,
   or target changes, and no forced adaptation or change record is needed. PASS.
2. Compiled both modules in import order with lcompile.py, without errors or
   warnings. Scratch copies with #print axioms show exactly propext,
   Classical.choice, and Quot.sound for both public theorems, with no sorryAx.
   Neither delivered file contains sorry or forbidden declarations. The reused
   resolutionSES is proved from the constructed free-resolution theorem; the
   chosen splittings are supplied hypotheses, not data from an unproved existence
   theorem. PASS.
3. There are no statements left sorry or split-off holes. Read the new, fully
   proved comparison theorem and its node: it is a signed equality of maps,
   strictly part of the original kernel-inclusion argument. Checked the sign
   against Mathlib's ShortExact.δ_apply and the identity D + t εA = dP k.
   Zero modules, q equal to the identity, q with zero target, and characteristic
   two introduce no exceptional divisions or sign assumptions. Independent
   leanfinder search for connecting morphisms computed from lifted cycles and
   loogle search for δ_apply returned generic snake/homology formulas, already
   used here; rg across the existing Tor construction, naturality, and exactness
   modules found no signed comparison to reuse. PASS.
4. Read the proof from the kernel inclusion down to the comparison. The existing
   private resolutionSES and homologyZeroIso are genuinely reused through a
   proof-only import all; no duplicate helpers remain. The shorter existential
   Tor exact-sequence theorem does not identify the fixed constructed boundary.
   Retained public imports supply the signatures (including HomologySequence for
   hS.δ); ConcreteCategory supplies δ_apply and ShortComplex.ModuleCat supplies
   its PreservesHomology instance. Both parent imports beyond the construction
   are proof-only. The old proof dependency
   lem-weil-pbc-free-resolution-ses-split is replaced as a direct dependency by
   lem-weil-pbc-tor-long-exact-first-variable, but stays used transitively by its
   resolutionSES; all other old dependencies remain. Thus no project module or
   node is globally pruned. Read dag/units/sk-thm-picard-duality.json: neither
   this item nor the helper replaces a realized statement or step, and realized
   is unchanged. PASS.
5. Compared the existing node: only proof, proof_deps, and proof_origin change.
   For both nodes, the Lean signature matches lean.statement verbatim and the
   union of proof-step uses equals proof_deps. The new node has its source,
   complete lift/sign argument, searches, creation metadata, blueprint parent,
   chapter, unit, status, and Lean record. The proof metadata follows the actual
   reuse, sign calculation, homology exactness, and Tor transport. PASS.

Second reading changed only this report: recorded independent checks and made
explicit which old direct dependency was replaced but remains needed transitively.
No Lean repair was necessary. One old hole is closed, zero holes are added, and
none are split off; the additional comparison theorem is fully proved.
