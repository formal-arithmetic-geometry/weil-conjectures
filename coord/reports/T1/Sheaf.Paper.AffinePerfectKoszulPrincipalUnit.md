## What changed
Split `AlgebraicGeometry.affine_perfect_koszul_principal_unit` into its perfectness and
principal-open isomorphism conjuncts in two dedicated modules, and combine them by
conjunction. The existing theorem signature and public imports are unchanged.
Removed redundant proof imports of `Sheaf.Paper.KoszulComplex` from all three files
(the statements already see it through `ShiftedKoszulAugmentation`), and removed the
unused public `PerfectComplex` import from the new isomorphism module.

## Proved and sorry left
Closed the body hole of `AlgebraicGeometry.affine_perfect_koszul_principal_unit`.
Added two named holes:
- `AlgebraicGeometry.affine_perfect_koszul_principal_unit_perfect`, node
  `lem-sc-affine-perfect-koszul-principal-unit-perfect`;
- `AlgebraicGeometry.affine_perfect_koszul_principal_unit_iso`, node
  `lem-sc-affine-perfect-koszul-principal-unit-iso`.

This is a decomposition, not a sorry-free proof: one hole closed, two added, net -1.
The parent still depends on `sorryAx` through both helpers. No data definitions changed
or were added. All three files compile; explicit `#print axioms` probes list only
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for each declaration.

## No longer needed
Removed the redundant direct `Sheaf.Paper.KoszulComplex` import from the parent and
both helpers. Removed `Sheaf.AlgebraicGeometry.PerfectComplex` from the new iso helper.
The old parent proof dependencies `def-pc-perfect-complex` and
`def-weil-pbc-koszul-complex` are replaced as direct dependencies by the two component
nodes; both old dependencies are still used in the component plans and needed in the
import closure. No DAG node or module is pruned from the targets' closure.

## Where the brief, the DAG or earlier work was wrong
The first version omitted complete natural-language proofs from the helper docstrings,
used the placeholder statement “Intermediate conjunct of parent theorem” in both new
nodes, and copied a circular proof plan into both nodes (each depended on itself and
the other helper). These were repaired. The parent node incorrectly called the helpers
proved: it now explicitly describes the open decomposition. The old split-report
metadata copied into the new nodes described a previous unsplit version and was removed.

## New nodes
`lem-sc-affine-perfect-koszul-principal-unit-perfect` isolates bounded finite-free
perfectness, with a self-contained statement, source, complete proof plan and Lean record.
`lem-sc-affine-perfect-koszul-principal-unit-iso` isolates the localized contracting
homotopy and open-cover conclusion, with the same required records. No change record
is required because existing statements, definitions and visibility are unchanged.

## Second reading by T1
1. Compared the parent module with the repository using `diff`: the existing signature
   is byte-for-byte unchanged; only proof-only imports and its body differ. The new
   modules add exactly the two conjuncts with identical binders, without additional
   hypotheses or weakened conclusions. No existing definition or public import changed.
2. Compiled each module in import order via `lcompile.py`, successfully. Inspected every
   declaration: no forbidden constructs or hollow definitions; exactly the two listed
   named `sorry` theorems remain. Scratch `#print axioms` copies compiled and showed only
   the standard three axioms and `sorryAx`; scratch sources were removed.
3. Checked both component statements against the concrete exterior-power complex and
   augmentation. The wedge bases give finite-free terms; the inverse-generator wedge
   homotopy gives localized acyclicity. Checked `r=0` (zero deleted complex and empty
   union), `r=1` (multiplication by a unit), zero equations (empty union), and the zero
   ring (empty spectrum). Added complete docstring proofs. LeanSearch calls were recorded as unavailable (Internal Server Error); no mathematical
   verdict is claimed for that service. Independent msearch calls
   used leanfinder (truncated finite Koszul bounded finite-free complex), loogle
   (`CategoryTheory.IsIso`), and grep (contractibility/exterior freeness). Local `rg`
   also found affine strict-model and Koszul cone infrastructure, but no duplicate
   component theorem or short complete route. The two holes are strictly separate
   conjuncts, not a renamed copy of the complete conjunction.
4. Read the old plan and its dependency declarations (`PerfectComplex`, `KoszulComplex`)
   and `ShiftedKoszulAugmentation`. The finite-projective affine strict-model theorem
   still requires boundedness and termwise projectivity inputs; the other Koszul-open
   cohomology core calls the parent, so using it would be circular. Removed redundant
   imports. `dag/units/sk-thm-picard-duality.json` has empty `realized.statement` and
   `realized.steps`; no realized unit node is bypassed. The source route remains finite
   freeness, localization homotopy, and open-cover detection.
5. Checked the parent Lean proof against its two dependencies and corrected both new
   nodes' self/cross dependencies to the actual component plans. New nodes now have
   self-contained statements, three search records, provenance, source, creation,
   blueprint, chapter/unit and verbatim Lean statements. Parent `proof` no longer
   describes open helpers as proved. All remaining DAG metadata agrees with the code.

Changed in this second reading: complete helper docstrings; self-contained node
statements; acyclic component proof plans and accurate parent description; search
records; redundant imports; explicit decomposition accounting and this review report.
