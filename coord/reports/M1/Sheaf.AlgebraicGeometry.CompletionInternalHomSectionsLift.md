## What changed

Proved `AlgebraicGeometry.completion_internal_hom_sections_lift` from the new affine
comparison theorem in `Sheaf.AlgebraicGeometry.CompletionInternalHomAffineSectionsLift`.
The existing theorem's signature and docstring are unchanged. No definition or existing
public interface changed.

The item's module contains a complete private descent proof for an arbitrary diagram
of sheaves of modules and arbitrary evaluation morphisms. It first proves equality of
sections after affine refinement and that affine opens cover the terminal object.
Local uniqueness then proves restriction compatibility of the entire inverse-limit
families, including all transition maps. Sheaf separatedness gives agreement over
arbitrary intersections; `existsUnique_section` glues every level. Finally,
`CoversTop.sections_ext` proves global transition compatibility, evaluation, and uniqueness.
The final proof transports the section equality through `homObjSectionsEquiv`.

Updated the item's DAG proof to this route. Added one affine comparison module and node,
carrying exactly the affine algebra portion (old steps 1–3), with source and a complete
proof in words. Both sandbox modules compile with `lcompile.py`; the item has no `sorry`.

## Proved and sorry left

Closed: `AlgebraicGeometry.completion_internal_hom_sections_lift`
(node `lem-weil-pbc-completion-internal-hom-sections-lift`), 1 of 1 original holes.

Added and left: `AlgebraicGeometry.completion_internal_hom_affine_sections_lift`
(node `lem-weil-pbc-completion-internal-hom-affine-sections-lift`), exactly one whole-proof
`sorry` in its own module. It asserts lifts only on a specified affine open; it asserts
neither global sections nor compatibility between different opens. The nontrivial descent
from this local statement to the original global statement is completely proved here.
This delivery is a decomposition, with one hole closed and one added (net zero), rather
than a completed proof of the affine comparison. There are no other holes in the delivery.

Reviewed the new statement's edge cases mathematically: the unit ideal gives zero
quotient modules and the unique zero family; the zero ideal gives the ordinary internal
Hom section correspondence; the empty affine open has unique sections; positive levels
are consistently `n.unop + 1`. The statement uses uniqueness of the entire compatible
family and never asserts that an individual finite-level evaluation map is bijective.
No object is defined by choosing an arbitrary witness of an admitted existence theorem.

## No longer needed

Removed direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.CompletionInternalHomQuotient`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`
- `Sheaf.AlgebraicGeometry.CoherentSheafHom`
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
- `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`
- `Mathlib.Algebra.Module.FinitePresentation`

These dependencies are transferred to the new affine-comparison module and node, where
their statements are needed for the remaining proof plan. They are not claimed as globally
pruned. No mathematical dependency or unit-route step has been removed from the targets'
import closure; globally pruned modules/nodes: none. Both existing public imports stay.
The global descent now directly imports the affine comparison, `CoversTop.Basic`, and
`Topology.Sheaves.Sheaf`.

## Where the brief, the DAG or earlier work was wrong

The planned affine comparison was not already a usable declared theorem: its listed
lemmas give the ingredients, but applying them requires transporting sheaves, quotient
sections, and morphisms through the affine equivalences and checking the evaluation map.
That genuine remaining part is isolated as the new node; the global sheaf argument is
proved, rather than bundled into another restatement of the original theorem.

The source file `literature/stacks-project/coherent.tex` is absent on this machine.
Read the published source at https://stacks.math.columbia.edu/tag/0882; it gives exactly
the affine-local reduction and the completion/tensor/Hom chain used in the local node.
LeanSearch returned HTTP 500; it is recorded as unavailable, not evidence of absence.
No statement was disputed or changed, and the blueprint unit's route is preserved.

## Second reading by M1

1. Compared the delivered sections-lift module with the repository version. The theorem
   signature and all existing declarations are unchanged; only proof imports, private
   helpers, and the proof body differ.
2. Compiled both delivered modules with `lcompile.py`; the sections-lift theorem has no
   `sorry`, and the only remaining `sorry` is the named affine comparison theorem. No
   forbidden declarations occur. The remaining `sorry` is documented and has its DAG node.
3. Checked the affine comparison statement against its use and edge cases. It is a strict
   local reduction: it quantifies over one specified affine open and does not restate the
   global target. Its hypotheses and conclusion are exactly what the gluing helper needs.
4. Checked the proof route and pruning. The global proof uses the affine node, sheaf
   separatedness, affine basis covers, and section gluing; the removed imports are no
   longer needed directly. The unit route through affine comparison and global gluing is
   preserved.
5. Checked the DAG records: the existing node's proof and dependencies match the actual
   helper and affine theorem used, and the new affine node records its source, statement,
   proof plan, and Lean declaration.

Changed only this report by adding this review record; no Lean statements or definitions
were altered.

## New nodes

`lem-weil-pbc-completion-internal-hom-affine-sections-lift`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-completion-internal-hom-affine-sections-lift.json`,
declaring `AlgebraicGeometry.completion_internal_hom_affine_sections_lift` in
`lean/Sheaf/AlgebraicGeometry/CompletionInternalHomAffineSectionsLift.lean`.
It is the affine portion of the old proof, strictly before global gluing. Its module
retains the old affine proof dependencies. No existing interface changes or forced
adaptations; no change record is needed.
