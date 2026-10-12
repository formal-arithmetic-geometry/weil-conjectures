## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.exists_higherDirectImage_limit_fiber_eq_zero`
with a complete Lean reduction to affine-section vanishing. The proof represents a fiber
class by a section, shrinks a zero germ using the filtered fiber equality criterion,
refines to a pointed affine etale object using the cover-dense affine site, applies the
local vanishing statement, and returns to the original germ by naturality.

Added `Sheaf.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing` for the remaining
local cohomology and finite-cover argument. Its docstring gives the full argument with
its source. Both files preserve module-system headers and the original item's signature.
The new statement was checked on empty affine objects, degree zero, constant diagrams,
and a non-qcqs base: only the etale neighborhood needs to be affine.

## Proved and sorry left

`AlgebraicGeometry.Etale.exists_higherDirectImage_limit_fiber_eq_zero` has no sorry in
its proof. This is a reduction, not yet a sorry-free transitive proof.

The only sorry added or left in the delivered files is
`AlgebraicGeometry.Etale.exists_higherDirectImage_affine_section_eq_zero`
(node `sbc-lem-higher-direct-image-affine-section-vanishing`). It concerns sections on
an affine etale object, with vanishing before taking germs. The item's representation,
shrinking, affine refinement, and return-to-germs argument is proved.
Both delivered modules compile cleanly using lcompile.py.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf` and
`Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit`; these two nodes are retained as
proof dependencies of the new local statement, so neither module is globally pruned.
Replaced them by a proof import of the new module and
`Mathlib.AlgebraicGeometry.Sites.AffineEtale`. No original node is no longer needed.
The new module does not import the etale point module, which its statement does not use.

## Where the brief, the DAG or earlier work was wrong

The supplied route is mathematically consistent, but its cited presheaf theorem provides
only existence of an isomorphism; it does not expose naturality for
`abelianHigherDirectImageMap` or its identification with restricted cohomology on
base-changed neighborhoods. The continuity theorem is stated for qcqs schemes and
complex systems, rather than the relative system and sheaf sections here. These
local comparison and finite-cover steps remain in the new theorem, not as silent glue.
The module-coefficient affine continuity lemma found in the library applies to a sheaf
pulled back from a fixed scheme and does not cover the varying abelian sheaf system.

The local Stacks tex is absent in this read-only clone. Read the authoritative online
proof of Tag 09Z1 at https://stacks.math.columbia.edu/tag/09Z1 instead. Mathlib searches
were run through the prescribed wrapper; LeanSearch returned HTTP 500, recorded as
unavailable. LeanFinder returned structure-sheaf limit results, and grep found no match.
The blueprint search for higher direct images found the existing module-coefficient
local continuity node, but no corresponding varying abelian affine-section statement.
The unit's route is retained: the original two cohomology dependencies stay below the
new local node. Its unit has no populated realized entries to bypass.

## New nodes

`sbc-lem-higher-direct-image-affine-section-vanishing` records vanishing on an affine
etale object before taking a fiber. Its Lean module is
`lean/Sheaf/AlgebraicGeometry/HigherDirectImageAffineSectionVanishing.lean`. It carries
the local higher-image comparison, base-changed complex continuity, and finite-cover
assembly. The existing item node now records the proved point-fiber reduction to it.
No definition, existing statement, public import, or change record was changed.

## Second reading by J1

1. Compared the existing module against the read-only repository with diff. The only
   changes are two proof imports and the proof body; the full existing signature,
   definitions, docstrings, and public imports are byte for byte unchanged. There
   are no adapted declarations or change records. Verdict: pass.
2. Both delivered modules compile locally. Inspected every proof step: representation
   of the germ, shrinking the zero germ, pointed affine refinement, and naturality
   back to the original germ are genuine Lean arguments. The sole textual sorry is
   the whole proof of the named affine-section theorem. No forbidden declarations
   or hollow definitions occur. Explicit axiom checks are recorded below.
3. Read the new theorem, its node, and Stacks Tags 09Z1 and 03Q8. The finite-cover
   argument is sound: affine etale members are qcqs; base changes of the qcqs
   structure maps to these members are qcqs schemes, with affine transitions;
   continuity kills each representative, and finitely many indices have a common
   upper bound. Empty affine objects have zero sections; p = 0 uses sections;
   constant diagrams reduce to filtered sheaf colimits. S need not itself be qcqs.
   This is a strict local part of the argument (no point or fiber), not a renaming
   of the item's conclusion. LeanFinder, Loogle, and alternate repository searches
   found no theorem closing the varying abelian relative comparison. The module
   section-colimit theorem assumes a colimit already and the upstream higher-image
   theorem fixes a pulled-back ModuleCat sheaf. Verdict: pass; one split remains.
4. The proof first uses Mathlib point and affine-site APIs, then the local theorem.
   The item's original two dependencies remain below that theorem; none is globally
   pruned. All public imports serve signatures, and proof imports are plain imports.
   The unit sk-lem-failure-field has empty realized statement and step entries; its
   route is preserved through the original cohomology dependencies. Verdict: pass.
5. The item node describes exactly the proved fiber reduction; the new node describes
   the remaining affine comparison and finite-cover assembly. Its statement matches
   Lean, its proof_deps are the union of step uses, and source, creation, blueprint,
   chapter, unit, searches, and Lean records are present. Verdict: pass.

Second-reading repair: added plain imports of AbelianHigherDirectImagePresheaf and
EtaleComplexCohomologyLimit to the new affine-section module so its imports expose
its recorded proof plan. Added independent search evidence to the new node. No
proof, existing signature, or definition needed repair.

Explicit scratch-copy #print axioms checks for both the affine-section theorem and
the item returned exactly propext, Classical.choice, Quot.sound, and sorryAx.
The item is therefore proved as a reduction, with its transitive local proof open.
