## What changed

Added the intermediate module-sheafification theorem and used it to combine the affine-open
section comparison with the sheaf-level derived direct-image comparison. The target theorem now
has a complete proof from that strictly smaller intermediate statement and the existing section
comparison theorem.

## Proved and sorry left

Proved `AlgebraicGeometry.qcoh_acyclic_derived_pushforward_cohomology` by composing the two
isomorphisms supplied by `qcoh_acyclic_derived_sections_comparison` and the new gluing theorem.
Closed one local hole: `AlgebraicGeometry.qcoh_acyclic_derived_pushforward_cohomology`.
Added one hole: `AlgebraicGeometry.module_sheafification_iso_of_affine_restriction`.
This is a decomposition (one hole closed, one added), not a net proof or an axiom-free target.
The existing imported `AlgebraicGeometry.qcoh_acyclic_derived_sections_comparison` is still open.
The new theorem `AlgebraicGeometry.module_sheafification_iso_of_affine_restriction` remains a
named `sorry`, with node `lem-sc-module-sheafification-affine-restriction`.

## No longer needed

No module imports were removed and no modules are claimed pruned. The old direct
proof dependencies `def-pc-derived-direct-image` and `def-weil-pbc-sheafification`
were removed from the item node: the former remains needed for the signature, and the
latter is now used through the new gluing node. Neither is claimed globally unnecessary.
The affine acyclicity details are supplied by the existing section-comparison theorem.

## Where the brief, the DAG or earlier work was wrong

The DAG plan omitted a Lean statement for the affine-basis sheafification and gluing argument;
it is split off as the new intermediate node above. The target statement itself is unchanged.

## New nodes

`lem-sc-module-sheafification-affine-restriction` records the affine-basis sheafification lemma
needed by the proof; its Lean module is
`Sheaf.AlgebraicGeometry.ModuleSheafificationAffineRestriction`.


## Second reading by C3

1. PASS. Diffed the existing item module against the repository: its declaration signature
   is byte for byte unchanged; the only changes are its proof and a plain proof-only import.
   The other module and node are new. No definitions or target statements were changed.
2. PASS as a decomposition. Compiled both modules in import order with lcompile.py; no
   errors or warnings. Read every declaration: the only local sorry is the named gluing
   theorem listed above; there are no definitions, arbitrary witness constructions, or
   forbidden axiom/unsafe/opaque/extern mechanisms. Scratch #print axioms for both
   declarations reports propext, Classical.choice, Quot.sound and sorryAx only.
3. PASS. The split is a strictly smaller, purely sheaf-theoretic part of the argument,
   with no derived categories, morphism acyclicity or cohomology conclusion. Checked
   the empty scheme/open, empty parameter category, zero modules, and arbitrary affine
   overlaps: refine overlaps by affine opens, with no separatedness assumption on Y.
   Its docstring gives the extension, module linearity, factorization, stalk criterion
   and naturality arguments. Verified the sources at
   [Tag 009U](https://stacks.math.columbia.edu/tag/009U) and
   [Tag 0089](https://stacks.math.columbia.edu/tag/0089). Independent searches using
   basis agreement, dense restriction, and TopCat.Sheaf.restrictHomEquivHom found
   useful underlying-map lemmas but no duplicate of this module-valued comparison.
   Also searched lean/Sheaf, lean/WeilConjectures and the upstream source. Formalizing
   the module extension and its invertibility is substantial, so the split stays open.
4. PASS after report repair. The target uses the existing section comparison and the
   smaller gluing statement, composing the inverse pushforward comparison in the correct
   direction. Each public import of the new module is needed in its signature; the two
   item proof imports are plain imports. No removable import was found. The unit
   sk-thm-picard-duality has empty realized statement/step lists; its route is unchanged.
   Corrected No longer needed to list both removed direct DAG dependencies, without
   claiming their modules globally pruned.
5. PASS after metadata repair. The item's proof_deps are exactly the two theorems used
   by the Lean proof. The new node has its source, full statement, Lean record, searches,
   creation provenance, blueprint ancestry, unit and chapter, and a matching docstring.
   Corrected its proof_origin from sites.tex Tags 009H/0088 to sheaves.tex Tags 009U/0089.
   Marked the item's gluing step non-elementary since it invokes the new theorem.

Second reading changed only the report and DAG metadata; the Lean proof was retained.
