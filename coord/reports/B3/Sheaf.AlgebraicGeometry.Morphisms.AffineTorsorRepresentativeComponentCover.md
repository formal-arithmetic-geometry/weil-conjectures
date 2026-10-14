## What changed

Kept the signature of `AlgebraicGeometry.Scheme.affine_torsor_representative_component_cover`
unchanged and replaced its sorry with a compiling proof. Added the proof-only import
`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorComponentImageOrbit`.

Added `AffineTorsorSplitPointLifting`: `fixedSplitSectionOver` is the actual pullback lift
of the explicit split section and its structural map, using the proved named compatibility
lemma `fixedSplitSectionOver_compat`. Its point-lifting theorem is completely proved from
Mathlib. Pull back Spec C over the second projection, lift its map into D(h) using the
factorization through D(g), read the coproduct label, and use a second pullback of that
coproduct immersion to obtain the equality of points. This avoids assuming that the
underlying points of a scheme pullback form the set-theoretic fibre product.

Added `AffineTorsorComponentImageOrbit`: the remaining geometric step describes one
component image by its orbit, without a family, completeness, or distinctness. The item
combines point lifting and this criterion: completeness supplies a covering component;
two memberships give alpha and beta with the same label, so beta inverse times alpha
carries one representative to the other, and distinctness forces equality.

Updated the parent node's proof route and added nodes for both new modules. No existing
statement, definition, visibility, or public import changed. No forced adaptations.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.affine_torsor_representative_component_cover`
(node `lem-sbc-affine-torsor-representative-component-cover`).

Added and fully proved `AlgebraicGeometry.Scheme.fixedSplitSectionOver_compat` and
`AlgebraicGeometry.Scheme.affine_torsor_split_point_lifting`
(node `lem-sbc-affine-torsor-split-point-lifting`). The accompanying section definition
contains no sorry and chooses no data from an unproved existence theorem.

One new sorry remains: `AlgebraicGeometry.Scheme.affine_torsor_component_image_orbit`
(node `lem-sbc-affine-torsor-component-image-orbit`). This is a decomposition, not a
sorry-free proof: one upper hole closed and one strictly single-component hole added.
The main theorem still transitively uses this sorry. No other holes are added.

Edge checks: d=0 makes the image lemma's x binder empty; proved point lifting then
forces the base-changed scheme to have no points. The main proof also handles m=0
without a nonemptiness assumption. For G trivial the image criterion selects one
label. For K=G it selects the entire orbit of x. The second-base section is a
morphism built by pullback.lift, not a pair of underlying points.

## No longer needed

None. All original imports remain needed for the public signature or explicit action.
The action node remains used. Neither the single-stabilizer existence module nor the
parent orbit-component-descent module is imported; they depend in the other direction
and cannot be used as shortcuts. No existing node or module is pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The parent DAG cited only the label-action laws for a step which also needs geometric
lifting and an orbit-image argument. The laws supply the final permutation calculation,
but do not state the component-image criterion. Both missing steps now have modules
and nodes, and point lifting is fully proved.

Searches used LeanFinder, Loogle, LeanSearch (service returned Internal Server Error),
and ripgrep in Mathlib, Sheaf, WeilConjectures, and the DAG. Abstract Galois-category
quotient/stabilizer lemmas do not identify these particular invariant-ring scheme maps;
Mathlib's faithful-flat surjectivity, pullback range, and coproduct cover API do close
the point-lifting step. Read Stacks Tag 03SF for the Galois-cover interpretation. The
unit's statement and route are preserved; its `realized` lists contain no node being
bypassed here. No claim is made that the remaining orbit-image argument is formalized.

## New nodes

`lem-sbc-affine-torsor-split-point-lifting` records the explicit second-base section
and its fully proved point-lifting theorem in
`lean/Sheaf/AlgebraicGeometry/Morphisms/AffineTorsorSplitPointLifting.lean`.

`lem-sbc-affine-torsor-component-image-orbit` records the single-component orbit
membership criterion in
`lean/Sheaf/AlgebraicGeometry/Morphisms/AffineTorsorComponentImageOrbit.lean`.
Its docstring gives the geometric-fibre argument and the invariant-ring integrality
argument. This is strictly a part of the original proof: it contains no family,
no completeness or distinctness hypotheses, and neither coverage nor disjointness
conclusion. There are no change records because all existing signatures are unchanged.

## Second reading by B3

1. Compared the delivered item module against the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof and a proof-only import changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. There are no errors, forbidden declarations, or sorries except the named `affine_torsor_component_image_orbit` split-off theorem. The point-lifting theorem and compatibility lemma are fully proved. Verdict: pass.
3. Checked the two new statements against their DAG nodes, docstrings, and source argument. Point lifting is a strict lower-level lemma; the component-image theorem is the remaining single-component geometric reduction and is strictly weaker than the parent conclusion. The split theorem is explicitly named and documented. Verdict: pass, with one intentional split-off sorry.
4. Checked proof dependencies and pruning. The parent proof uses point lifting, the component-image criterion, and the existing label-action laws; no original import or node is unused. The unit route and `realized` records are preserved. Verdict: pass.
5. Checked the DAG Lean records and proof routes against the actual declarations and imports, including the new modules and node metadata. No forced adaptations or statement changes are present. Verdict: pass.

Changed after second reading: added this review section to satisfy the stage-3 report contract; no Lean code or DAG content required repair.
