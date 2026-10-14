## What changed

Replaced the sorry in `affine_torsor_stabilizer_section_open` by a complete Lean
combination of two strictly smaller statements: the invariant principal open is
etale over Spec H, and the selected descended map is a monomorphism. Etaleness
of p follows from its factorization through j; the base equation and
`Etale.of_comp` give etaleness of f. `IsOpenImmersion.of_flat_of_mono` finishes.
The original signature, visibility, public imports and definitions are unchanged.
The two new modules are proof imports. The existing node now records this route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.affine_torsor_stabilizer_section_open`.
This is a decomposition, not a complete proof: one upper hole closed, two lower
holes added (net -1), with no other holes changed.

The two remaining holes, each the entire proof of its public theorem, are:

- `AlgebraicGeometry.Scheme.affine_torsor_invariant_puncture_etale`, node
  `lem-sbc-affine-torsor-invariant-puncture-etale`. It has no Y, splitting, label,
  or descended-map parameters; it concerns only the subgroup-invariant basic open.
- `AlgebraicGeometry.Scheme.affine_torsor_stabilizer_section_mono`, node
  `lem-sbc-affine-torsor-stabilizer-section-mono`. It proves only monomorphy and
  omits j, hj and every finite/etale assumption on the original target cover.

All three modules compile cleanly via lcompile.py. The new statements were checked
on K trivial, K = G and trivial G. Nonzero denominator excludes the empty source;
d = 0 gives no selected x. T need not be connected: its pullback to the connected
principal open is what is used. No inverse of the group order is assumed or needed.

## No longer needed

None of the original imports or modules is pruned: the original public imports
are needed by its unchanged statement. No existing DAG branch is declared unused.
The split-label laws remain needed by the monomorphy step and the original
statement, through the new node. No parent component-descent module is imported.
Unused `Mathlib.AlgebraicGeometry.Morphisms.Finite` imports were removed from the
two newly written modules before delivery; these were never library dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original node's sole proof dependency
supplies the label action, but does not state the subgroup quotient's etaleness
or its map's monomorphy. These are the two nontrivial geometric steps split off.
The existing proved `Scheme.GaloisCover.exists_connected_subgroup_quotient`
provides a scheme-theoretic quotient, useful for both remaining proofs, but does
not identify it with the displayed intersection-of-equalizers localization.
Using `AffineTorsorSingleStabilizerComponent` to prove this item would be circular.
LeanSearch returned Internal Server Error; LeanFinder, Loogle and source searches
worked. The local literature tree is absent; Tag 03SF was read on the official
Stacks site. The blueprint ancestor utility returned None for this created node;
the new nodes record their immediate source node rather than inventing an ancestor.

## New nodes

`lem-sbc-affine-torsor-invariant-puncture-etale`, in
`lean/Sheaf/AlgebraicGeometry/Morphisms/AffineTorsorInvariantPunctureEtale.lean`,
is the invariant-ring quotient etaleness step of the existing argument.

`lem-sbc-affine-torsor-stabilizer-section-mono`, in
`lean/Sheaf/AlgebraicGeometry/Morphisms/AffineTorsorStabilizerSectionMono.lean`,
is the exact-stabilizer injectivity/monomorphy step. It needs no global finite
etale target hypothesis because the given splitting already supplies the target
locally on the torsor. Both nodes have full Lean signatures, source and complete
proofs in words, and point to the already proved generic subgroup-quotient tool.
No change records or forced adaptations are required.

## Second reading by P4

1. Interface: PASS. Compared the item module against the repository with diff.
   Its existing declaration signature, visibility, docstring and public imports
   are byte for byte unchanged. Only three proof imports and the proof were added.
   The other two modules are new; there are no new definitions or change records.
2. Proof: PASS as a decomposition. Independently compiled all three modules in
   import order through lcompile.py, without errors or warnings. A scratch copy
   with #print axioms for all three theorems reports only propext,
   Classical.choice, Quot.sound and sorryAx. Exactly the two reported named
   helper theorems contain sorry; there are no forbidden declarations or data
   chosen from unproved existence. The final proof genuinely derives Etale f
   from the base equation and etale projection, then applies flat monomorphism
   openness. It does not claim that either remaining geometric step is proved.
3. New statements: PASS. Read both complete signatures and natural-language
   proofs against Stacks Tag 03SF and the concrete split-action definitions.
   The subgroup quotient is finite etale; invariants commute with localization
   at the fixed nonzero denominator. After the torsor base change, the exact
   stabilizer makes the coset-to-label map injective, so the selected map is
   a monomorphism. The missing global finite-etale target assumptions in the
   monomorphy lemma cause no gap: its pullback over the puncture is already
   split by delta. Checked K trivial, K = G, G trivial, d = 0, a unit denominator,
   and the excluded zero denominator. Neither helper merely renames the item:
   the first has no selected map, and the second asserts only monomorphy.
   Independent LeanFinder and Loogle searches and broader source rg searches
   found no exact replacement. The upstream TotallySplit module does provide
   AlgHom.finite_and_etale_fixedPoints, AlgHom.tensorFixedPointsEquiv and
   AlgHom.surjective_comap_fixedPoints_val_and_iff; these are useful additional
   ingredients for the remaining localization and quotient compatibility work.
   They were missed by the first source search and do not immediately close
   either helper in a few minutes.
4. Route and pruning: PASS. The top proof takes the direct etale-plus-mono
   route using Mathlib. All added item imports are proof-only and used. Existing
   public imports support the unchanged signature. The old direct dependency
   lem-sbc-affine-torsor-split-label-laws is now used through the monomorphy
   helper and still supports the statement; it is not pruned. The unit record
   sk-prop-input-spreading has empty realized entries; this delivery changes
   none of them and replaces no unit step. No module is claimed pruned.
5. Nodes: PASS. Matched every Lean signature to its node record and checked
   proof_deps against the union of proof-step uses. The item records the two
   actual helper applications and elementary Mathlib steps. New nodes have
   sourced proof plans, creation and blueprint records, search evidence, the
   same chapter/unit, and verbatim Lean signatures. Their subgroup-quotient
   dependency is the proved generic tool, not the parent component theorem.

Second reading changes: added this independent review and additional source-search
results to the two new nodes. No Lean proof or statement repair was necessary.
One original hole is closed by two new holes: decomposition, net minus one;
zero original holes have been closed without remaining geometric obligations.
