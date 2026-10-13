## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.injective_restrictAdjunction_unit_app_of_depth_one`
with a complete Lean reduction. Its statement and public imports are unchanged.
Added proof-only imports of `Mathlib.RingTheory.Regular.IsSMulRegular` and
`Sheaf.AlgebraicGeometry.Morphisms.AffineSectionAssociatedStalk`.

The private `depth_zero_of_maximal_associated` is proved directly from the
regular-sequence depth definition, Nakayama, and Mathlib's associated-prime
zerodivisor criterion. Affine injectivity follows by detecting unequal sections
at an associated stalk and ruling out such a boundary stalk by positive depth.
Naturality of the unit transfers equality to affine opens; germ compatibility
and sheaf separatedness then prove injectivity on every open.

Added one module with one strictly smaller remaining theorem: affine sections
are detected at associated stalks. It has no open U or depth hypothesis and
asserts a local witness, not restriction injectivity. Its docstring gives the
cyclic submodule proof. The node records the existing affine tilde/Gamma,
localization, and algebraic detection declarations for the next worker.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.injective_restrictAdjunction_unit_app_of_depth_one`
(node `lem-sbc-depth-one-restriction-injective`). The item's module has no sorry.
The private `depth_zero_of_maximal_associated` is fully proved.

Added exactly one hole:
`AlgebraicGeometry.Scheme.exists_associated_stalk_germ_ne_of_isAffineOpen`
(node `lem-sbc-affine-section-associated-stalk`), in the new module
`Sheaf.AlgebraicGeometry.Morphisms.AffineSectionAssociatedStalk`.
This is a decomposition: one upper hole closed, one strictly smaller hole added,
net zero holes. The positive-depth algebra and arbitrary-open gluing are proved.

The zero module and empty affine open make the new lemma's unequal-section
hypothesis impossible. For nonzero sections the cyclic-submodule proof supplies
an associated prime where the difference survives. No nonempty U hypothesis is
used: with U empty the original depth assumption forces the module to be zero.
U equal to the whole scheme has no boundary condition, and restriction is injective.

## No longer needed

No existing imports, nodes, or modules were pruned. The item initially had no
proof-dependency imports or proof dependency nodes. No structure-sheaf-only
associated-point lemma was imported: those statements do not cover N.
The new affine lemma packages the original plan's affine image-submodule step;
the unit route in `sk-prop-input-spreading` is preserved (its realized list is empty).

## Where the brief, the DAG or earlier work was wrong

The node's three proof steps had empty `uses` lists. There was no recorded Lean
interface for the affine section-detection step; the new node supplies it.
There is no statement correction or forced adaptation.

Searched Mathlib and both library roots for restriction/depth and
associated-prime/germ detection. LeanFinder and Loogle returned stalk criteria
and algebraic association tools, not the desired sheaf theorem. LeanSearch was
unavailable (Internal Server Error); grep found the existing algebraic
localization and tilde/Gamma tools recorded in the new node. Read Stacks Tags
0B3M, 05AR and 00LL at their official pages because the local Stacks files are
absent on this machine.

The new node uses existing algebraic and affine-localization nodes from other
units as tools; no existing node of this unit states those general interfaces.
The maintainer may record those tool uses as required by the route checker.

## New nodes

`lem-sbc-affine-section-associated-stalk`: for a finite quasi-coherent module
on an affine open of a locally Noetherian scheme, unequal sections have unequal
germs at a point whose stalk has associated maximal ideal. This is the affine
cyclic-image step of Stacks 0B3M, independent of an open complement and depth.
Its module, source, complete proof in words, searches, and Lean record are
included. No change records are needed.

## Second reading by J4

1. Compared both delivered modules with the repository (the affine module is new).
   The existing theorem signature and docstring are byte for byte unchanged;
   existing public imports are unchanged. No definition or existing public statement
   was altered, and no change record is needed. Restored one extra space before
   the existing theorem's proof delimiter.
2. Compiled both modules locally with lcompile.py in import order: no errors or
   warnings. Independently compiled scratch copies with #print axioms for the
   private depth lemma and both public theorems. The private lemma uses only
   propext, Classical.choice and Quot.sound; the public theorems additionally
   use sorryAx through the one reported affine hole. No forbidden declaration,
   hollow definition, or unreported sorry occurs. Scratch copies were removed.
3. Read the affine lemma's statement, full cyclic-submodule proof and node.
   It is true: an associated prime of the nonzero cyclic submodule detects its
   generator, hence the original difference, and remains associated after
   localization. Empty affine opens and zero modules admit no unequal sections;
   over a field the sole point detects every unequal pair. This is strictly
   smaller than restriction injectivity: no U, boundary depth or gluing occurs.
   Repeated LeanFinder, Loogle and grep searches with different queries and
   searched both Lean roots. Found no duplicate sheaf result. The existing
   algebraic product-localization and associated-prime-localization declarations
   are tools, not replacements. Checked the cited argument at
   https://stacks.math.columbia.edu/tag/0B3M and
   https://stacks.math.columbia.edu/tag/05AR. The remaining affine dictionary
   work cannot be closed by a short application of the search results.
4. Reviewed the proof from the restriction theorem downward: affine detection,
   the direct regular-sequence depth-zero contradiction, naturality, and sheaf
   separatedness implement the stated route. The similar depth-zero helper in
   DepthLeDimAssociatedPrime is private and cannot be reused. Both added imports
   are proof-only; the new module's imports supply its public signature and
   required stalk instances. No old proof dependency was dropped: the original
   proof_deps list was empty. The unit's realized lists are empty and unchanged;
   its depth-extension step is preserved. No module is pruned.
5. Compared the existing node diff: only proof, proof_deps and proof_origin
   changed. Their dependency union agrees with the proof. The new node has the
   required source, complete proof, searches, creation/blueprint provenance,
   chapter/unit and verbatim Lean statement. Its listed algebraic and affine
   dictionaries support the still-open affine proof. No additional hole was
   introduced during this reading.

Second-reading change: signature whitespace only; independent searches and this
review record. Verdict: sound one-for-one decomposition (one original hole
closed, one strictly smaller hole added, net zero), ready for delivery checks.
