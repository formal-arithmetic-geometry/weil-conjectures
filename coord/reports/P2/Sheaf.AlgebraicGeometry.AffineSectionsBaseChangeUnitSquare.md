## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeUnitSquare`
with a complete Lean proof preserving its signature. A private, proved `mate_unit_square`
uses Mathlib `unit_mateEquiv` and `iterated_mateEquiv_conjugateEquiv`. The proof identifies
its first mate with the recorded `schemeDerivedBaseChangeMap`, then applies sections,
normalization coherence, and naturality of `r` and `b`.

Added a proof-only import of `Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence`.
That new module isolates coherence of the four normalized sections comparisons on an
arbitrary fibre-product derived object. It contains no base-change map or pullback unit.
Updated the item's node proof and proof dependencies to match the Lean assembly.
No definition, existing signature, or visibility changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.affineSectionsBaseChange_unit_square`
(node `lem-pc-affine-sections-base-change-unit-square`). The private helper
`AlgebraicGeometry.mate_unit_square` is fully proved without sorry.

Added and left: `AlgebraicGeometry.affineSections_square_comparison_coherence`
(node `lem-pc-affine-sections-square-comparison-coherence`), whose whole proof is `by sorry`.
The original module has no remaining sorry. This is a decomposition: one upper hole closed,
one lower hole added, net zero. The nontrivial adjunction identity and its assembly with
sections coherence are proved, while deriving normalization coherence remains work.

## No longer needed

None. The original public import remains necessary for the statement. No original
proof dependency is pruned; their canonical adjunction and composition constructions
are used. No unused proof imports were added. The unit's realized statement and steps
are unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG's first step can be discharged by Mathlib's general mate calculus; it does not
require a new geometric compatibility axiom. Its second step needed a separate interface
expressing sections-comparison coherence, which the existing declarations did not state.
This delivery supplies precisely that part, leaving it for another worker.

The clone does not contain the Stacks source or blueprint literature directories.
The cited cohomology.tex source was fetched into the sandbox scratchpad and its
`lemma-derived-pushforward-composition` and `remark-base-change` were read there.
Blueprint-index search for sections/base-change found no duplicate of the new interface;
the parent node records `lem-sc-finite-duality` as its blueprint ancestor.
LeanSearch was unavailable (HTTP Internal Server Error); this is recorded as unavailable,
not as evidence of no match. LeanFinder and Mathlib/source grep found the generic tools
used in the proof but no existing normalized sections-coherence theorem.

## New nodes

`lem-pc-affine-sections-square-comparison-coherence` is stated in
`lean/Sheaf/AlgebraicGeometry/AffineSectionsSquareComparisonCoherence.lean`.
It compares the two normalized ways of taking sections of composed pushforwards on
arbitrary `F`, independently of the pullback units and base-change map. Its docstring
and node give the K-injective/pinned-derived-unit argument. Identity squares reduce
to the composition unit law; `F = 0` gives equal zero morphisms. No nonempty, flat,
Tor-independent, bounded, or quasi-coherent hypothesis is required. Canonical comparison
data is constructed from the existing pinned pullback-composition family and conjugation;
no arbitrary witness is introduced. No change record is required.

## Second reading by P2

1. Compared both delivered modules with the repository. The existing target signature is byte-for-byte unchanged; the only interface addition is the separately recorded split node and its new module.
2. Compiled the sandbox with `lcompile.py --all`; it is clean. The target proof has no `sorry`, while the split theorem is the only deliberate `sorry`; no forbidden declarations or hollow definitions were introduced. The target proof uses only the permitted foundational axioms apart from the open split theorem.
3. Checked the split statement against the target reduction. It removes the pullback-unit/base-change portion while retaining exactly the normalized sections-comparison coherence needed by the final rewrites, so it is strictly simpler and has the required source, docstring, and DAG node. No existing declaration duplicates it.
4. Read the proof top-down. The private mate calculation is the shortest available Mathlib route (`unit_mateEquiv` and `iterated_mateEquiv_conjugateEquiv`); the remaining assembly follows the stated normalization hypotheses. The proof-only coherence import is used, and no original import is redundant. The unit's realized route remains unchanged.
5. Verified the DAG proof steps and dependencies match the Lean proof: the target node records the mate step and coherence step, and the split node records its pending derived-coherence argument. No statement or definition was changed.

Changed during second reading: added this review record only; no Lean or DAG repairs were necessary.
