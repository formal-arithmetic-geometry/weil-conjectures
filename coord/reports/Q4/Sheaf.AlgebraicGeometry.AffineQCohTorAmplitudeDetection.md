## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.affineQCoh_torAmplitude_detection` with the full affine
flat-model argument. The statement, universes, visibility, public imports and
definitions are unchanged. No other Lean module is changed.

Represent the object by a module complex using the canonical affine chart.
Exact and faithful tilde followed by restriction detects the vanishing of module
tensor homology from the quasi-coherent tests. The module flat-model criterion
then gives a flat complex concentrated in the requested interval. Its restricted
associated-sheaf complex is K-flat and represents the original object. Tensoring
with any sheaf gives zero terms, hence zero homology, outside the interval.
All model choices are eliminated in a proof of a proposition; no data definition
is constructed from an unproved existence statement.

Used the already proved public `tilde_preserves_finite_limits` instead of the
private helper named in the old node plan. Updated the item's node proof and
proof dependencies accordingly. The unit route is unchanged. Searches through
LeanFinder, Loogle, msearch grep and local rg found no shorter applicable theorem;
`affine_torAmplitude_iff` has all-sheaf tests in its premise and does not itself
supply the needed quasi-coherent-test implication.

Validation: the complete proof compiled through `lcompile.py` without warnings,
including after pruning redundant imports, in approximately 21 seconds. The
required delivery dry run is run on this final sandbox. No target statement or
intermediate statement changed, and no consumer adaptation is necessary.

## Proved and sorry left

Closed: `AlgebraicGeometry.affineQCoh_torAmplitude_detection`
(blueprint: `lem-pc-affine-qcoh-tor-amplitude-detection`). One of one original
holes closed. Zero holes added, zero split off, and no `sorry` remains in the
item module. Existing imported statements retain their own proof obligations;
most notably the affine derived tensor chart comparison is used as stated.
This is a proof from the existing dependency declarations, not a decomposition.

## No longer needed

Removed direct imports:

- `Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison`: the public
  finite-limit theorem plus Mathlib's exact-functor homology comparison replaces
  its private kernel helper. The corresponding direct proof dependency
  `new-affine-derived-tilde-homology-comparison` is removed from the item's node.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`:
  already publicly supplied by `TorAmplitudeFlatModel`.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`: already publicly
  supplied through `TorAmplitudeFlatModel` and the source flat-model module.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  the used factorization and homology comparisons are Mathlib declarations
  already available from the retained imports.

The source K-flat resolution and K-flat tensor-model nodes are still used, even
though their declarations are supplied transitively. No other planned nodes are
pruned. Removed direct imports may still be reached through other modules; this
report makes no claim that their entire modules leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The old plan requested a private kernel-preservation helper from
`AffineDerivedTildeHomologyComparison`. That module is now a re-export wrapper
after upstream synchronization. The existing public theorem in
`TildePreservesFiniteLimits` provides the needed interface directly and avoids
depending on the retired private helper. The original mathematical statement and
the remainder of its flat-model plan are sound. The proof uses neither a
nonzero-ring assumption nor boundedness of the initial complex; empty affine
schemes and singleton intervals are covered by the same construction.

## Second reading by Q4

1. **Signatures and accidental changes — pass.** I diffed the delivered Lean
   module against the repository version. The theorem signature and all existing
   declarations are byte-for-byte unchanged; only the proof body and proof-only
   imports changed. The DAG update changes only the recorded proof route,
   dependencies, and origin fields.

2. **Compilation and proof status — pass.** The module and the complete sandbox
   import closure compile with `lcompile.py` without errors or warnings. The
   theorem has no `sorry`, and the proof introduces no definitions, axioms,
   `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. The proof
   uses only the permitted existing declarations and standard classical
   reasoning.

3. **Statements and split-off work — pass.** No new theorem statement was
   split off. The existing target statement remains unchanged and its proof
   establishes the stated conclusion for every sheaf `G`; no hypothesis was
   added and no conclusion was weakened. The node's recorded statement and
   declaration agree exactly, and the recorded searches found no shorter
   library theorem.

4. **Route and pruning — pass.** The unit route through the affine module
   representative, tensor comparison, flat model, and K-flat restriction is
   retained. The proof uses the public finite-limit theorem and removes only
   obsolete or transitively supplied proof-only imports; all removed imports
   and the retired helper dependency are listed above.

5. **DAG consistency — pass.** The node's proof steps, `proof_deps`, and
   `proof_origin` now match the Lean proof, including replacement of the retired
   private kernel helper by `lem-sc-tilde-preserves-finite-limits`. No unit
   `realized` entry or target statement was changed.

**Changes made during this reading.** I added this second-reading record and
verified the final module with both single-file and sandbox-wide compilation;
the Lean proof itself required no further repair.
