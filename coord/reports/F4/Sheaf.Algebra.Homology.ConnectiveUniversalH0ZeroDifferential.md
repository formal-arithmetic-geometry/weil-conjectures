## What changed

Replaced the whole proof hole of
`CochainComplex.connective_universalH0_zero_differential` by a compiling cancellation
argument. Its signature, visibility, and existing public imports are unchanged.
Added proof-only imports of `Mathlib.CategoryTheory.Idempotents.HomologicalComplex`,
`Mathlib.RingTheory.Finiteness.Basic`, and
`Sheaf.Algebra.Homology.UniversalH0SplitDifferential`.

The new module isolates the local algebra in
`CochainComplex.universalH0_split_differential`: the first differential admits
`s` satisfying `d ≫ s ≫ d = d`. This intermediate statement needs finite
projectivity only in degrees zero and one, and vanishing only in degree minus one;
it has no boundedness hypothesis. The main theorem specializes those hypotheses
and constructs the desired homotopy equivalence itself.

The cancellation uses the null-homotopic chain idempotent `e = dh + hd`, supported
in degrees zero and one. Splitting `1 - e` produces `Q` with termwise retractions.
The proof transfers boundedness, finite generation, projectivity, and negative
vanishing, proves the outgoing differential zero, and explicitly supplies both
homotopies. It keeps the original support bounds. No data definition or arbitrary
witness of an unproved existence theorem is introduced.

Both modules compiled with the prescribed `lcompile.py` wrapper. Updated both DAG
records so the remaining algebra step and the proved cancellation agree with Lean.

## Proved and sorry left

Closed the original hole:
`CochainComplex.connective_universalH0_zero_differential`
(node `lem-sc-connective-universal-h0-zero-differential`).

Added one whole-proof hole:
`CochainComplex.universalH0_split_differential`
(node `lem-sc-universal-h0-split-differential`).

This is a decomposition: one hole closed, one strictly smaller hole added, net zero.
The local matrix/global projectivity argument remains to formalize. The cancellation,
all six requested output properties, and their assembly are proved without holes.
The new lemma asserts no new complex or homotopy equivalence and does not repackage
the parent conclusion.

## No longer needed

No existing imports were removed: all five original public imports supply statement
vocabulary, and both additional Mathlib proof imports are used. In the new lemma
module, replaced the unnecessarily broad Homotopy import by
Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex, which supplies homology
and the scalar-extension complex construction used in its statement.

The new local matrix route no longer needs:

- `lem-sc-perfect-local-pseudocoherent-free-model`, module
  `Sheaf.RingTheory.MinimalFreeModel`;
- `lem-pc-finite-projective-cokernel-localization`, module
  `Sheaf.RingTheory.FiniteProjectiveCokernelLocalization`;
- `lem-pc-ring-derived-map-representative`, declaration
  `CochainComplex.IsKProjective.Qh_map_bijective` in
  `Mathlib.Algebra.Homology.DerivedCategory.KProjective`.

These disappear from this proof route, including its remaining lemma's plan;
no claim is made that other target branches cease to need them.
The other three former dependencies move into the new algebra lemma's plan:
`lem-weil-pbc-finite-projective-finitely-presented`,
`lem-weil-pbc-finite-projective-prime-local-free`, and
`lem-weil-pbc-finitely-presented-flat-module-projective`.
They have not been pruned globally or silently replaced by new copies. The
residue-injectivity cokernel theorem does not apply to the original differential
with its one-dimensional residue kernel; the new proof uses the unit-minor
calculation from its source, followed by a separate rank-one argument.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old proof used a minimal derived model even
though only the degree-zero kernel matters. A local unit-minor reduction of the
first differential suffices; neither boundedness nor higher projective terms
are used in the remaining algebra lemma. Its rank-one remainder has kernel A,
whose inclusion is multiplication by a non-zero-divisor, forcing its differential
to vanish. This avoids derived-category comparison and minimal-model uniqueness.

The local algebra was checked against Stacks
[00O0](https://stacks.math.columbia.edu/tag/00O0), especially the unit-minor
argument, and [0BCC](https://stacks.math.columbia.edu/tag/0BCC), the route being
removed. The new argument is marked as agent-written, not quoted as a theorem
of either source. The original docstring remains as an alternative proof plan.

Edge cases: over the zero ring all maps are zero; a complex supported only in
zero has `d = 0` and admits `s = 0`; source rank one gives the empty identity
block in the local matrix argument; arbitrary nonreduced rings are allowed
because cancellation uses an injective multiplier, not a reducedness assumption.
The category-theoretic cancellation also handles zero source or target terms.
No unit statement or realized unit step is bypassed.

Searches were run by `msearch.py` (LeanSearch unavailable with HTTP 500;
LeanFinder, Loogle and source grep available), and the complete DAG, source
library and imported blueprint were searched for an existing splitting lemma.
No exact existing statement was found. Search records are in the new node.

## New nodes

`lem-sc-universal-h0-split-differential`, in
`lean/Sheaf/Algebra/Homology/UniversalH0SplitDifferential.lean`, isolates the
existence of a generalized inverse for the first differential. Its docstring
and node give the complete local unit-minor argument, the non-zero-divisor
calculation, and the global cokernel/image projectivity argument. No existing
interface changes or forced adaptations were required; there is no change record.

## Second reading by F4

1. Compared the complete existing module with the repository using diff and checked
   its theorem signature byte for byte. Verdict: unchanged signature, visibility,
   public imports, and definitions; only three proof imports and the proof body
   were added. No interface change or change record is required.
2. Independently compiled both delivered modules with lcompile.py --all, then
   compiled a scratch copy with #print axioms for both declarations. Verdict:
   no compiler errors or warnings; the only hole is the named theorem
   CochainComplex.universalH0_split_differential. Both axiom lists contain only
   propext, Classical.choice, Quot.sound, and sorryAx. No forbidden declaration,
   hidden hole, data definition, or arbitrary unproved witness in a definition
   occurs. The generalized inverse is eliminated within a theorem proof.
3. Read the algebra lemma's statement, complete docstring argument, and node.
   Verdict: true and strictly smaller than the parent. Only degrees -1, 0, 1
   matter; residue rank n-1 gives a unit minor, the remaining rank-one kernel
   gives an injective multiplier, and cancellation makes the remaining entries
   zero. Finitely presented locally free cokernel is projective; two sections
   then give d s d = d. Checked zero ring, n=1, zero target, and nonreduced
   rings. Independently searched LeanFinder for universally free rank-one
   kernels/split images, Loogle for Module.Projective with LinearMap.range,
   Mathlib grep for regular maps, split ranges and kernel ranks, and both
   library roots for universal-kernel and generalized-inverse variants. No
   matching theorem was found; only ordinary projective splitting and
   rank-nullity ingredients. The remaining hole needs substantial local matrix
   and scalar-extension formalization and cannot be closed in a few minutes.
4. Read the cancellation from the top: e=dh+hd is an idempotent supported in
   degrees zero and one; the splitting of 1-e transfers all four termwise
   properties and kills d0; the explicit -h homotopy proves equivalence.
   Verdict: a real reduction, not a restatement. All old dependencies unused
   by this proof are accounted for under No longer needed, with three retained
   in the remaining algebra plan. Checked dag/units/sk-prop-av-cube.json and
   its unit statement/step: this is below the cube theorem's unit route and
   changes no realization or unit step. Imports are confined to statement
   vocabulary and the cancellation tools; narrowed the new lemma's homology
   import to the module defining the required vocabulary.
5. Checked both nodes' verbatim Lean signatures, proof steps, union of uses,
   proof_deps, proof_origin, source, chapter, unit, and new-node metadata.
   Verdict: they now agree. Removed the new lemma's erroneous dependency on
   lem-pc-finite-projective-cokernel-localization: its conclusion assumes an
   injective residue map, whereas the original differential has a rank-one
   residue kernel. The local calculation adapts the proof of
   [Stacks 00O0](https://stacks.math.columbia.edu/tag/00O0); it does not apply
   that theorem to the original differential. The globalization uses
   [Stacks 00NX](https://stacks.math.columbia.edu/tag/00NX).

Changed only the new module's homology import, the new node's inaccurate
proof-dependency citation and explanatory text, and this report's pruning
account. No correct Lean proof was rewritten. One original hole is closed,
one strictly smaller hole is added, and net holes closed is zero: decomposition.
