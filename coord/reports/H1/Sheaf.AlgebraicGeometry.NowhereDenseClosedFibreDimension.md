## What changed

Proved `AlgebraicGeometry.fibre_dimension_lt_of_closed_interior_eq_empty` in
`Sheaf.AlgebraicGeometry.NowhereDenseClosedFibreDimension` with its signature unchanged.
Added proof-only imports of `Mathlib.AlgebraicGeometry.Noetherian` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.

The proof constructs the closed immersion between the ordinary fibres and identifies
its range and distinguished point. Three fully proved private helpers establish the
topological argument: each point generalizes outside a nowhere dense closed subset;
a specialization chain therefore extends by one; applying this on an open neighbourhood
of dimension less than the finite local dimension plus one gives the strict local drop.
The finite-dimensional noetherian hypotheses on the ambient fibre come from existing
Mathlib and source-library theorems. Updated the existing node's proof, proof_deps,
and proof_origin to this route. The unit record has no realized nodes to retain here;
this change is below the unit level and retains the slicing argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.fibre_dimension_lt_of_closed_interior_eq_empty`
(node `lem-sbc-nowhere-dense-closed-fibre-dimension`).

No sorries remain in the item and none were added elsewhere. This is a proof, not a
decomposition. All three new private helper theorems are proved.

The module compiles without errors or warnings using the required launcher.
`#print axioms AlgebraicGeometry.fibre_dimension_lt_of_closed_interior_eq_empty`
reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
No public signature or definition changed and no forced adaptations are needed.

## No longer needed

The planned dependency `lem-weil-pbc-dimension-at-point-components` and its module
`Sheaf.RingTheory.DimensionAtPointComponents` are not used or imported by this proof.
Removed that node from this item's proof_deps. The initial module did not actually
import it, so no existing Lean import was removed. The component maximum, finite-type
domain dimension, and affine/local-ring comparisons below that dependency are unnecessary
for this item's proof. This is a local pruning claim; those nodes may still be needed
by other targets or modules.

## Where the brief, the DAG or earlier work was wrong

The existing planned component-formula dependency is unnecessary. The statement is true
in the more general setting of a closed embedding into a finite-dimensional noetherian
sober T0 space, and the pointwise inequality follows by applying the chain-extension
bound on a neighbourhood. The earlier DAG left the chain-extension and maximum steps
without named dependencies; the delivery supplies complete Lean proofs of the needed
topological steps and avoids the maximum argument entirely.

Read Stacks Tags 054X and 0052 online because this machine does not contain the Stacks
source tree. Tag 054X supplies the original dimension contradiction, and Tag 0052(3)
supplies the nonempty open inside each irreducible component. All library results used
were also read in their local Lean source. No statement disputes or new nodes.

## Second reading by H1

1. I diffed the delivered module against the repository version. The theorem signature
   and all existing declarations are unchanged byte for byte; only proof code, proof-only
   imports, and the node's proof metadata changed. Verdict: pass.
2. I compiled the module with `lcompile.py`. It has no errors or warnings, no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and no definition contains
   `sorry`. A scratch copy with `#print axioms` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. I checked every helper and the main theorem against the node and source argument.
   The specialization-extension argument and the local-dimension restriction are true,
   and no new public statement or split-off theorem was introduced. At dimension zero
   the closed subset must be empty; a source point would contradict this, as the proof
   shows. Empty ambient spaces are vacuous, and reducible spaces are covered by the
   generic-point argument for a component through each point. Verdict: pass.
4. I checked the downward route and pruning. The component-formula dependency is not
   used; the proof instead uses the existing Noetherian and finite-dimension results and
   private topological helpers. I also searched the existing dimension-drop modules and
   Mathlib topology; the related scheme dimension-drop theorem remains sorry and is
   global, while the proved specialization-chain theorem is already used. The two
   added imports are proof-only and the removed
   dependency is recorded above. Verdict: pass.
5. I checked the DAG node's theorem statement, proof steps, proof dependencies, and
   proof origin against the Lean proof. The node's statement is unchanged, and the unit
   route is retained; no unit step is bypassed. Verdict: pass.

The first worker's proof, imports, and node metadata needed no repair. My only change
was to add this second-reading record; I preserved the delivered Lean module.
