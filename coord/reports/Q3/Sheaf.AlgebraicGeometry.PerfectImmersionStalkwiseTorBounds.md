## What changed

`Sheaf.AlgebraicGeometry.PerfectImmersionStalkwiseTorBounds` now proves
`AlgebraicGeometry.perfectImmersion_stalkwiseTorBounds` from a bounded projective
stalk resolution. Its existing signature, visibility, docstring and public imports
are unchanged. The proof first uses the existing closed-pushforward cokernel theorem
to supply exactness, then the exact-functor derived comparison to identify the derived
pushforward of the unit with the ordinary pushforward placed in degree zero.
It extracts the specified local strictly perfect model from `hperfect` and applies
the new stalk-resolution theorem.

The two private helpers are proved: `tor'_isZero_of_bounded_resolution` computes Tor'
with `ProjectiveResolution.isoLeftDerivedObj`, observes the zero degree-j tensor term,
and deduces exactness and zero homology; `tor_isZero_of_tor'_isZero` uses the existing
`nonempty_tor'_flip_iso`, then derives `tensorLeftIsoTensorRight` using
`NatTrans.leftDerived_comp` and `NatTrans.leftDerived_id`. The second assertion uses
the same bound as the first. No new double-complex or Tor-balance hole is introduced.

New proof imports are the stalk-resolution module, `TorSymmetry`,
`ClosedImmersionPushforwardCokernel`, and the upstream exact-functor derived comparison
module `RightDerivedFunctor.MapDerivedCategory`. Tor symmetry is a generic algebra
tool, used without changing the Picard-duality unit's route. Both the original node
and the new node have proof plans matching this implementation.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.perfectImmersion_stalkwiseTorBounds`
(node `lem-sc-perfect-immersion-stalkwise-tor-bounds`).
There is no `sorry` in the item's module or its private helpers.

Added exactly one hole:
`AlgebraicGeometry.strictPerfectClosedPushforward_stalkResolution`
(node `lem-sc-strict-perfect-closed-pushforward-stalk-resolution`), in
`Sheaf.AlgebraicGeometry.StrictPerfectClosedPushforwardStalkResolution`.
Its proof is exactly `by sorry`. It has a complete proof in words and recorded source
and searches. This theorem concerns a specified local model of the ordinary single
pushforward and returns an actual bounded projective resolution; it has no derived
pushforward hypothesis and no Tor conclusion. The original proof supplies the
comparison, extracts the model, computes Tor' and transfers vanishing to Tor.
This is a decomposition, not an unconditional proof of the target: one hole closed,
one new hole added, net zero for these delivered declarations.

Both modules compile together using `lcompile.py --all`, without warnings. The
required delivery dry run is the final check. No definition, existing theorem
signature, target, or existing public import was changed.

## No longer needed

Removed the item's direct proof import
`Sheaf.AlgebraicGeometry.ClosedPushforwardStalks`. It remains needed transitively by
`ClosedImmersionPushforwardCokernel` and in the new stalk-resolution node's proof plan,
so this is not a claim that that module or its node is globally pruned.

No original dependency module or node is globally pruned. The original
`def-pc-perfect-complex` dependency remains, and
`lem-weil-pbc-closed-pushforward-stalks` is used below the new node rather than directly
by the item's proof. The original tensor-double-complex step is discharged using the
existing `lem-weil-pbc-tor-symmetry`; no new nodes for its rows, columns or balancing
are needed in this delivery.

## Where the brief, the DAG or earlier work was wrong

The original statement and mathematical plan are sound. The listed proof dependencies
alone do not expose a declaration producing the bounded stalk resolution; that is the
one new node. The double-complex step already has an implementation in `TorSymmetry`,
so no new balance theorem was needed. The closed-pushforward exactness step already has
the proved cokernel-preservation interface, which is reused rather than re-proved.

The existing `tools/blueprint_refs.py ancestor` command returns `None` for this item
because its `created.item` is a module name; the new node therefore inherits the
existing node's explicit `blueprint.from.node = lem-sc-finite-duality` and prepends the
item node to the recorded `via` chain. Blueprint searches for "perfect stalk",
"bounded projective resolution" and "066Q" found no duplicate blueprint node.

Sources read: Stacks `duality.tex`, `lemma-compare-with-pullback-flat-proper-noetherian`
(Tag 0A9U); `cohomology.tex`, `definition-strictly-perfect` (08C4);
`more-algebra.tex`, `lemma-perfect-module` (066Q). Tag 0A9U is the motivating
hypothesis translation, not a claim that its statement directly gives the new local
resolution theorem. The new node expands the stalk and finite-resolution argument.
LeanSearch returned an internal server error and is recorded as unavailable;
LeanFinder and grep returned component results only.

## New nodes

`lem-sc-strict-perfect-closed-pushforward-stalk-resolution`, at
`dag/nodes/sec-picard-framework/lem-sc-strict-perfect-closed-pushforward-stalk-resolution.json`,
stated by `AlgebraicGeometry.strictPerfectClosedPushforward_stalkResolution` in
`lean/Sheaf/AlgebraicGeometry/StrictPerfectClosedPushforwardStalkResolution.lean`.
Take the exact stalk functor of the specified local model, identify the pushforward
stalk by the closed-immersion formula, and retain the finite-projective retracts and
bounds. Split the acyclic positive projective tail from its bounded upper endpoint,
augment the remaining nonpositive complex by its degree-zero cokernel, and reverse
indices. The lower endpoint supplies the bound on the resolution length. Empty Z
has no point x; identity immersions give the free rank-one stalk; an acyclic local
model gives a zero stalk and its zero resolution. The dual-numbers closed point
without finite projective dimension does not satisfy the local strictly perfect
hypothesis, so it is not an excluded counterexample. No change record is needed:
this is a new theorem and no existing interface was changed.

## Second reading by Q3

1. Compared the delivered item module with the repository version. The target
   signature, docstring, visibility, and all existing declarations are unchanged;
   only the proof and proof-only imports changed. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. The target has no
   `sorry`; the sole remaining `sorry` is the named theorem
   `strictPerfectClosedPushforward_stalkResolution`, with a matching node and
   complete proof sketch. No forbidden declarations or hollow definitions occur.
   Scratch `#print axioms` checks found only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx` in the target and split theorem. The direct
   resolution-to-Tor' helper has only the three standard axioms; the Tor transport
   helper also inherits `sorryAx` from the existing symmetry dependencies.
   Verdict: pass.
3. Checked the split-off statement against the closed-immersion stalk and strictly
   perfect hypotheses, including empty and acyclic cases. It is a strict reduction
   to a bounded projective resolution and has no Tor conclusion; its source,
   searches, and node are recorded. Independent LeanFinder search for a bounded
   projective complex with degree-zero homology returned general resolution
   machinery only; grep for finite/bounded projective resolutions returned no
   applicable theorem. Verdict: pass.
4. Checked the proof route and pruning. The exact closed-pushforward comparison,
   local resolution node, projective-resolution Tor computation, and existing Tor
   symmetry are all used; the removed direct stalk import is unnecessary. The
   Picard-duality unit route remains represented. Verdict: pass.
5. Checked the DAG records against the Lean declarations and proof dependencies;
   the target node records the four implemented steps and the new node records the
   split theorem and its source. Verdict: pass.

Changed during second reading: added this review record only; no Lean or DAG edits
were needed.
