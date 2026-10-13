## What changed

Replaced the main hole by affine restriction, a bounded-above finite-free module lift,
the ring perfectness criterion, and sheafification of its finite-projective model.
The local lifts and finite-free retract calculations are proved private helpers.
A new theorem isolates transfer of global Tor bounds to a given affine module model.
All existing signatures and public imports are unchanged.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.isPerfect_of_isPseudoCoherent_of_hasFiniteTorDimension`
(node `lem-pc-pseudo-coherent-finite-tor-perfect`).

Added one hole:
`AlgebraicGeometry.Scheme.finiteTorAmplitude_of_affine_sheafification`
(node `lem-pc-affine-sheafification-tor-amplitude`).

This is a decomposition, not a net reduction in holes: one closed, one added.
The remaining statement is only the Tor-bound transport step, with no
pseudo-coherence hypothesis and no perfectness conclusion.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`.
Node `lem-pc-affine-derived-pullback-tensor-tilde` is the only old direct proof dependency
removed from the target node. Its tensor comparison is needed in the remaining
Tor-transport step rather than directly
in the final assembly. It is not claimed to be globally pruned.
The ring criterion remains used. The sections/tilde node remains used via the explicit
finite-free lift. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The ring criterion is already proved in the current checkout. No statement correction
was necessary. The planned affine Tor transfer needs compatibility across the localized
open site, the open subscheme, and its spectrum, which is not supplied by a single
original proof dependency. The new theorem isolates this compatibility.

## New nodes

`lem-pc-affine-sheafification-tor-amplitude`, in
`Sheaf.AlgebraicGeometry.AffineSheafificationTorAmplitude`: transfer global finite Tor
dimension to a module complex representing restriction on an affine open. Its source
is the locality of Tor amplitude (08CG), the affine criterion (08E9), and the tensor
comparison (08DX). Zero rings, empty opens, and unbounded representatives are allowed.
No change record is needed: existing signatures and public environments are unchanged.

## Second reading by X2

1. Statements: compared the delivered target module and both DAG statements with the repository. The target signature is byte for byte unchanged; the added Tor-amplitude theorem is a genuine affine module-model transport statement and is strictly narrower than the target. Verdict: pass.
2. Proof: compiled both delivered modules with `lcompile.py --all`; there are no compiler errors, forbidden declarations, or hollow definitions. The target proof has no `sorry`; the one remaining `sorry` is the named transport theorem. `#print axioms` on scratch copies of both public theorems returned only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the delivery probe also checked all declarations. Verdict: pass, with the documented decomposition.
3. New statement: checked edge cases in the statement (empty affine opens, zero rings, zero complexes, and unbounded representatives are explicitly covered) and searched Lean/Mathlib for duplicates. No existing declaration states this transport result: `affine_torAmplitude_iff` supplies only the spectrum criterion, while `derivedTensor_openRestriction_iso_universes` supplies tensor restriction. Checked Stacks Tags [08E9](https://stacks.math.columbia.edu/tag/08E9), [08CG](https://stacks.math.columbia.edu/tag/08CG), and [08CQ](https://stacks.math.columbia.edu/tag/08CQ). On the empty open the module category is zero; for zero complexes the bounds are arbitrary; unbounded representatives are permitted because the comparison is in the derived category. Verdict: pass.
4. Pruning: the removed proof import is no longer used by the target proof; the remaining imports are used by declarations or proofs. The unit route remains affine reduction followed by the ring criterion and local perfectness. Verdict: pass.
5. DAG agreement: checked the target node and new node fields, declarations, statements, proof dependencies, and proof origin against the Lean files. Verdict: pass.

Second reading changed the report to make pruning explicit, and added independent searches to the new node. The Lean proof was retained. No existing signatures or definitions were changed.
