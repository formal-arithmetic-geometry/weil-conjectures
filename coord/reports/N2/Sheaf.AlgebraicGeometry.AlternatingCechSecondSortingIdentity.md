## What changed

The item now combines two explicitly named intermediate contraction and transport
lemmas. The combination proof is complete and uses only the finite-sum definitions.
The two intermediate lemmas retain their documented `sorry` proofs because their
term-by-term cancellation arguments are the remaining work.

## Proved and sorry left

Closed one original hole and added two holes: this is a decomposition, not a
sorry-free proof. `AlgebraicGeometry.Scheme.cechSecondSortingIdentity` is proved from the two
intermediate statements and the sorting operators. The following named statements
remain sorry and have corresponding DAG nodes: `AlgebraicGeometry.Scheme.cechSortedContraction`
and `AlgebraicGeometry.Scheme.cechSortingBoundaryTransport`.

## No longer needed

None. The sorting-operator and Čech-complex imports remain needed by the definitions
and the combination proof.

## Where the brief, the DAG or earlier work was wrong

The original node treated the full finite-sum cancellation as one step. Lean requires
separating the cancellation on nondecreasing tuples from its stable-sorting transport;
the two new nodes make those strictly smaller obligations explicit.

## New nodes

`lem-pc-alternating-cech-sorted-contraction` and
`lem-pc-alternating-cech-sorting-boundary-transport` are the two intermediate
statements, in the corresponding new modules under `lean/Sheaf/AlgebraicGeometry`.

## Second reading by N2

1. The target and existing declaration signatures were compared byte for byte
   with the repository versions; the target statement is unchanged. Verdict: pass.
2. All three delivered modules compile with `lcompile.py --all`. The target proof
   has no `sorry`; the two explicitly split intermediate theorems retain their
   named `sorry`s, with no sorry in definitions. Verdict: pass.
3. The two split statements are strict sub-obligations of the target, have source
   and proof prose, and each has a corresponding DAG node. Searches found no
   existing library or Mathlib declaration. Verdict: pass.
4. The target proof follows the stated transport, finite-sum distribution, and
   sorted-contraction route; no import can be removed without losing a used
   declaration. The unit route is unchanged. Verdict: pass.
5. Node proofs and `proof_deps` agree with the imports and declarations used by
   the delivered Lean files; the two new nodes are marked split and carry the
   required metadata. Verdict: pass.

Changed only the target proof and the two new split modules/nodes, then recorded
this second-reading review. No statement or definition was changed.
