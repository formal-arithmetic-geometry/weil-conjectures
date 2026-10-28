## What changed

Replaced the sole hole in `Sheaf.Paper.FiniteQuotientLayerTensorDerivedSliceComparison`
by a K-flat representative argument. The statement and all existing public imports are unchanged.
The proof balances tensor along the successor-to-residue map, proves that exact slice
restriction commutes with this calculation, applies the supplied chart isomorphism through
actual slice functors, and computes the bounded projective constant chart term by term.

Added two modules for the ordinary algebra/sheaf steps:
`Sheaf.Paper.FiniteQuotientLayerKernelConstantComparison` and
`Sheaf.Paper.FiniteQuotientLayerOrdinaryTensorComparison`.
Their statements involve only abelian module categories. The main module proves the derived
balancing, slice transport, projective-to-K-flat argument, and final composition in Lean.
It uses existing K-flat tensor, scalar cancellation, exact restriction, constant flatness,
and coefficient-change APIs through proof-only imports. No other existing module was changed.

Local irreducibility prevents unfolding chosen scalar-extension and tensor data. In particular,
abstracting the chosen ordinary scalar functor removes an elaboration timeout; using the
existing coefficient-adjunction exactness result removes a slow slice instance proof.
These are local implementation choices and change no exported instance or definition.

Validation: all three modules compile cleanly together in import order using `lcompile.py --all`.
The assigned module takes 35.4 seconds against the published green build
`4a1bdb8d2fb5e1e48f22d8319fd1af5a4230ae99`, below the 60-second limit.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.finiteQuotient_layer_tensor_derived_slice_comparison`.
This is a decomposition into two ordinary statements, not a net proof-hole reduction.
All private helpers in the item are proved; no definition contains a hole.

Added exactly two holes, each a public theorem with an exact `by sorry` body:

- `AlgebraicGeometry.Scheme.finiteQuotient_layer_kernel_constant_comparison`, node
  `lem-weil-pbc-finite-quotient-layer-kernel-constant-comparison`.
- `AlgebraicGeometry.Scheme.finiteQuotient_layer_ordinary_tensor_comparison`, node
  `lem-weil-pbc-finite-quotient-layer-ordinary-tensor-comparison`.

The item itself has zero remaining holes. The delivery closes one original hole and adds two:
the net hole change is minus one in the convention “closed minus added”. The two obligations
are genuine ordinary steps: neither has a derived input M, a chart isomorphism, a cohomological
bound, or the original conclusion. The tensor statement is natural for all ordinary residue
modules, without flatness or projectivity assumptions.

## No longer needed

None of the original proof dependencies is pruned. The original imports remain useful.
No existing module or declaration is withdrawn. No unit route is bypassed.

Searches found ordinary quotient-tensor identities and the ideal-power quotient linear
equivalence in Mathlib, but no complete comparison for this actual coefficient system.
The already proved adic graded comparison uses a different coefficient/site presentation;
transporting that presentation would still require the ordinary comparisons isolated here.

## Where the brief, the DAG or earlier work was wrong

No defect in the assigned statement was found. The DAG's single balancing step hid two
ordinary coefficient identifications. These are now explicit nodes, and the derived parts
are Lean proofs from the existing library instead of another copy of the original obligation.

The argument includes zero layers, I=0, I=top, zero rings, zero complexes and empty charts.
There is no division, choice of an arbitrary module witness, finite-rank assumption, or
nonempty-chart assumption.

## New nodes

`lem-weil-pbc-finite-quotient-layer-kernel-constant-comparison` identifies the actual unit-map
kernel with the restricted constant ideal-power layer. Its docstring gives the algebraic
kernel calculation, exact constant sheafification argument, and coefficient-square transport.

`lem-weil-pbc-finite-quotient-layer-ordinary-tensor-comparison` identifies two ordinary functors
using the lifted pure-tensor equivalence, monoidal constant realization, scalar compatibility,
and tensor symmetry. Its docstring explains naturality and the degenerate cases.

Both nodes have source references, three kinds of Mathlib search, Lean attachments, and
self-contained proof plans. The assigned node's proof, dependencies and proof origin follow
the implemented route. There are no change records because no existing interface changed.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteQuotientLayerKernelConstantComparison": "9529b5438e26e9eb8adb2018a235161623dca992", "Sheaf.Paper.FiniteQuotientLayerOrdinaryTensorComparison": "d8d5736778ac85dbf8a59ac9b592237bf26d1ca2", "Sheaf.Paper.FiniteQuotientLayerTensorDerivedSliceComparison": "5ae7dae666ee669bedcf57d18ec6ef248a9c3373"}, "results": {"Sheaf.Paper.FiniteQuotientLayerLocalComplexCore": {"hash": "2032123f990a6b00b8a77331e03aa63bec899775", "status": "OK"}, "Sheaf.Paper.FiniteQuotientLayerTensorDerivedHomologyComparison": {"hash": "cd8fe642a061f164759f4551d6f24652d2003a16", "status": "OK"}, "Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison": {"hash": "e7e22bda9763d91570b3c4729f81fe18fbffc15b", "status": "OK"}}, "seconds": 17, "time": "2026-10-28T11:44:48+0800", "transitive": 2, "version": 1}
```

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
