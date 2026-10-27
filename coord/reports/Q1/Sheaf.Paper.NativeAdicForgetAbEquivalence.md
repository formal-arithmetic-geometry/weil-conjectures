## What changed

Proved `WeilConjectures.LocallyFiniteAdicCompactSupport.native_adic_forgetAb_isEquivalence`
in `Sheaf.Paper.NativeAdicForgetAbEquivalence` by applying the existing proved theorem
`AlgebraicGeometry.ProEtale.nativeScalarForgetting_isEquivalence` with the same prime and
scheme. Added its private proof import `Sheaf.Paper.NativeScalarForgetting`. The signatures,
public imports, definitions and existing docstrings are unchanged. Updated the item's node
proof and proof dependency to match this reuse of the complete scalar-recovery argument.

The import-direction check confirms that the dependency does not reach this item. The
single-file remote compile passed without warnings in 3.4 seconds. The delivery tool also
checks the theorem's axioms. The unit has no realized statement or proof-step nodes; this
reuse stays within the same unit and preserves the parent's native geometry route.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.LocallyFiniteAdicCompactSupport.native_adic_forgetAb_isEquivalence`
(node `lem-sf-native-adic-forget-ab-equivalence`). Holes added: 0. Holes left in the item's
module: 0. No split-off statements. The dependency's scalar-recovery proof is complete;
it constructs the recovered module and proves full faithfulness and essential surjectivity.

## No longer needed

No imports removed and no modules withdrawn. The three formerly planned local construction
steps need no new declarations or duplicate proofs: their full argument already exists in
`Sheaf.Paper.NativeScalarForgetting`, node `lem-sf-native-scalar-forgetting-equivalence`.
The original node had no proof dependencies to prune. Its statement dependency
`def-sf-locally-finite-adic-realization-data` remains unchanged. No existing node or module
is claimed to become globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The item's statement duplicates an already proved library theorem. The original plan omitted
that reusable declaration and classified the full scalar recovery construction as elementary.
The existing theorem has precisely the same conclusion for any scheme, in the same universes,
with no finiteness assumptions. It covers the empty test object and zero module. Reusing it
closes the obligation rather than splitting it again. The module is retained because the
native compact-support geometry proof uses its public theorem.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
