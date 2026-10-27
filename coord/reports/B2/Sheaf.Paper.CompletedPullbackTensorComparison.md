## What changed

Reduced `WeilConjectures.canonicalFinitePullbackTensor_quotient` to the flat-term
K-flat representative square in the new proof-only import
`Sheaf.Paper.FinitePullbackTensorQuotientRepresentatives`. The parent constructs
the two paths as natural transformations, applies the existing normalized
ordinary and derived quotient comparisons on representatives, and extends their
equality by naturality and resolution isomorphisms. A proved private helper keeps
this descent abstract over its categories; a private typed tensorator wrapper
avoids repeatedly unfolding the chosen evaluation calculus. All existing signatures,
definitions and public imports are preserved. The original DAG gains this
representative step; its existing steps remain.

Validation: the new representative module compiled remotely. The final item, with
all profiling and diagnostic code removed, compiled remotely in 36.0 seconds,
below the 60-second limit.

## Proved and sorry left

One of the item's three direct holes is reduced, with one lower hole added:
`WeilConjectures.canonicalFinitePullbackTensor_quotient` now has a complete Lean
proof from the representative theorem. This is a decomposition, not a net proof
of the quotient square.

The two original holes retained in the item, both owned by
`def-pur-completed-pullback-tensor-comparison`, are
`WeilConjectures.canonicalCommonStagePullbackTensor_existsUnique` and
`WeilConjectures.canonicalIntegralPullbackTensor_scalar`.

The one new hole is
`WeilConjectures.finitePullbackTensor_quotient_representatives`, owned by
`lem-pur-finite-pullback-tensor-quotient-representatives`. It is restricted to
localized flat-term K-flat pairs and includes the ordinary unit and derived
counit normalization assumptions. The parent supplies these from existing proved
specifications. The naturality descent is proved separately in the parent.
Direct holes: 3 before, 2 in the item plus 1 in the new module afterward; net 0.

## No longer needed

None. No existing import, declaration, node or module is withdrawn. All original
proof dependencies still serve the existing declarations; the new dependency is
strictly the generator calculation for the finite quotient square. In particular,
no source-library declaration is removed or reset to sorry.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or unit route was changed. The former finite quotient
proof docstring bundled the representative calculation and naturality descent.
This delivery makes that distinction explicit in Lean. Existing ordinary unit,
cochain degree, and derived counit normalizations are sufficient for the descent;
there is no extra quotient-flatness assumption. Edge cases checked at the new
statement: m=n, m=n=0, empty schemes, zero complexes, and non-flat positive
quotient transitions; the generator formula and descent remain valid.

## New nodes

`lem-pur-finite-pullback-tensor-quotient-representatives` states only the flat-term
K-flat representative calculation for the normalized finite quotient square.
Its three proof steps follow the total-complex argument of Stacks 07A4, with the
existing quotient counits. It has no dependency on the parent module and is
strictly smaller than the all-derived-input equation. No change record is
needed: existing public signatures and definitions are unchanged.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
