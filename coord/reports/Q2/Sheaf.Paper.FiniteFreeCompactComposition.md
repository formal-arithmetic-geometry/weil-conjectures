## What changed

Implemented `WeilConjectures.FiniteFreeCompactComposition.pullRestrictionInv_isIso`
using ordinary evaluation of coefficient systems. Private helpers compare normalized
direct-image squares, paste their adjunction mates, and detect invertibility on all
coefficient levels. The finite-level inverse mate is the existing ring-sheaf scalar
restriction pullback comparison. All existing public statements and definitions remain
unchanged. Proof imports expose the existing mate-pasting, varying-ring evaluation,
and ring-sheaf adjunction APIs. Ordinary isomorphism detection follows by applying the
conservative forgetful functor to abelian presheaves.

## Proved and sorry left

Closed one existing hole:
`WeilConjectures.FiniteFreeCompactComposition.pullRestrictionInv_isIso`.
Added no holes and no split-off statements.

The three remaining original holes, all attached to
`lem-coef-finite-free-compact-composition`, are:

- `WeilConjectures.FiniteFreeCompactComposition.pushRestriction_isIso`.
- `WeilConjectures.FiniteFreeCompactComposition.openRestrictionInv_isIso`.
- `WeilConjectures.FiniteFreeCompactComposition.systemComposition`.

The previously implemented finite-level composition theorem is retained.
The full module compiled successfully in 49.2 seconds; profiling options and the
temporary evaluation probe were removed before delivery.

## No longer needed

None. This partial delivery does not withdraw any module or planned dependency of
`systemComposition`. The new pullback argument uses the general ring-sheaf adjunction
and evaluation comparisons; it needs neither a finite-free basis nor a finite-field
hypothesis.

## Where the brief, the DAG or earlier work was wrong

The pullback auxiliary theorem is stated for arbitrary schemes and can be proved for
arbitrary compatible constant coefficient towers. The finite-field-specific system
restriction package is therefore unnecessary for this auxiliary theorem. Evaluation
is used only to detect isomorphisms of ordinary system morphisms, never to infer an
equality of derived system morphisms. The coherent system composition assertion and
its planned whole-system argument remain unchanged.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
