## What changed

Marked `native_exceptional_ordinary_counit_carrier` STATEMENT-DISPUTED without
changing its signature or replacing it by a weaker theorem. Added proved private
helpers in the item module certifying the obstruction: an invertible triangular
comparison, its naturality square, an invertible swapping action, the resulting
counit obstruction, and the implication from the actual zero-shift invariant
condition to ordinary equivariance. The extra Mathlib import is proof-only.
The node records this diagnosis and retains the original construction plan and
its dependencies pending repair. No other existing module is changed.

Validation: `lcompile.py` compiled the delivered item with all private helpers
in 11.1 seconds, exit 0 and no warnings. The delivered code adds no transparency
overrides or timing-limit changes.

## Proved and sorry left

Closed: 0 of the item's 1 holes. Added: 0 holes. Split off: 0.

The only remaining hole is
`WeilConjectures.NativeExceptionalForgetful.native_exceptional_ordinary_counit_carrier`
(node `lem-sf-native-exceptional-ordinary-counit-carrier`). Its statement is
believed false for the explicit reason below. No claim is made to have proved it.

The private declarations `triangularComparison`, `triangularComparison_naturality`,
`swappingAction`, `triangular_counit_obstruction`, and
`invariant_implies_equivariant` have complete proofs/constructions. They certify
the categorical calculation; the realization of that calculation by a finite
etale cover is a mathematical counterexample described below, not a Lean proof
of the negation of the geometric theorem.

## No longer needed

None. The original theorem remains unresolved and no dependency, public import,
module or node is pruned. No further copy of the carrier obligation is introduced.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the arbitrary comparison `a` need not be compatible with
Frobenius. The source's final exceptional-adjunction sentence uses the specified
normalized comparison and its mate. The dependency
`NativeWeilScalarFrobeniusCounit.scalar_frobenius_counit` likewise concerns that
specified comparison. Its conclusion does not justify the current universal
quantifier over natural comparison isomorphisms.

Here is the counterexample. Take the finite etale morphism
`Spec(F_(q^2)) -> Spec(F_q)` with any allowed coefficient prime. Its geometric
source consists of two points interchanged by Frobenius. On these components a
native complex has underlying complexes A and B and structure isomorphisms
phi : B -> A and psi : A -> B. Ordinary compact support is A direct-sum B,
with Frobenius matrix theta = [[0, phi], [psi, 0]]. Take L to be the nonzero
constant coefficient unit at the target, with identity Frobenius. Ordinary
exceptional inverse image is (L,L), and the counit is the sum map.

Let alpha be the normalized comparison. For every native H define the ordinary
automorphism tau_H = [[1, phi], [0, 1]] of its sum. Its inverse is
[[1, -phi], [0, 1]]. A native arrow with components f and g satisfies
g followed by phi' = phi followed by f, which is precisely the naturality
square for tau. Thus a_H = alpha_H followed by tau_H is an allowed natural
comparison isomorphism in the current Lean statement. It can be transported to
the common-stage categories using the fully faithful realization. No
Frobenius-compatibility condition in the statement excludes it.

Suppose a carrier existed for this a and L. On the two components its ordinary
identification e gives isomorphisms eA : A -> L and eB : B -> L. The displayed
transported-arrow equation, after the prescribed realization isomorphisms,
identifies t with tau_H followed by the row (eA,eB). Hence its components are
eA and (phi followed by eA) + eB. The zero-shift invariant condition is ordinary
equivariance theta followed by t = t, since the target action is the identity.
Restrict this equation to the second summand. It says
phi followed by eA = (phi followed by eA) + eB. Cancellation gives eB=0.
As eB is an isomorphism, L is zero, a contradiction.

The checked `triangular_counit_obstruction` proves exactly that cancellation and
zero-object consequence in every preadditive category; it does not assume
characteristic different from two. The other helpers verify invertibility,
naturality and the zero-shift implication. For a derived H, apply degree-zero
cohomology: the ordinary isomorphism with (L,L) concentrates the underlying
complex in degree zero, and its two cohomology maps are still isomorphisms.
Finite etale direct image and these component decompositions are exact, so the
same calculation applies; higher derived extensions cannot avoid it.

A repair should retain the normalized comparison together with its action
compatibility, or existentially choose that comparison with the carrier.
The parent `NativeExceptionalOrdinaryCounitWitness` also quantifies over an
arbitrary a; it needs coordinated review. I have preserved its signature and
all other callers, and have not silently weakened this item or any target.

Searches run: LeanFinder for lifting a Frobenius-equivariant adjunction counit
along fully faithful realization found generic adjunction restriction lemmas,
not the missing compatibility; the Loogle query for Adjunction and IsoAlgebra
returned a query error, not an exact match. Local searches found
`CyclicDerivedLiftedCounitRepresents` (whose explicit hc hypothesis supplies
exactly the missing Frobenius compatibility), scalar-counit normalization,
and the existing Brown adjoint construction. Neither permits the arbitrary
comparison in this statement.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitCarrier": "00bc6b9e0c1ed9394c39d215ee6de33ac82f1f83"}, "results": {"Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness": {"hash": "0e4c52d3e1311304c4ad0b61faf22e3ef3dbbb90", "status": "OK"}}, "seconds": 133, "time": "2026-10-28T10:20:10+0800", "transitive": 0, "version": 1}
```

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
