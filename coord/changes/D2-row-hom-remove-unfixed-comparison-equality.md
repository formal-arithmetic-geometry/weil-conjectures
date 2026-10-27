# AlgebraicGeometry.ProEtaleWeilSheaf.native_row_hom_eta_eq

## Reason

STATEMENT-DISPUTED: compatibility with arbitrary representative isomorphisms does
not identify a derived comparison with a fixed comparison. Given compatible data,
negate the native representative isomorphism in every bidegree and negate the
comparison natural isomorphism (both hom and inverse). Naturality remains true.
The compatibility equation has both sides negated, with the very same canonical
chain comparison. The functors, nativeModel and ordinaryModel do not change.
On a nonzero internal Hom over the characteristic-zero coefficient field this
changes the comparison. For example take the coefficient unit on the geometric
point over a finite field of characteristic different from ell, in degree zero.
Its endomorphism object is nonzero and multiplication by -1 differs from 1.
Thus the universal equality assertion is false. It is removed, not weakened.

The unchanged native_row_hom_comparison is now proved by explicit construction
with m.derived itself, so its comparison equality is HEq.rfl. The independent
native_row_hom_data theorem is proved by the same construction. Neither theorem
uses the withdrawn assertion, and the unit route is unchanged.

## Old

```lean
theorem native_row_hom_eta_eq
    (m : TwoInjectiveHomModel (k₀ := k₀) (l := l) (X := X))
    (M : NativeClosedHomModels k₀ l X)
    (η : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (hM : HEq M.weilHom m.hom) (hO : HEq M.ordinaryHom m.underlyingHom)
    (hC : NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) η) :
    HEq η m.derived
```

## New

The false declaration is removed. A STATEMENT-DISPUTED comment remains at its
former location. Its DAG node is preserved with a null Lean attachment and the
withdrawal reason. The main comparison statement and data statement are verbatim;
their proofs construct rowClosedModel and use m.derived directly.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NativeWeilRowHomComparison | D2 | The sole consumer of the removed declaration was the main comparison proof; replaced by the explicit construction. |
| Sheaf.Paper.NativeWeilClosedForgetful | unclaimed in the shared claim records | Sole direct importer; uses only native_row_hom_comparison, whose signature and visibility are unchanged. Compiled against this delivery. |

`tools/downstream.py Sheaf.Paper.NativeWeilRowHomComparison --uses
native_row_hom_eta_eq` found only the item module as a declaration user.
A repository-wide Lean and DAG search found no other consumer. The sole DAG
citer is lem-sf-weil-native-row-hom-comparison, whose proof dependency is updated.
No public imports, shared definitions, target signatures or upstream declarations
change. No forced adaptation is needed.

## Status

landed 20261026T194521-L-2384465 2026-10-26 (merge of deliver/D2/Sheaf.Paper.NativeWeilRowHomComparison)
