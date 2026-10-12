# exists_chow_modification_data

## Reason

Repair of return X-85771 (E1/D1, H1, H8): The geometric witness now includes n, the projective immersion e, and its equation over Spec A. The identity q = 𝟙 Z with L = ⊤ is insufficient unless an immersion of Z into finite projective space over A is also supplied.
The new theorem is isolated in its own module, `Sheaf.AlgebraicGeometry.ChowModificationData`.
No existing library or Challenge signature changes.

## Old

No declaration exists on the delivery base. The returned draft placed this helper in
`Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization` and omitted the projective immersion
from the conclusion.
That returned interface is replaced before landing.

## New

```lean
theorem exists_chow_modification_data
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {Z : Scheme.{u}} [IsNoetherian Z] (f : Z ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hZ : Nonempty Z) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Z) (_ : IsProper q) (L : Z.IdealSheafData)
      (n : ℕ)
      (e : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A))),
      IsImmersion e ∧
      e ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ↘ Spec (.of A)) =
        q ≫ f ∧
      (L.support.compl : Set Z).Nonempty ∧
      IsIso (pullback.snd q (Scheme.Opens.ι L.support.compl))
```

The theorem has a source-and-proof docstring. Its node carries the corrected argument and
module path, without copied review or landing claims.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization | W3 | Imports the new helper privately; passes the immersion data between helpers and forgets it only in the final existential tuple. |

## Status

landed 20261012T194153-L-469364 2026-10-12 (merge of deliver/W3/Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization)
