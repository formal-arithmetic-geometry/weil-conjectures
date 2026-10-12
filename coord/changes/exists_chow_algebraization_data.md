# exists_chow_algebraization_data

## Reason

Repair of return X-85771 (E1/D1, H1, H8): The algebraization helper now assumes the finite projective immersion e and the equation he over Spec A. Its projective closure is constructed from this immersion; properness of q alone is no longer asserted to provide a compactification.
The new theorem is isolated in its own module, `Sheaf.AlgebraicGeometry.ChowAlgebraizationData`.
No existing library or Challenge signature changes.

## Old

No declaration exists on the delivery base. The returned draft placed this helper in
`Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization` and omitted the projective immersion
from the hypotheses.
That returned interface is replaced before landing.

## New

```lean
theorem exists_chow_algebraization_data
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} [IsNoetherian Z] (f : Z ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Q : Z.IdealSheafData)
    (hQ : Q = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (G : CoherentFormalModule Z Q)
    (hR : Scheme.Modules.HasSupportProperOver f (G.obj.obj (op 0)))
    (Y : Scheme.{u}) (q : Y ⟶ Z) [IsProper q] (n : ℕ)
    (e : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)))
    [IsImmersion e]
    (he : e ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ↘ Spec (.of A)) =
      q ≫ f)
    (L : Z.IdealSheafData)
    (hL : (L.support.compl : Set Z).Nonempty)
    (hIso : IsIso (pullback.snd q (Scheme.Opens.ι L.support.compl))) :
    ∃ F : CoherentModules Y,
      Nonempty (G.obj ⋙ Scheme.Modules.tensorPullback q ≅
        formalCompletionSystem (Q.comap q) F.obj) ∧
      Scheme.Modules.HasSupportProperOver f ((Scheme.Modules.pushforward q).obj F.obj)
```

The theorem has a source-and-proof docstring. Its node carries the corrected argument and
module path, without copied review or landing claims.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization | W3 | Imports the new helper privately; passes the immersion data between helpers and forgets it only in the final existential tuple. |

## Status

landed 20261012T194153-L-469364 2026-10-12 (merge of deliver/W3/Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization)
