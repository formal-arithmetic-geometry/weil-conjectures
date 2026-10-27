# AlgebraicGeometry.exists_smooth_finiteCover_dimension_cut

## Reason

Implement the single-cut assembly using the existing finite-cover irreducibility theorem.
The projective prescribed-point smooth-system interface still needs its affine restriction
and basis reindexing; isolate that strictly smaller input as a separate named theorem.

## Old

The assigned theorem had the following signature followed by `:= by sorry`:

```lean
theorem exists_smooth_finiteCover_dimension_cut {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsAffine X] [ConnectedSpace X]
    {d : ℕ} (hd : 2 ≤ d) [SmoothOfRelativeDimension d f]
    {T : Scheme.{u}} (π : T ⟶ X) [IsFinite π] [Etale π] [ConnectedSpace T]
    (S : Finset (Spec (.of k) ⟶ X)) (hS : S.Nonempty)
    (hS' : ∀ s ∈ S, s ≫ f = 𝟙 _) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X), IsClosedImmersion j ∧ IsAffine Y ∧
      SmoothOfRelativeDimension (d - 1) (j ≫ f) ∧ ConnectedSpace Y ∧
      (∀ s ∈ S, ∃ t, t ≫ j = s) ∧ ConnectedSpace ↑(pullback π j)
```
There was no `AlgebraicGeometry.exists_smooth_affine_prescribedPoint_linearSystem`.
The assigned module opened `CategoryTheory CategoryTheory.Limits` only.

## New

The assigned signature above and original public imports stay verbatim. Its proof now performs
rational coefficient selection, the finite-cover application, dimension conversion and
factorization. New private proof imports expose the existing geometry APIs only locally.
The new theorem in `Sheaf.AlgebraicGeometry.BertiniSmoothAffineLinearSystem` states just the
smooth affine coordinate-system input, with one whole-proof sorry. Its module opens
`CategoryTheory CategoryTheory.Limits Opposite` and the `AlgebraicGeometry` scope for its
signature; no global instance or existing definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BertiniFiniteCoverDimensionCut | K4 | Proof filled from the new interface and existing finite-cover theorem; unchanged signature. |
| Sheaf.AlgebraicGeometry.BertiniSmoothAffineLinearSystem | new in this delivery | New smooth-system interface and statement imports. |
| WeilConjectures.AlgebraicGeometry.Bertini | unclaimed consumer of the original item on the server | Original interface unchanged; no adaptation. |

## Status

landed 20261025T163814-L-853757 2026-10-25 (merge of deliver/K4/Sheaf.AlgebraicGeometry.BertiniFiniteCoverDimensionCut)
