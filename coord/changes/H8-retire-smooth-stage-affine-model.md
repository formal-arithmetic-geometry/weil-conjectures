# AlgebraicGeometry.Scheme.NoetherianApproximation.exists_smooth_affine_model

## Reason

Retire `Sheaf.AlgebraicGeometry.SmoothStageAffineModel` as requested by its row in
`coord/retire-items.tsv` and the human hand-off in
`coord/changes/retire-sheaf-twins-20261020.md`. The upstream theorem is already proved
and has the same qualified name. It directly supplies smoothness of the canonical
pullback projection, which is stronger than the former arbitrary-model conclusion.
The old comparison isomorphism did not have to commute with the structural maps.

The DAG attachment now names the official module and records its exact signature.
The node statement is aligned with this canonical formulation of Stacks Tag 0C0C,
`limits.tex`, `lemma-descend-smooth`. The new conclusion implies the old one by
choosing the canonical pullback, its second projection and the identity isomorphism;
this implication was compiled separately, with only the three permitted axioms.
No target statement or definition changes, so no target semantic review is reopened.

## Old

In `Sheaf.AlgebraicGeometry.SmoothStageAffineModel`:

```lean
theorem Scheme.NoetherianApproximation.exists_smooth_affine_model
    {S : Scheme.{u}} (N : S.NoetherianApproximation) {i : N.I}
    {Y X : Scheme.{u}} (p : Y ⟶ N.D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (f : X ⟶ S) [Smooth f] (a : X ⟶ Y)
    (H : IsPullback a f p (N.π.app i)) :
    ∃ (j : Over i) (Z : Scheme.{u}) (q : Z ⟶ N.D.obj j.left)
      (_ : LocallyOfFinitePresentation q) (_ : QuasiCompact q) (_ : QuasiSeparated q),
      Smooth q ∧ Nonempty (Z ≅ Limits.pullback p (N.D.map j.hom))
```

## New

The Sheaf copy is withdrawn through `deleted.txt` (the delivery tool installs an empty
module). The existing declaration in
`WeilConjectures.AlgebraicGeometry.SmoothStageAffineModel` is retained verbatim:

```lean
theorem Scheme.NoetherianApproximation.exists_smooth_affine_model
    {S : Scheme.{u}} (N : S.NoetherianApproximation) {i : N.I}
    {Y X : Scheme.{u}} (p : Y ⟶ N.D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (f : X ⟶ S) [Smooth f] (a : X ⟶ Y)
    (H : IsPullback a f p (N.π.app i)) :
    ∃ j : Over i, Smooth (pullback.snd p (N.D.map j.hom))
```

No upstream source file is delivered or edited.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SmoothStageAffineModel --uses
exists_smooth_affine_model` reports zero downstream modules. A fresh import scan
of both Lean roots and both quarantine roots likewise finds zero consumers.
The historical consumer in the retirement row has already migrated upstream.
Its official source was compiled separately from a sandbox copy in 2.7 seconds,
with no warnings.
A full node scan finds no other node citing this node through statement dependencies,
proof dependencies or proof-step uses, and no unit's `realized` field names it.
The official module's import closure contains no pair of Sheaf/upstream twins.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SmoothStageAffineModel | H8 assignment | Withdraw duplicate. |
| WeilConjectures.AlgebraicGeometry.SmoothStageAffineModel | unclaimed | Existing theorem retained verbatim; DAG attachment destination. |
| WeilConjectures.AlgebraicGeometry.NoetherianApproximationSmoothStage | unclaimed | Already imports the official module and uses its canonical conclusion; unchanged. |

## Status

landed 20261020T221216-L-4157596 2026-10-20 (merge of deliver/H8/Sheaf.AlgebraicGeometry.SmoothStageAffineModel)
