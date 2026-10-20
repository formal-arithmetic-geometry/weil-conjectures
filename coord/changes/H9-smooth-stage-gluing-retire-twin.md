# AlgebraicGeometry.Scheme.NoetherianApproximation.smooth_stage_of_affine_models

## Reason

The assigned Sheaf module is already proved and unused. Upstream now has a theorem
of the same name with the intended comparison over the base, and the active parent
`WeilConjectures.AlgebraicGeometry.NoetherianApproximationSmoothStage` uses that theorem.
Retire the unused Sheaf twin and attach its node to the existing upstream declaration.
A bare scheme isomorphism, as in the old hmodel, does not by itself identify the
structure morphism q with the pullback projection. The old theorem remains true
because its separate smooth-limit hypotheses imply the result by general affine-limit
descent; its proof ignores hmodel. The upstream interface describes the actual gluing
step, and its proof just transports smoothness along the specified base isomorphism.

## Old

Module `Sheaf.AlgebraicGeometry.SmoothStageGluing`:

```lean
theorem Scheme.NoetherianApproximation.smooth_stage_of_affine_models
    {S : Scheme.{u}} (N : S.NoetherianApproximation) {i : N.I}
    {Y X : Scheme.{u}} (p : Y ⟶ N.D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (f : X ⟶ S) [Smooth f] (a : X ⟶ Y)
    (H : IsPullback a f p (N.π.app i))
    (hmodel : ∃ (j : Over i) (Z : Scheme.{u}) (q : Z ⟶ N.D.obj j.left)
      (_ : LocallyOfFinitePresentation q) (_ : QuasiCompact q) (_ : QuasiSeparated q),
      Smooth q ∧ Nonempty (Z ≅ Limits.pullback p (N.D.map j.hom))) :
    ∃ j : Over i, Smooth (pullback.snd p (N.D.map j.hom))
```

## New

Withdraw `lean/Sheaf/AlgebraicGeometry/SmoothStageGluing.lean` via deleted.txt.
Reattach the node to the already existing, unchanged upstream theorem:

```lean
theorem Scheme.NoetherianApproximation.smooth_stage_of_affine_models
    {S : Scheme.{u}} (N : S.NoetherianApproximation) {i : N.I}
    {Y : Scheme.{u}} (p : Y ⟶ N.D.obj i)
    (hmodel : ∃ (j : Over i) (Z : Scheme.{u}) (q : Z ⟶ N.D.obj j.left)
      (e : Z ≅ pullback p (N.D.map j.hom)),
        e.hom ≫ pullback.snd p (N.D.map j.hom) = q ∧ Smooth q) :
    ∃ j : Over i, Smooth (pullback.snd p (N.D.map j.hom))
```

The node's prose statement already asks for smooth model and comparison data; the
comparison is now explicitly over the stage base in its recorded Lean statement.
Neither the prose statement nor any target or definition changes. No source-library
file is edited or withdrawn.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SmoothStageGluing | H9 (assigned item) | Withdraw unused twin; node attaches upstream. |
| WeilConjectures.AlgebraicGeometry.SmoothStageGluing | unclaimed | Existing replacement; unchanged. |
| WeilConjectures.AlgebraicGeometry.NoetherianApproximationSmoothStage | unclaimed | Already uses upstream gluing with Iso.refl and Category.id_comp; unchanged. |

`tools/downstream.py` reports zero modules downstream of the Sheaf module and only
the module itself when searching its declaration. Full searches of lean/Sheaf,
lean/WeilConjectures and quarantine find no importer of the withdrawn module.
The only occurrence of its node id in dag/nodes is its own node: there are no
stmt_deps, proof_deps, or step-uses parents to adapt. Its unit's realized statement
and step lists do not require this node. No rework or return entry names the item.
The actual active parent argument is retained verbatim: first obtain a smooth
canonical pullback stage from exists_smooth_affine_model, then pass that projection
as q with e = Iso.refl and Category.id_comp to the upstream gluing theorem.

Edge cases: the comparison is over the same base, so transport also works for an
empty scheme; no nonempty or connectedness hypothesis is introduced. Empty diagrams
are excluded by the existing NoetherianApproximation structure. This is a gluing
interface reconciliation, not a replacement of a unit's descent argument.

## Status

landed 20261020T221217-L-4158000 2026-10-20 (merge of deliver/H9/Sheaf.AlgebraicGeometry.SmoothStageGluing)
