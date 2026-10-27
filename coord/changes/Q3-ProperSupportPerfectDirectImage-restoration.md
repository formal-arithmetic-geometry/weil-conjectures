# AlgebraicGeometry.properSupport_perfect_directImage

## Reason

Restore the module quarantined in coord/rework.tsv on 2026-10-20. Its recorded failure
is an unknown `derivedPullback` in the public theorem statement because its owner was
only privately reachable. The archived public Sheaf imports for derived pullback and
the single-complex stalk condition are now empty withdrawn modules. Their definitions
and instances belong to the corresponding WeilConjectures modules. The statement uses
both derivedPullback and the tensor-pullback Additive instance needed to form its
termwise complex functor, so both owners must be publicly imported.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso
```

The archived theorem signature is the reference and remains verbatim.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso
```

The base-change theorem's proof import points directly to the owner recorded by
lem-pc-relatively-flat-tensor-base-change-iso; its old Sheaf path is only a re-export.
The restored module is lean/Sheaf/AlgebraicGeometry/ProperSupportPerfectDirectImage.lean.
No signature, definition, attribute or DAG dependency changes. The sole proof edit
is `SheafOfModules.overFunctor` to `SheafOfModules.overFunctor.{u}` at the final
restriction transport. The first repaired compile reported an unsolved universe
constraint `?u + 1 = u` there; the explicit module-sheaf universe fixes the
inference without changing the argument or any public type.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage
--allow-missing --uses properSupport_perfect_directImage` finds zero live importers.
Separate searches of lean/ and quarantine/ identify the two archived consumers below;
both use only the first conjunct of the same theorem with identical arguments.
No archived consumer is withdrawn or adapted by this repair. Claim files for both
consumers were absent in this snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | quarantined; no claim found | Same theorem application and perfectness conclusion; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | quarantined; no claim found | Same theorem application and perfectness conclusion; no adaptation. |

The DAG also retains references from lem-sc-proper-flat-derived-direct-image-perfect-universes,
lem-sc-proper-flat-image-global-hom-base-change-isIso, lem-sfb-relative-acyclic-direct-image,
and lem-sfb-flat-proper-pseudocoherent-direct-image. All remain valid because the theorem
is unchanged. The item's lean attachment and all six proof dependencies are preserved.
The unit route, target signatures and meanings are unchanged.

The node proof remains accurate: it already records applying the exact restriction
functor to the model isomorphism and composing with the strictly perfect witness.
No node-field edit is necessary for the explicit universe annotation.

Validation: lcompile.py compiled the repaired file cleanly in 13.6 seconds.
import_direction.py permits each of the three replacement imports. The delivered
module has zero holes, and the signature matches the archived declaration verbatim.

## Status

landed 20261025T095736-L-3475833 2026-10-25 (merge of deliver/Q3/Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage)
