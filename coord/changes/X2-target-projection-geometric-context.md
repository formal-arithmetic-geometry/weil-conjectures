# CategoryTheory.ConstantCompletion.ordinaryReducedPull_targetProjectionIso and target context

## Reason

The old projection-model statement is false outside geometric inverse images.
`InverseImageData L` supplies algebraic lifts and a natural constant-ring isomorphism,
but asserts neither a right adjoint to L nor preservation of colimits. Stacks 03EL
(`sites-modules.tex`, `lemma-tensor-product-pullback`) assumes a morphism of ringed topoi
and explicitly uses the inverse/direct-image adjunction. The existing proved generic
`finiteInverseScalar_exists` helper requires that adjunction and finite-limit preservation.
Restore these hypotheses in the item and its target-transport caller, then pass the
already available V and adj through `ordinaryReducedPull_transport`.

Counterexample to the original interface: let L take C2-invariants of C2-sets, viewed
as sheaves on the one-object group site with trivial topology, to sets. L preserves
finite limits and constant objects. Invariants of ring and module objects supply
coherent algebraic lifts. Take A = ℤ, I = (2), n = 0, and the completed-coefficient
module M = ℤ₂ with sign action. The completed coefficient ring has trivial action,
and `completedMap` is the identity. The old left functor gives M^C2 / 2 = 0,
whereas the right functor gives (M / 2)^C2 = ℤ/2. Thus left exactness alone also
fails to imply the old statement. The geometric adjunction excludes this example.
This is the same omitted-context defect independently corrected on the source side
in the reviewed `D6-ordinary-reduced-pull-geometric-context.md` change record.

The proof uses only `limit.lift_π` and the already proved private helpers
`finiteInverseScalar_exists` and `finiteScalarComposite_exists` from
`Sheaf.Paper.ConstantCompletionOrdinaryFinitePullExistence`, imported with `import all`.
The former is generic in a ring map and uses the normalized module adjunction;
the latter is ordinary uniqueness of left adjoints for successive scalar extensions.
There is no new theorem, arbitrary witness assumption, or hole. A separate
`#print axioms ordinaryReducedPull_targetProjectionIso` compilation reports exactly
propext, Classical.choice and Quot.sound.

No definition, instance, attribute, universe, or target statement changes. The unit's
statement and proof route remain the same. No source-library module is edited.
The item's unnecessary public source-transport import is replaced by the smaller
`ConstantCompletionInverseImage` statement import. Its sole importer, TargetIso,
already imports SourceIso publicly, so that importer loses no declarations.

## Old

In the existing section context for F (TargetIso's unused V and adj were absent
from its elaborated theorem; finite limits were explicitly omitted):

```lean
theorem ordinaryReducedPull_targetProjectionIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    Nonempty ((pull F (completedMap F A I) ⋙ change (projection J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1)))))

theorem ordinaryReducedPull_targetIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    Nonempty ((pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) ⋙
        change (quotient J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1)))))
```

## New

In the same section context for F:

```lean
theorem ordinaryReducedPull_targetProjectionIso
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    Nonempty ((pull F (completedMap F A I) ⋙ change (projection J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1)))))

theorem ordinaryReducedPull_targetIso
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    Nonempty ((pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) ⋙
        change (quotient J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1)))))
```

The proof call in `ConstantCompletionOrdinaryReducedPullTransport` becomes
`ordinaryReducedPull_targetIso F V adj A I n` in place of
`ordinaryReducedPull_targetIso F A I n`. An explicit private proof import of TargetIso
records this direct dependency (previously available only through TransportEquation).
Its signature is unchanged. The source-transport application is also given its required
`Nonempty` isomorphism type and discharged with
`solve_by_elim only [ordinaryReducedPull_sourceIso F, V, adj]`. This still uses exactly
the same source lemma. Argument inference lets the proof elaborate against both the
published source signature and its current reviewed geometric repair, which was not
yet published during the first delivery compile. Both source versions are checked;
no source declaration is duplicated or modified.

## Users

`tools/downstream.py` with both changed modules and `--uses` reports only the
TargetIso caller of targetProjectionIso and the Transport caller of targetIso.
A whole-library declaration-name search confirms these are the only uses.
The direct importers and the intervening chain are included below. Current server
claim files contain no claim for either adapted existing consumer. The unchanged
SourceIso, TransportEquation and OrdinaryReducedPull are copied only for compilation
against current source dependencies and removed from the delivery packet afterwards.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetProjectionModelIso | X2 | Restore geometric context and fully prove the corrected statement. |
| Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso | unclaimed | Restore and pass geometric context to the projection-model comparison; same conclusion. |
| Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransport | unclaimed | Pass V and adj to targetIso, import that proof dependency, and infer the source lemma arguments. |
| Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransportEquation | F2 | Unchanged direct importer of TargetIso; compile against the correction. |
| Sheaf.Paper.ConstantCompletionOrdinaryReducedPullSourceIso | unclaimed | Unchanged dependency; current reviewed geometric signature used during the chain check. |
| Sheaf.Paper.ConstantCompletionOrdinaryReducedPull | unclaimed | Unchanged direct importer of Transport; compile against the corrected chain. |

Before adapting TargetIso, compiling it against the corrected item produced:
`Application type mismatch`: A was supplied where a right-adjoint functor was
expected, and `failed to synthesize PreservesFiniteLimits L`. The caller cannot
supply the geometric hypotheses under its old signature. The restored hypotheses
are exactly those its Transport caller already has. No module held by another
group is adapted. Both changed statement nodes record their correction and audit
all current DAG citers. The Transport node already includes the geometric context.

## Status

landed 20261028T072501-L-1954025 2026-10-28 (merge of deliver/X2/Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetProjectionModelIso)
