# constantExtensionWeilPush and constantExtensionWeilAdjunction

## Reason

Restore `Sheaf.Paper.ConstantExtensionMixedDescent` from the quarantine named in
`coord/rework.tsv`, retaining its complete mathematical interface and its node.
The recorded failure was a 60-second timeout. On the current published build,
the archived source already compiles in 6.7 seconds; with command profiling it
compiles in 7.6 seconds. The old timeout does not reproduce, so this delivery
makes no claim to have reproduced or measured that earlier bottleneck.

The actual definition repair seals the choice-based right adjoint and adjunction
against automatic unfolding. The direct-image functor has a proved, explicit
unfolding equation, and construction of its adjunction unfolds only that wrapper explicitly.
`constantExtensionPointPull` now states its functor result type explicitly, so
users need not infer that interface from the derived-pullback implementation.
Strict transparency is used throughout the definitions and sheet components;
the two relaxed options are scoped only to the large final theorem statement,
whose change-of-datum typeclass matching needs them. No timeout is increased,
no file is split, and no mathematical data or hypothesis is replaced.

## Old

The old construction, verbatim:

```lean
def constantExtensionWeilPush :
    sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ⥤
      sfCommonStageWeilSheaf D l hl X₀ Ω :=
  @Functor.rightAdjoint _ _ _ _
    (zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀))
    (constantExtensionWeilPull_isLeftAdjoint D m hm X₀ l hl Ω)

def constantExtensionWeilAdjunction :
    zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀) ⊣
      constantExtensionWeilPush D m hm X₀ l hl Ω :=
  @Adjunction.ofIsLeftAdjoint _ _ _ _
    (zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀))
    (constantExtensionWeilPull_isLeftAdjoint D m hm X₀ l hl Ω)

def constantExtensionPointPull
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ x
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)
```

Both `backward.isDefEq.respectTransparency` options were false file-wide, with
true overrides just on `constantExtensionCounitComponent`.

## New

The new definitions, verbatim:

```lean
@[irreducible]
def constantExtensionWeilPush :
    sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ⥤
      sfCommonStageWeilSheaf D l hl X₀ Ω :=
  @Functor.rightAdjoint _ _ _ _
    (zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀))
    (constantExtensionWeilPull_isLeftAdjoint D m hm X₀ l hl Ω)

@[irreducible]
def constantExtensionWeilAdjunction :
    zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀) ⊣
      constantExtensionWeilPush D m hm X₀ l hl Ω := by
  unfold constantExtensionWeilPush
  exact @Adjunction.ofIsLeftAdjoint _ _ _ _
    (zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀))
    (constantExtensionWeilPull_isLeftAdjoint D m hm X₀ l hl Ω)

def constantExtensionPointPull
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :
    generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ x
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)
```

`constantExtensionWeilPush_eq` proves the functor's defining equality by unfolding
that definition and reflexivity. It is deliberately not a simplification rule:
ordinary elaboration should use the functor interface. The existing adjunction
unit and counit projections remain its usable interface. The rewritten adjunction
selects exactly the same data by explicitly unfolding just its functor wrapper;
there is no equality transport in the resulting construction. The explicit point-pull result type is its existing
inferred type. Both theorem holes, all existing public signatures, the actual
sheet-component composite and every import are retained. No target meaning
changes and no mathematical statement review is reopened.

## Users

`python3 tools/downstream.py Sheaf.Paper.ConstantExtensionMixedDescent
--allow-missing --uses constantExtensionWeilPush constantExtensionWeilAdjunction
constantExtensionCounitComponent` reports zero current Lean importers and zero
external declaration users. An additional source search across `quarantine/`
finds these names only in this item's archive.

This does not withdraw the item: `thm-zl-real-mixed-by-curves` still cites its node,
and `dag/units/sk-i-dl-general-real.json` realizes its descent step through it.
The parent module is `WeilConjectures.DeligneLaumon.Reduction.RealSheaves`, whose
unfinished proof has not yet imported this module. No consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantExtensionMixedDescent | R1 | Restored with the adjoint definition repair and the same two theorem holes. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed in the local claim snapshot | DAG parent retained; no Lean import or adaptation. |

The existing node's Lean declaration list gains only the proved unfolding
equation. Its statement, dependencies, proof plan and unit attachment are intact.
The independent delivery reader should compare against the quarantined source,
not treat restoration as a newly invented theorem or as a withdrawal.

Validation: the complete production module and a separate scratch probe compile.
The probe proves heterogeneous equality of the adjunction and its unit with the
archived terms by explicit unfolding and reflexivity, and equality of the point
pullback with its original defining functor. Thus the extra type annotation and
reduction-control attributes do not change those data. The scratch probe is not
part of the delivery. Both existing theorem holes remain, including their
inherited axiom dependencies; no additional hole or axiom is introduced.

## Status

landed 20261024T190752-L-64149 2026-10-24 (merge of deliver/R1/Sheaf.Paper.ConstantExtensionMixedDescent)
