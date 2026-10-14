# AlgebraicGeometry.overlapPairMapOfModel

## Reason

Comparing the expanded chart isomorphisms while specializing the two restriction lemmas
exceeded the 60-second compilation limit. Name the two chart constructions and combine the
restriction lemmas in a proved generic private helper before specialization. The isomorphisms
are the same constructions as the previous local `ta` and `tb`; no data, hypotheses or
conclusions change. The delivered module compiles in approximately 25 seconds.

## Old

```lean
@[irreducible]
def overlapPairMapOfModel {k : I} (hjk : j ≤ k)
    (N : (d : U.I₀) → (U.X d).Modules)
    (α : (Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b a
          (pullback.fst (U.f a) (U.f b)))).obj (N a)) ⟶
      (Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b b
          (pullback.snd (U.f a) (U.f b)))).obj (N b))) :
    let q := overlapStageMap R f hij hjk
    let V := U.pullback₁ q
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
      (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b) :=
  let V := U.pullback₁ (overlapStageMap R f hij hjk)
  let ta := overlapModelStageComparison R f hij U a b hjk N a
    (pullback.fst (U.f a) (U.f b)) (pullback.fst (V.f a) (V.f b))
    (pullback.lift_fst _ _ _)
  let tb := overlapModelStageComparison R f hij U a b hjk N b
    (pullback.snd (U.f a) (U.f b)) (pullback.snd (V.f a) (V.f b))
    (pullback.lift_snd _ _ _)
  ta.inv ≫ (Scheme.Modules.pullback (overlapPairToModel R f hij U a b hjk)).map α ≫ tb.hom
```

## New

```lean
@[irreducible]
def overlapPairMapOfModel {k : I} (hjk : j ≤ k)
    (N : (d : U.I₀) → (U.X d).Modules)
    (α : (Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b a
          (pullback.fst (U.f a) (U.f b)))).obj (N a)) ⟶
      (Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b b
          (pullback.snd (U.f a) (U.f b)))).obj (N b))) :
    let q := overlapStageMap R f hij hjk
    let V := U.pullback₁ q
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
      (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b) :=
  (overlapModelStageComparisonFst R f hij U a b hjk N).inv ≫
    (Scheme.Modules.pullback (overlapPairToModel R f hij U a b hjk)).map α ≫
    (overlapModelStageComparisonSnd R f hij U a b hjk N).hom
```

The new public irreducible definitions `overlapModelStageComparisonFst` and
`overlapModelStageComparisonSnd` are exactly the old local `ta` and `tb`, respectively.
Their defining equations provide the API used in the proof. All existing declaration
signatures and visibility remain identical. Definitions contain no postponed proof or data.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OverlapPairModelTransport | C1 | Pair-map body uses the two named chart constructions; recovery theorem is proved. |
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapPairSingleStage | unclaimed | Statement mentions the pair map; original source compiled unchanged against the changed module (47.7 s). No adaptation. |

The body is definitionally the same map, so its mathematical meaning is unchanged.
The target-statement review required by AGENTS.md §4 and stage 2 §4 is reopened for
any target using this definition; the reviewer can unfold the two named constructions to
recover the original term. No statement of `Challenge.lean` is edited.

## Status

landed 20261014T004057-L-2832340 2026-10-14 (merge of deliver/C1/Sheaf.AlgebraicGeometry.OverlapPairModelTransport)
