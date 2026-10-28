# CategoryTheory.ConstantCompletion.ordinaryReducedPull_sourceIso and transport context

## Reason

The source transport and its immediate transport caller declared section variables
`V`, `adj : L ⊣ V`, and finite-limit preservation, but did not retain them in their
elaborated theorem signatures. Stacks 03EL assumes a morphism of ringed topoi and
uses the inverse/direct-image adjunction. The existing
`ordinaryFinitePull_existsUnique` explicitly requires these geometric hypotheses.
Restore them, then prove the source transport by the exact existing DAG plan.

The original interface is false even for a left exact algebraic functor preserving
constant rings. Take C2-invariants from C2-sets to sets, A = ℤ, I = (2), n = 0,
and the completed module ℤ₂ with sign action. Its invariant module is zero,
whereas its reduction is ℤ/2 with trivial action. Thus the claimed two functors
send this module to zero and ℤ/2 respectively. The restored adjunction excludes
this direct-image example. This is a source-based statement repair, not a proof
of the invalid original generality.

The parent `ordinaryReducedPull_isIso` already has exactly the geometric context
and now passes V and adj to its transport lemma. All public imports, definitions,
instances, attributes and target statements stay verbatim. No module of
lean/WeilConjectures is edited. The blueprint unit route is retained.

## Old

In the existing section context containing F, V and adj, the latter two unused
variables and the finite-limit instance were absent from both elaborated types:

```lean
theorem ordinaryReducedPull_sourceIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    Nonempty ((res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⋙
        change (quotient J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1)))))

theorem ordinaryReducedPull_transport (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    ∃ (X : Mod (completed J A I) ⥤ Mod (finite J' A I n))
      (s : (res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⋙
        change (quotient J' A I n)) ≅ X)
      (t : (pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) ⋙
        change (quotient J' A I n)) ≅ X),
      Functor.whiskerRight (ordinaryPullComparison F A I)
          (change (quotient J' A I n)) ≫ t.hom = s.hom
```

## New

In the same context for F:

```lean
theorem ordinaryReducedPull_sourceIso
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    Nonempty ((res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⋙
        change (quotient J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1)))))

theorem ordinaryReducedPull_transport
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    ∃ (X : Mod (completed J A I) ⥤ Mod (finite J' A I n))
      (s : (res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⋙
        change (quotient J' A I n)) ≅ X)
      (t : (pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) ⋙
        change (quotient J' A I n)) ≅ X),
      Functor.whiskerRight (ordinaryPullComparison F A I)
          (change (quotient J' A I n)) ≫ t.hom = s.hom
```

The only edit to `ordinaryReducedPull_isIso` is the call
`ordinaryReducedPull_transport F V adj A I n` in place of
`ordinaryReducedPull_transport F A I n`. Its signature stays verbatim.

## Users

`tools/downstream.py ... --direct --uses ordinaryReducedPull_sourceIso
ordinaryReducedPull_transport` and a full transitive declaration-name scan find
only the two caller uses shown below. The direct importers are TargetIso and
OrdinaryReducedPull. Both are compiled against the changed source, along with
the intervening TransportEquation and the CompletedFinitePull consumer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantCompletionOrdinaryReducedPullSourceIso | D6 | Restore geometric context; close the only proof hole. |
| Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransport | unclaimed | Restore context already required by its node; pass V and adj to sourceIso. |
| Sheaf.Paper.ConstantCompletionOrdinaryReducedPull | unclaimed | Pass its existing V and adj to transport; signature unchanged. |
| Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso | C6 | Unchanged direct importer; compile against sourceIso. |
| Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransportEquation | B8 | Unchanged intervening importer; compile against sourceIso. |
| Sheaf.Paper.ConstantCompletionCompletedFinitePull | not adapted | Unchanged consumer of ordinaryReducedPull_isIso; compile against the full chain. |

Holder information was read from current server claim records. Neither adapted
consumer is held by another group. No forced adaptation of a held module occurs.
The source node records the statement correction and its only DAG citer. The
transport node already states the geometric context, so only its Lean attachment
changes. The source proof follows its existing plan and adds no proof dependency.

## Status

landed 20261028T020303-L-2489734 2026-10-28 (merge of deliver/D6/Sheaf.Paper.ConstantCompletionOrdinaryReducedPullSourceIso)
