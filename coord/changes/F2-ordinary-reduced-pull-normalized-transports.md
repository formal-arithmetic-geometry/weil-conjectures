# CategoryTheory.ConstantCompletion.ordinaryReducedPull_transport_eq

## Reason

The assigned statement was already marked STATEMENT-DISPUTED. It falsely asserted
compatibility for every pair of independently chosen source and target isomorphisms.
On the terminal site with identity inverse image, take A = F₃, I = 0 and the nonzero
rank-one coefficient module. Multiplication by -1 is a nonidentity natural automorphism
of the finite-module functor. Postcomposing t by it preserves every old hypothesis
and changes the claimed composite. An equation for all such choices is impossible.

The source argument and unchanged parent require a pair with compatible insertion
normalizations. This repair constructs that pair, with the same fixed canonical
finite quotient model. It proves the equation through the scalar-extension Hom
adjunctions and the prescribed insertion equation for ordinaryPullComparison.
It changes no definition, instance, axiom, target or parent theorem statement.

## Old

```lean
theorem ordinaryReducedPull_transport_eq (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ)
    (s : (res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⋙
      change (quotient J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1)))))
    (t : (pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) ⋙
      change (quotient J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1))))) :
    Functor.whiskerRight (ordinaryPullComparison F A I)
        (change (quotient J' A I n)) ≫ t.hom = s.hom
```

The section's geometric right-adjoint data did not occur in this old statement.
The public import was ConstantCompletionOrdinaryReducedPullTargetIso.

## New

The geometric arguments V, adj : L ⊣ V and PreservesFiniteLimits L are included.

```lean
theorem ordinaryReducedPull_transport_eq
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [hL : PreservesFiniteLimits L] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    ∃ (s : (res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⋙
        change (quotient J' A I n)) ≅
        (change (projection J A I n) ⋙
          pull F (constantMap F (A ⧸ I ^ (n + 1)))))
      (t : (pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) ⋙
        change (quotient J' A I n)) ≅
        (change (projection J A I n) ⋙
          pull F (constantMap F (A ⧸ I ^ (n + 1))))),
      Functor.whiskerRight (ordinaryPullComparison F A I)
          (change (quotient J' A I n)) ≫ t.hom = s.hom
```

The statement imports ConstantCompletionDerivedPull publicly. The proof privately
imports all declarations of ConstantCompletionOrdinaryFinitePullExistence and
ConstantCompletionOrdinaryFinitePullUniqueness to reuse their proved scalar
reassociation and adjunction helpers. The normalized target projection comparison
is constructed directly, avoiding the old unnormalized existential helper chain.
All added local helpers are private, fully proved theorems.

The existing node
lem-weil-pbc-constant-completion-ordinary-finite-pull-existence also receives a
metadata repair: its statement explicitly spells out its unchanged geometric
context, and its dependencies refer to the coefficient/inverse-image definitions,
tensor-section calculus and normalized module adjunction its proof actually uses.
The old reference to the parent completion-equivalence theorem was an ownership
reference, not a Lean dependency. Retaining it while citing this proved theorem
would create a dependency cycle. That Lean module, its signatures and its proofs
are unchanged. Its statement_change records all existing citers.

## Users

The source scan of every Lean module finds one caller of the changed declaration.
`tools/downstream.py ... --direct --uses ordinaryReducedPull_transport_eq` also
reports exactly this direct importer. Other transitive importers contain no use
of this declaration or of the four removed transport helper declarations.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransportEquation | F2 | Repaired statement and complete normalized proof; one old textual hole, no remaining or added holes. |
| Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransport | unclaimed (current server claims checked) | Preserve its exact signature and visibility. Replace the two independent choices and false universal equation application by obtaining the compatible pair from the repaired theorem. |
| Sheaf.Paper.ConstantCompletionOrdinaryFinitePullExistence | unclaimed (current server claims checked) | DAG metadata only; no Lean change or new mathematical premise. |

The four bypassed helper modules are left intact: ConstantCompletionOrdinaryReducedPullSourceIso,
ConstantCompletionOrdinaryReducedPullTargetIso, ConstantCompletionOrdinaryReducedPullTargetProjectionIso,
and ConstantCompletionOrdinaryReducedPullTargetProjectionModelIso. No surviving caller uses
their declarations outside that helper chain. No adopted WeilConjectures source file changes.

## Status

landed 20261028T055644-L-789631 2026-10-28 (merge of deliver/F2/Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransportEquation)
