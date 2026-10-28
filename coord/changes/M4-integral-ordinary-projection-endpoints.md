# WeilConjectures.integralOrdinaryProjection_endpointCompatibility

## Reason

The old statement quantifies over two independently chosen endpoint isomorphisms and
asserts they commute. Composing just the target isomorphism with a nontrivial
automorphism preserves its hypotheses and destroys the asserted equality. The paper
instead constructs compatible endpoints. Construct an isomorphism of projection
arrows using the scalar mate square, and extract its endpoints in the sole consumer.
No target or consumer statement changes. The unit route remains the proper/open
factorization followed by finite coefficient realization.

## Old

```lean
theorem integralOrdinaryProjection_endpointCompatibility
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((PurCompactSupport.completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((PurCompactSupport.completed l E).ring Y))
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ)
    (d : IntegralOrdinaryProjectionEndpointData l E c aX aZ aY K L n) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    d.s.hom ≫ ((sfIntrinsicDerivedEquivalence Y A).functor.map
        (((ProEtale.projectionMapOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj
              ((scalarReductionDerivedExtension l E X n).obj K))).app
            ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
              ((scalarReductionDerivedExtension l E Y n).obj L)))) =
      ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K).app L)) ≫ d.t.hom
```

## New

```lean
theorem integralOrdinaryProjection_endpointCompatibility
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((PurCompactSupport.completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((PurCompactSupport.completed l E).ring Y))
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    Nonempty (Arrow.mk ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K).app L)) ≅
      Arrow.mk ((sfIntrinsicDerivedEquivalence Y A).functor.map
        (((ProEtale.projectionMapOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj
              ((scalarReductionDerivedExtension l E X n).obj K))).app
            ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
              ((scalarReductionDerivedExtension l E Y n).obj L)))))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility | M4 | Replace the false universal assertion with a proved construction of compatible endpoints. |
| Sheaf.Paper.IntegralOrdinaryProjectionArrowComparison | unclaimed | Keep both signatures; extract endpoint isomorphisms and commutativity from the constructed arrow isomorphism. |

The downstream name search finds this sole consumer. The remaining indirect consumers
continue to use its unchanged statements. No definition used by a target changes.

## Status

landed 20261028T072430-L-1946465 2026-10-28 (merge of deliver/M4/Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility)
