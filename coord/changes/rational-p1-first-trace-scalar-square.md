# AlgebraicGeometry.ProEtale.RationalP1.rationalP1_first_trace_transport_counit_expanded_for_diagram

## Reason

The old arbitrary-Diagram statement is false. Diagram.traceq is an unconstrained
arrow: the only integration equations concern trace₁ and trace₂. Replacing traceq
by zero preserves all its fields, both integration equations and all old theorem
hypotheses. It makes the old left-hand side zero. For a canonical normalized
first trace over a geometric point and M the coefficient unit, the terminal
functional on the right is nonzero on the Chern summand. Thus the needed scalar
base-change square cannot be obtained from an arbitrary Diagram.

Add precisely that scalar square as ht. The canonical caller already has Family
and Reference; first_scalar_trace supplies it without changing any hypothesis
or conclusion of that caller. This is a correction of a non-target statement,
not a proof of the old false claim. No definition used by a target is changed.

## Old

```lean
theorem rationalP1_first_trace_transport_counit_expanded_for_diagram
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (d : Diagram (coefficient l c).X Y (line l c))
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (hq : IsIso (projectionMap (coefficient l c).X (ProjectiveLine Y ↘ Y)
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
          (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)))
    (hb : IsIso ((condensedAmbientExchange (coefficient l c).X (square Y)).app M))
    (hp : IsIso (twistProjectionMap (coefficient l c).X (secondProjection Y)
      (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
      (secondLineComparison l c k p hpl Y)
      ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)))
    (h₁ : IsIso (projectionMap (coefficient l c).X (firstProjection Y) M
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧))) :
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
      (X := (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
              (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
      ((moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).map
        (X := ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
              (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
          (tensorShiftIso (coefficient l c).X (diagonalSurface Y)
            (line l c (diagonalSurface Y))
            ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)).hom ≫
        @inv _ _ _ _ (twistProjectionMap (coefficient l c).X (secondProjection Y)
          (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
          (secondLineComparison l c k p hpl Y)
          ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)) hp ≫
        (twist (coefficient l c).X (ProjectiveLine Y)
          (line l c (ProjectiveLine Y))).map
          (by
            unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
            exact @inv _ _ _ _
              ((condensedAmbientExchange (coefficient l c).X (square Y)).app M) hb)) ≫
      counitProjectionPart (coefficient l c).X Y (line l c (ProjectiveLine Y))
        ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M) hq ≫
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M ◁
        (trace (coefficient l c).X Y (line l c) d ≫
          (singleUnitIso (coefficient l c).X Y).hom)) ≫
      (ρ_ ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)).hom =
    firstTerminalFunctional (coefficient l c).X Y (line l c) d M
      (((DerivedCategory.singleFunctor
          (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
            (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
      d.trace₁ h₁
```

## New

```lean
theorem rationalP1_first_trace_transport_counit_expanded_for_diagram
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (d : Diagram (coefficient l c).X Y (line l c))
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (hq : IsIso (projectionMap (coefficient l c).X (ProjectiveLine Y ↘ Y)
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
          (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)))
    (hb : IsIso ((condensedAmbientExchange (coefficient l c).X (square Y)).app M))
    (hp : IsIso (twistProjectionMap (coefficient l c).X (secondProjection Y)
      (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
      (secondLineComparison l c k p hpl Y)
      ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)))
    (h₁ : IsIso (projectionMap (coefficient l c).X (firstProjection Y) M
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
    (ht : firstTraceExchange (coefficient l c).X Y
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
          0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
        (secondLineComparison l c k p hpl Y) ≫
      firstNativeFunctional (coefficient l c).X Y (line l c) d
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) d.trace₁ ≫
      (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom =
      (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (trace (coefficient l c).X Y (line l c) d ≫
          (singleUnitIso (coefficient l c).X Y).hom) ≫
        (secondTraceUnitIso (coefficient l c).X Y).hom) :
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
      (X := (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
              (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
      ((moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).map
        (X := ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
              (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
          (tensorShiftIso (coefficient l c).X (diagonalSurface Y)
            (line l c (diagonalSurface Y))
            ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)).hom ≫
        @inv _ _ _ _ (twistProjectionMap (coefficient l c).X (secondProjection Y)
          (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
          (secondLineComparison l c k p hpl Y)
          ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)) hp ≫
        (twist (coefficient l c).X (ProjectiveLine Y)
          (line l c (ProjectiveLine Y))).map
          (by
            unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
            exact @inv _ _ _ _
              ((condensedAmbientExchange (coefficient l c).X (square Y)).app M) hb)) ≫
      counitProjectionPart (coefficient l c).X Y (line l c (ProjectiveLine Y))
        ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M) hq ≫
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M ◁
        (trace (coefficient l c).X Y (line l c) d ≫
          (singleUnitIso (coefficient l c).X Y).hom)) ≫
      (ρ_ ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)).hom =
    firstTerminalFunctional (coefficient l c).X Y (line l c) d M
      (((DerivedCategory.singleFunctor
          (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
            (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
      d.trace₁ h₁
```

## Users

The downstream --uses check lists exactly the two modules below. There are 704
transitive importers, but no other source mentions the changed declaration.
The only direct importer is the canonical caller. Its signature and visibility
stay verbatim; only its proof import and final argument change. The current
snapshot has no claim for the caller (unclaimed).

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalP1FirstTraceTransportCounitExpandedForDiagram | A3 | Adds the necessary scalar trace-square hypothesis; proves the corrected conclusion from the trace-free comparison and normalized projection scalar evaluation. |
| Sheaf.Paper.RationalP1FirstTraceTransportCounitExpanded | unclaimed | Supplies ht using first_scalar_trace and its existing Family and Reference; signature unchanged. |

The copied parent DAG node changes only its proof route. New nodes record the
opposite mate construction, the trace-free comparison, the scalar square, and
normalized projection scalar evaluation.
No adopted-source declaration or adopted-source public import is modified.

Validation: the original canonical caller fails at line 141 against the repaired
signature because the supplied term still expects the scalar-square argument.
Its adaptation supplies first_scalar_trace and compiles in 13.6 seconds. The
repaired item compiles in 20.3 seconds (kernel checking 2.3 seconds). The three
split statements compile independently; no adopted-source module is changed.

## Status

landed 20261028T072334-L-1934575 2026-10-28 (merge of deliver/A3/Sheaf.Paper.RationalP1FirstTraceTransportCounitExpandedForDiagram)
