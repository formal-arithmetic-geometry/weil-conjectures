# AlgebraicGeometry.Etale.ClosedChartExceptionalAssertion

## Reason

Kernel conversion of the expanded nested conjunction repeatedly unfolds large concrete
etale derived-functor constructions. The original setup alone compiles, but adding the
purity/comparison fields produces kernel deterministic timeouts. Use the project-prescribed
structure representation for a large proposition (stages/3-proving-and-pruning.md §4).

The three fields are precisely the old three conjuncts, in the same order:
`purityAdjunction`, `comparison`, and `preservation`. No binder, functor, equation,
quantifier, hypothesis, or conclusion within these clauses changes. This is an equivalent
representation of a proposition, not a mathematical statement change.
The comparison field uses the new definition `counitNormalizedChartComparison`, which
expands to exactly its old unique-isomorphism assertion and the identical counit equation.
This generic predicate has no additional hypotheses or proof fields; it only abstracts
the five categories, functors, adjunctions and left comparison already in that equation.
Its statement is attached to the existing item node, not a new mathematical result.
The private generic theorem proves the predicate using right-adjoint uniqueness.
A diagnostic with the expanded equation took over 60 seconds; the compact predicate
version compiled in 32.4 seconds at a diagnostic heartbeat limit lower than the default. The parent
`ClosedChartExceptionalPreservation` and main theorem signatures remain verbatim.
No arbitrary data is introduced: all fields are proofs and the structure is in Prop.

## Old

```lean
def ClosedChartExceptionalAssertion
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    {X Y U V : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ Y) (v : V ⟶ Y) (r : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin r)) V)
    [IsOpenImmersion u] [IsOpenImmersion v] [IsClosedImmersion i]
    [QuasiCompact u] [QuasiCompact v] [QuasiCompact f] [QuasiCompact (u ≫ f)]
    [HasCompactification u] [HasCompactification v] [HasCompactification f]
    [HasCompactification (u ≫ f)]
    [HasCompactification (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V))]
    [HasCompactification ((i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v)]
    (h : u ≫ f = (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) : Prop :=
  Nonempty (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin r)) V ↘ V) ⊣ closedChartTwistedPullback A N hA V r) ∧
  (∀ (F : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adjF : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ F)
    (adjπ : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin r)) V ↘ V) ⊣ closedChartTwistedPullback A N hA V r),
    ∃! e : F ⋙ (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ≅
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙
          closedChartTwistedPullback A N hA V r) ⋙
          (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint,
      ∀ L : DerivedCategoryModule A Y,
        (closedChartCompactSupportComparison A u f v r i h).hom.app
            ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj (F.obj L)) ≫
          ((R(lowerStar (ModuleCat.{u + 1} A) i) ⋙
            rightDerivedLowerShriek (ModuleCat.{u + 1} A)
              (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ⋙
            (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory).map
              (e.hom.app L) ≫
          (((Adjunction.ofIsLeftAdjoint
            (R(lowerStar (ModuleCat.{u + 1} A) i))).comp adjπ).comp
            (derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) v)).counit.app L =
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) u).comp adjF).counit.app L) ∧
  ∀ L : DerivedCategoryModule A Y,
    DerivedCategory.isBoundedConstructible A Y L →
    (∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A Y a b L) →
    DerivedCategory.isBoundedConstructible A U
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj
        ((closedChartTwistedPullback A N hA V r).obj
          ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj L))) ∧
    ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A U a b
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj
        ((closedChartTwistedPullback A N hA V r).obj
          ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj L)))
```

## New

```lean
def counitNormalizedChartComparison
    {C D E B H : Type*}
    [Category* C] [Category* D] [Category* E] [Category* B] [Category* H]
    {Lu : C ⥤ D} {Ru : D ⥤ C} {F : D ⥤ E} {R : E ⥤ D}
    {Li : C ⥤ B} {Ri : B ⥤ C} {Lπ : B ⥤ H} {Rπ : H ⥤ B}
    {Lv : H ⥤ E} {Rv : E ⥤ H}
    (au : Lu ⊣ Ru) (af : F ⊣ R) (ai : Li ⊣ Ri) (aπ : Lπ ⊣ Rπ)
    (av : Lv ⊣ Rv) (e : Lu ⋙ F ≅ (Li ⋙ Lπ) ⋙ Lv) : Prop :=
    ∃! t : R ⋙ Ru ≅ (Rv ⋙ Rπ) ⋙ Ri, ∀ X,
      e.hom.app (Ru.obj (R.obj X)) ≫ ((Li ⋙ Lπ) ⋙ Lv).map (t.hom.app X) ≫
        ((ai.comp aπ).comp av).counit.app X = (au.comp af).counit.app X

structure ClosedChartExceptionalAssertion
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    {X Y U V : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ Y) (v : V ⟶ Y) (r : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin r)) V)
    [IsOpenImmersion u] [IsOpenImmersion v] [IsClosedImmersion i]
    [QuasiCompact u] [QuasiCompact v] [QuasiCompact f] [QuasiCompact (u ≫ f)]
    [HasCompactification u] [HasCompactification v] [HasCompactification f]
    [HasCompactification (u ≫ f)]
    [HasCompactification (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V))]
    [HasCompactification ((i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v)]
    (h : u ≫ f = (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) : Prop where
  purityAdjunction : Nonempty (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin r)) V ↘ V) ⊣ closedChartTwistedPullback A N hA V r)
  comparison : ∀ (F : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adjF : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ F)
    (adjπ : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin r)) V ↘ V) ⊣ closedChartTwistedPullback A N hA V r),
    counitNormalizedChartComparison
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) u)
      adjF (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))) adjπ
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v)
      (closedChartCompactSupportComparison A u f v r i h)
  preservation : ∀ L : DerivedCategoryModule A Y,
    DerivedCategory.isBoundedConstructible A Y L →
    (∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A Y a b L) →
    DerivedCategory.isBoundedConstructible A U
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj
        ((closedChartTwistedPullback A N hA V r).obj
          ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj L))) ∧
    ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A U a b
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj
        ((closedChartTwistedPullback A N hA V r).obj
          ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj L)))
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation
--uses ClosedChartExceptionalAssertion` reports zero downstream modules and one textual
user, the item itself. A search of both source roots confirms no external occurrence of
this predicate. The item retains its DAG attachment and is not withdrawn. No target
signature or the mathematics of any target changes. No forced adaptation. This definition lies below the project targets, so their
definition review is reopened under the stage-3 rule; the three mathematical clauses
are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | R4 | Its constructor proof supplies the three named fields; the mathematical clauses are identical. |

## Status

landed 20261024T015934-L-2478560 2026-10-24 (merge of deliver/R4/Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation)
