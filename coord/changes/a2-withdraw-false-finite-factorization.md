# CategoryTheory.derived_factor_through_small_subcoproduct (retained interface)

## Reason

STATEMENT-DISPUTED: the old finite-support theorem is false. In D(k), let U be a countable coproduct of k[0] and alpha = aleph1. U is alpha-presentable in the category of graded vector spaces, but its identity does not factor through any finite subcoproduct. The finite-subset diagram is filtered, but not alpha-filtered: the countable collection of singleton subsets has no finite upper bound. The theorem is not used by the repaired Properties route. The returned delivery's
empty replacement module was reverted so holder C1's existing public interface stays
available; no weaker replacement theorem is claimed.

Sources: Krause (2001), conditions (G3)--(G4), Lemmas 4--5, pages 121--125;
Localization theory 6.2--6.3 and 6.10.2; Neeman Theorem 0.2.

## Old

```lean
theorem derived_factor_through_small_subcoproduct
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (α : Cardinal.{v}) [Fact α.IsRegular]
    (I : Type v) (Y : I → DerivedCategory A)
    (U : DerivedCategory A) (hU : IsCardinalPresentable U α)
    (f : U ⟶ ∐ Y) :
    ∃ (J : Type v) (_ : Finite J) (a : J → I), HasCardinalLT J α ∧
      ∃ g : U ⟶ ∐ fun j ↦ Y (a j),
        g ≫ Sigma.desc (fun j ↦ Sigma.ι Y (a j)) = f
```

## New

```lean
The declaration is retained verbatim for holder C1's interface. It remains unused by
this route and no weakened replacement theorem is claimed.
```

## Users

Checked using tools/downstream.py Sheaf.CategoryTheory.DerivedPerfectSmallClassFactorization --uses derived_factor_through_small_subcoproduct.
All direct uses and transitive importers are listed. Holders checked on this machine.
The adapted Core and Properties modules were unclaimed; Factorization is held by C1 for interface preservation.
Only the current item was held by A2.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingCohomologicalRepresentability | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| Sheaf.CategoryTheory.DerivedLocalizingPerfectFamily | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| Sheaf.CategoryTheory.DerivedPerfectSmallClass | unclaimed | Compiled unchanged against the revised interfaces; every binder and the conclusion of derived_exists_perfectSmallClass stay verbatim. |
| Sheaf.CategoryTheory.DerivedPerfectSmallClassFactorization | C1 | Restored verbatim as a forced interface adaptation; its theorem remains an existing sorry and is unused by the repaired route. |
| Sheaf.CategoryTheory.DerivedPerfectSmallClassProperties | unclaimed | Adapted in this delivery: use G4 lifting and alpha-small support; remove both finite-support proof imports. |
| Sheaf.CategoryTheory.SetGeneratedDerivedSolutionSet | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| TargetsCheck | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | B4 | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Transitive importer only. Its assertions use the unchanged final perfect-class theorem, so their meanings are unchanged; no adaptation. |

The original final perfect-class consumer was compiled as a single file against
the changed overlay. Its statement and proof are unchanged; the old public
presentability import is not used by any further consumer. No target semantics
change, so this interface repair does not reopen target definition reviews.

## Forced adaptations

`Sheaf.CategoryTheory.DerivedPerfectSmallClassFactorization` (holder C1) is restored
verbatim because the returned head had an empty module and downstream interface checks
reported `unknown constant CategoryTheory.derived_factor_through_small_subcoproduct`.
No signature or visibility changed.

## Status

landed 20261017T210422-L-1009146 2026-10-17 (merge of deliver/A2/Sheaf.CategoryTheory.DerivedPerfectSmallClassCoreAlpha)
