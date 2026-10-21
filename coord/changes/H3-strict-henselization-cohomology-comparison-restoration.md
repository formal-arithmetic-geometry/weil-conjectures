# AlgebraicGeometry.Etale.isIso_strictHenselizationCohomologyComparison

## Reason

Restore the assigned original-model theorem into the current empty module. The return
at delivery head 27625c9ae6f says to take the file created by a02e6c2dfe9 as the base.
That current file contains only `module` and the retirement docstring shown below;
it has zero textual holes. The retained repair is reapplied as a substantive restoration
of its original-model theorem, not as a no-op on the current stub. There is no current
coord/rework.tsv entry for this module, and no archive is deleted. Its public
import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction is now an empty,
withdrawn module. Its old specialized small-model comparison no longer exists.
The adopted source uses strictLocalization instead of strictHenselizationScheme,
so substituting that provider would change the map and the model in the statement.

Use the existing general exact-global-sections Leray construction and the existing
small-model exactness instance. Display the canonical four-factor comparison in the
theorem signature itself. Do not recreate any of the retired restriction definitions.
The scheme, structural map, derived mate, degree, all binders, and all four morphisms
are preserved. A compiler probe reconstructs the archived comparison and its Leray
composite and proves its equality with the general Leray specialization by rfl. A separate
composition check verifies the parent application after an arbitrary invertible r.

## Old

Current live file, read again for this repair:

```lean
module

/-! Withdrawn: no declarations remain; use the official WeilConjectures twin. -/
```

The retained pre-retirement interface, which the restoration preserves mathematically:

```lean
public import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction
import Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology

theorem isIso_strictHenselizationCohomologyComparison
    {X S : Scheme.{w}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω]
    (xbar : Spec (.of Ω) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) (q : ℕ) :
    IsIso (strictHenselizationCohomologyComparison xbar f F q)
```

The old comparison definition is recorded verbatim in the landed change record
coord/changes/M2-strict-henselization-restriction-generic-cone.md. Its Leray factor
was the same composite as exactGlobalSectionsLerayHomologyIso specialized below.

## New

```lean
public import Sheaf.AlgebraicGeometry.ExactGlobalSectionsLeray
public import Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology

theorem isIso_strictHenselizationCohomologyComparison
    {X S : Scheme.{w}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω]
    (xbar : Spec (.of Ω) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) (q : ℕ) :
    IsIso
      ((Sheaf.Γ (Scheme.strictHenselizationScheme xbar).smallEtaleTopology
          AddCommGrpCat.{w + 1}).map
          ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
            (upperStar AddCommGrpCat.{w + 1} (Scheme.strictHenselizationStructuralMap xbar))
            (q : ℤ)).hom.app _) ≫
        (Sheaf.Γ (Scheme.strictHenselizationScheme xbar).smallEtaleTopology
          AddCommGrpCat.{w + 1}).map
          ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
            ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{w + 1} f).derivedPlus
              (upperStarLowerStarAdjunction AddCommGrpCat.{w + 1}
                (pullback.snd f (Scheme.strictHenselizationStructuralMap xbar))).derivedPlus
              (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{w + 1}
                (IsPullback.of_hasPullback f
                  (Scheme.strictHenselizationStructuralMap xbar)).toCommSq).hom))
                |>.natTrans.app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≫
        (exactGlobalSectionsLerayHomologyIso
          (strictHenselizationScheme_globalSections_preservesFiniteColimits xbar)
          (pullback.snd f (Scheme.strictHenselizationStructuralMap xbar)) (q : ℤ) _).hom ≫
        (cohomology AddCommGrpCat.{w + 1}
          (pullback f (Scheme.strictHenselizationStructuralMap xbar)) (q : ℤ)).map
          (DerivedCategory.Plus.ι.map
            ((Functor.mapDerivedCategoryPlusSingleFunctor
              (upperStar AddCommGrpCat.{w + 1}
                (pullback.fst f (Scheme.strictHenselizationStructuralMap xbar))) 0).hom.app
                  F)))
```

This is a definitional expansion, not a weakening or a replacement comparison.
The archived private helpers and four-factor proof remain, with only the obsolete
initial delta command removed. The explicit imports supply exactly the statement
constants. The strict-local base-change theorem remains a private proof import.
No adopted-source file or target statement is edited. The node retains its attachment
and mathematical statement; its Lean signature and proof dependencies now record
the actual expression and providers.

## Users

The current item is an empty retired module, as is its former direct parent
Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk. Running downstream.py
with the full theorem name finds zero live importers and zero live uses. The source
census agrees. The current parent DAG node still cites this item's node in proof_deps
and its proof's uses; those edges and both Lean attachments remain untouched.
The adopted-source twin uses strictLocalization, whereas this theorem concerns
strictHenselizationScheme. It is not a substitute for the original-model statement.
No adopted-source declaration is edited or removed.

The previous attempt checked the original parent's IsIso.comp_isIso' application
against this expanded comparison. That historical check does not assert that the
now-retired parent exports a declaration. No live consumer requires adaptation and
no new live target-closure progress is claimed by this restoration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | H3 | Restore the original-model theorem and its complete four-factor proof in the current empty module. |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | retired; unclaimed | No live declaration or import; its DAG citation remains. No edit or withdrawal. |

The unit sk-thm-br has empty realized statement and step lists. No unit route,
parent edge, Lean attachment, or quarantined archive is removed. No target meaning
changes: the explicit comparison is definitionally the archived one, on the same
small-colimit spectrum.

## Status

landed 20261021T214757-L-1852581 2026-10-21 (merge of deliver/H3/Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso)
