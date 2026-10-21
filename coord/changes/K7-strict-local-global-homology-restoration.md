# AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_globalHomology

## Reason

Restore the quarantined rework item from its preserved archive. The assigned module
has zero textual holes, but its imports no longer provide a usable library module:
compilation of the archive fails opening the retired
Sheaf.AlgebraicGeometry.StrictHenselizationRestriction.olean.server.
Several other historical Sheaf proof imports have been retired too.

The proof needs only the original-small-model neighbourhood presentation and derived
etale cohomology continuity. Its statement needs global sections, the original
strict-henselization structural map and the derived mate infrastructure. Import these
providers explicitly. Keep the complete declaration, docstring and proof verbatim.
The canonical upstream theorem uses strictLocalization rather than
strictHenselizationScheme, so it cannot replace this original-model statement by
an exact application. No source-library file is changed.

## Old

```lean
public import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction
import Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
```

The declaration signature, unchanged by this repair:

```lean
theorem isIso_strictHenselization_baseChange_globalHomology
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    IsIso
      ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K)))
```

## New

```lean
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
```

The signature, attributes and proof remain exactly as above and in the archive.
Only the import header changes. The new public imports expose the actual providers
of the statement's constants; the two proof imports remain private. This restores
the original small-colimit spectrum and structural map, without substituting the
canonical localization model. No definition or target meaning changes.

## Users

There are no live direct importers of the absent module. tools/downstream.py reports
unknown module for this quarantined item, so the census also searched lean/ and
quarantine/ directly. The complete archived direct importer list follows. Their
sources are preserved, and their applications of the theorem retain the identical
type. They have independent pending restorations and are not adapted in this packet.
No downstream module is forced to change by this import-only repair.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | quarantined; no local claim found | Same theorem application and statement. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | quarantined; no local claim found | Same derived-clause application and statement. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | quarantined; no local claim found | Same model-transport input theorem and statement. |

The existing node lem-weil-pbc-strict-local-base-change-global-homology retains its
Lean attachment, both proof dependencies and all three proof steps. Parent edges
and quarantined archives remain intact. The unit sk-prop-h2 has empty realized
lists, and no unit route changes.

## Status

landed 20261021T174245-L-3773895 2026-10-21 (merge of deliver/K7/Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology)
