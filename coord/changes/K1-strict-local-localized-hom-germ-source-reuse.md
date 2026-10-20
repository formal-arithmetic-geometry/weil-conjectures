# strictLocalSectionRestrictionNat and strictLocalComplexSectionRestriction

## Reason

Restore the quarantined item at its original Lean path, retaining its DAG attachment,
all five public names, and all mathematical dependencies. The archive has zero holes,
but no longer typechecks: its line 57 composes the adopted canonical-model
strictHenselizationSectionRestriction with a map of sections on the old colimit model.
Line 95 repeats the mismatch in the natural-transformation data; line 185 also mixes
the canonical source leg with the old-model complex restriction. These errors were
reproduced by compiling the archive through lcompile.py.

The adopted source module already implements and proves this entire API. Its current
source consistently uses Scheme.strictLocalization and Scheme.strictLocalizationToBase.
Re-exporting that implementation fixes the definitions by using the same underlying
objects as the adopted restriction and germ API. This is a substantive replacement of
two incompatible constructions by the existing coherent constructions, not a rebase
or an empty withdrawal. It also avoids introducing duplicate global declaration names.
No source-library file is edited, and the quarantine archive is not deleted or edited.

## Old

The archived public import and private proof import were:

```lean
public import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
import Sheaf.AlgebraicGeometry.SourceCocycleExactRestriction
```

The affected definition blocks were:

```lean
/-- The natural transformation of pointed neighbourhood section restriction.
Source: Stacks Project, Tag 03Q9, the canonical restriction construction.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ). -/
@[irreducible] noncomputable def strictLocalSectionRestrictionNat {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
        (op ((strictLocalNeighbourhoods s).obj i)) ⟶
      upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s) ⋙
        Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1} where
  app F := strictHenselizationSectionRestriction s F i
  naturality {_ _} b := strictHenselizationSectionRestriction_naturality s i b

set_option backward.isDefEq.respectTransparency false in
/-- The restriction on the complex of sections, transported to strict-local homology.
The construction applies to any complex; its definition contains no choice of a class.
Source: Stacks Project, Tag 03Q9, restriction of the complex to the strict local scheme.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ). -/
@[irreducible] noncomputable def strictLocalComplexSectionRestriction {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).obj
        ((((sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (op ((strictLocalNeighbourhoods s).obj i))).mapHomologicalComplex (.up ℤ)).obj L) ⟶
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus.obj K)) := by
  let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
  let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
    AddCommGrpCat.{v + 1}
  have := strictHenselization_globalSections_preservesFiniteColimits s
  let C := (U.mapHomologicalComplex (.up ℤ)).obj L
  let a := (NatTrans.mapHomologicalComplex (strictLocalSectionRestrictionNat s i)
    (.up ℤ)).app L
  exact (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.app _ ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
      (DerivedCategory.Q.map a ≫ G.mapDerivedCategoryFactors.inv.app C ≫
        G.mapDerivedCategory.map
          (U.mapDerivedCategoryFactors.inv.app L ≫ U.mapDerivedCategory.map r.inv)) ≫
    (G.mapDerivedCategoryHomologyFunctorIso n).inv.app (U.mapDerivedCategory.obj K.obj)
```

The archive also redeclared sourceLocalizedSectionsIso, the section-restriction
naturality theorem, a proved private source-leg helper, and sourceLocalizedSectionsIso_germ.

## New

The restored module has this public import:

```lean
public import WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm
```

All five recorded public declarations are provided by that module, under exactly their
existing qualified names. There is one implementation of each definition. In the
current adopted source, the two displayed definitions use Scheme.strictLocalization s
and Scheme.strictLocalizationToBase s throughout; their construction and comparison
proof are otherwise the same cocycle evaluation and exact-functor homology argument.
The main theorem's explicit signature is unchanged. The sourceLocalizedSectionsIso
construction itself is unchanged. No additional hypothesis or weakened conclusion is
introduced; the strict-local object is the same model as the adopted source germ leg.

Keep lean.module, lean.file, lean.declaration, lean.declarations and lean.statement on
the item's node. Its new lean.note records that the declarations are re-exported.
The node's proof now explicitly records reuse of the adopted proof; proof_deps and
stmt_deps remain unchanged. In particular no parent or unit route is bypassed.

## Users

The read-only downstream.py query with --allow-missing and --uses for both definitions
and the comparison theorem reports zero live importers and zero live downstream users.
A separate scan of quarantine/ and the DAG finds the following archived consumers.
They are listed explicitly rather than treating their absence from lean/ as withdrawal.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm | K1 | Restored at its original path; all five names exported from the adopted implementation. |
| WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm | adopted source; unchanged | Supplies the definitions and complete proofs; no source declaration, signature, attribute or import is edited. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreOrdinaryGerm | quarantined; no holder in shared claim records | Direct archived importer; uses the same naturality theorem name. Its remaining archived imports and proof hole are independent rework. |
| Sheaf.AlgebraicGeometry.StrictLocalUnderivedSectionsMate | quarantined; no holder in shared claim records | Direct archived importer. The old-model mate construction already needs migration to the adopted strict-local API; its adopted source counterpart uses the canonical model. |
| Sheaf.AlgebraicGeometry.StrictLocalComplexSectionsMate | quarantined; no holder in shared claim records | Direct archived importer. Its explicit old-model mate types already disagree with the adopted germ/target API; the adopted counterpart uses the canonical model. |
| Sheaf.AlgebraicGeometry.StrictLocalDerivedMateSectionsFactorization | quarantined; no holder in shared claim records | DAG parent and transitive archived consumer, with the same pre-existing old-model migration requirement; no node attachment or proof dependency is removed. |
| Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceDerivedRestriction | quarantined; no holder in shared claim records | DAG parent and transitive archived consumer; existing theorem names retained and no dependency withdrawn. |

No consumer source is edited or restored in this packet: all live consumers already
use the adopted source implementation. Quarantined consumers retain their current
rework assignments, archives, attachments and mathematical dependencies. Their broader
model migrations cannot be attributed solely to this item: the archived item itself
already fails against the adopted restriction and source-leg types before this change.
This delivery provides a coherent import for their restoration without redefining the
old model under the canonical names.

The definition changes affect the strict-local implementation that target proofs use,
so the normal semantic review of definitions remains applicable. Challenge.lean and
all five target statements are untouched. There is no mathematical statement change.

Validation: the restored module compiles. An independent import-only probe checks all
five exported names, the defining app equation for strictLocalSectionRestrictionNat,
and the full comparison theorem for arbitrary K, L, r, n and i. All five exported
declarations have only propext, Classical.choice and Quot.sound in #print axioms.
The published compiler cache still exposes the pre-sync old-model source signatures;
the generic interface probe is valid for that build and for the canonical model in
current source. The compatibility module always imports the actual source implementation,
so it cannot mix models internally. The delivery/global build validates the current
source dependency set.

## Status

landed 20261020T161140-L-3455410 2026-10-20 (merge of deliver/K1/Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm)
