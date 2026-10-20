# AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedDerivedSections_shiftTransport

## Reason

The listed retirement item is a duplicate of the adopted source-library module.
The public theorem signatures are textually identical. The retirement inventory marks
it DIFFERENT only because the Sheaf file has a private `restrictedCommShiftLowerStar`
instance absent from the source twin. The source proof instead proves
`canonical_adjunction_unit_commShift`: it checks the canonical unit on complexes and
passes the identity through the homotopy quotient and derived localization. Its
`pullback_commShift` uses `canonical_unit_commShift` for the direct-image right-derived
unit. Thus the private instance is unnecessary for the retained proof.

Withdraw only the Sheaf module and attach the existing DAG node to the source theorem.
No source-library file, public import, declaration, definition, or target is changed.

## Old

Module: `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport`.

```lean
theorem restrictedDerivedSections_shiftTransport {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (f : D+(upperStar AddCommGrpCat.{v + 1} a).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ⟶
        (DerivedCategory.Plus.singleFunctor _ 0).obj F') (U : S.Etale) :
    let T' := sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
    let τ := Functor.whiskerLeft
      (DerivedCategory.Plus.ι ⋙
        D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)))
      (derivedSectionPullback (rawAffineRestrictedMap a h h' w U)) ≫
      Functor.whiskerRight
        (Functor.whiskerLeft DerivedCategory.Plus.ι
          (derivedRestrictionIso a h h' w U).hom)
        (rightDerivedGlobalSections AddCommGrpCat.{v + 1} (Limits.pullback U.hom h'))
    let e := Evaluation.singleIso
      (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h))
      (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{v + 1}) F
    let e' := Evaluation.singleIso
      (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h'))
      (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1}) F'
    (restrictedSectionPullback a h h' w U).app (K⟦(p : ℤ)⟧) ≫
      (T' ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        ((D+(upperStar AddCommGrpCat.{v + 1} a).commShiftIso (p : ℤ)).hom.app K ≫
          (shiftFunctor _ (p : ℤ)).map f) ≫ (shiftIso h' p F' U).hom =
      (shiftIso h p F U).hom ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} (p : ℤ)).map
          (e.inv ≫ τ.app K ≫ T'.map f ≫ e'.hom)
```

## New

Module: `WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport`.
The following existing theorem replaces the withdrawn duplicate verbatim.

```lean
theorem restrictedDerivedSections_shiftTransport {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (f : D+(upperStar AddCommGrpCat.{v + 1} a).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ⟶
        (DerivedCategory.Plus.singleFunctor _ 0).obj F') (U : S.Etale) :
    let T' := sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
    let τ := Functor.whiskerLeft
      (DerivedCategory.Plus.ι ⋙
        D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)))
      (derivedSectionPullback (rawAffineRestrictedMap a h h' w U)) ≫
      Functor.whiskerRight
        (Functor.whiskerLeft DerivedCategory.Plus.ι
          (derivedRestrictionIso a h h' w U).hom)
        (rightDerivedGlobalSections AddCommGrpCat.{v + 1} (Limits.pullback U.hom h'))
    let e := Evaluation.singleIso
      (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h))
      (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{v + 1}) F
    let e' := Evaluation.singleIso
      (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h'))
      (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1}) F'
    (restrictedSectionPullback a h h' w U).app (K⟦(p : ℤ)⟧) ≫
      (T' ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        ((D+(upperStar AddCommGrpCat.{v + 1} a).commShiftIso (p : ℤ)).hom.app K ≫
          (shiftFunctor _ (p : ℤ)).map f) ≫ (shiftIso h' p F' U).hom =
      (shiftIso h p F U).hom ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} (p : ℤ)).map
          (e.inv ≫ τ.app K ≫ T'.map f ≫ e'.hom)
```

The node `lem-sbc-restricted-derived-sections-shift-transport` retains its declaration
name, full statement, statement dependencies, proof dependencies, and unit. Its Lean
module/file attachment is migrated and the proof description follows the source's
canonical-adjunction-unit argument. The discarded helper is private, has no references
outside the retired module, and appears in no public signature or definition.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport | P5 | Duplicate withdrawn. |
| WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionShiftComparison | unclaimed | Already imports the source twin; theorem application unchanged. |
| WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionPullbackCommShift | unclaimed | Already imports the source twin with import all; uses its proved private helpers. |
| WeilConjectures.AlgebraicGeometry.RawFixedDerivedComparisonNaturality | unclaimed | Already imports the source twin with import all; uses its proved private homology transport. |

`tools/downstream.py` finds zero current modules downstream of the retired Sheaf file;
its name-use search finds only the declaration in that file. A direct import search in
both library roots and quarantined Sheaf sources likewise finds no remaining importer
or external use of the private instance. The three source consumers above are listed
because they were the old consumer family in the retirement inventory. None is edited.

The two DAG parents are `lem-sbc-restricted-derived-section-shift-comparison` and
`lem-sc-raw-fixed-derived-comparison-naturality`. Both already point to source-library
modules. Their edges to this node remain correct after its attachment is migrated;
they still obtain the same theorem/private transport argument from the source twin.
The unit `sk-lem-failure-field` is unchanged. No target review is reopened: the retained
statement and every definition it mentions are identical. An `example` with the original
statement compiles by exact application of the retained theorem, and its axiom check
reports only the three permitted axioms. The unchanged source module and two direct
consumers compile individually. The optional unchanged `RawFixedDerivedComparisonNaturality`
source check times out at 60 seconds, also on retry; it is not an importer of the retired
Sheaf module and receives no source or dependency change from this packet.

## Status

landed 20261020T211812-L-3503756 2026-10-20 (merge of deliver/P5/Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport)
