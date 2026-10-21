# AlgebraicGeometry.Etale.strictLocalSections_unit_leray

## Reason

Complete the retirement listed in coord/retire-items.tsv. The assigned file has zero
sorry holes. Its full small-coordinate-ring-colimit proof is already present under
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalSectionsUnitLeray, with the
public theorem renamed smallModel_strictLocalSections_unit_leray. Apart from the name
and module comments, the two files have identical statements, imports and proof bodies.
The current node already attaches to that existing small-model declaration.

This packet removes only the obsolete original-path Sheaf copy. It does not replace
the small-colimit scheme by the canonical strictLocalization scheme: those are different
Lean models. The fully proved adopted-source theorem is preserved verbatim as well.
There are no live importers of the removed module, and the live parent already uses
the smallModel declaration. No target statement, definition or mathematical route changes.

## Old

The removed module publicly imports these five modules:

- Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
- Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact
- WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
- WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

Its public declaration, in namespace AlgebraicGeometry.Etale, is:

```lean
theorem strictLocalSections_unit_leray {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Y : Scheme.{v}} (t : Y ⟶ Scheme.strictHenselizationScheme s)
    (D : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (T : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (r : DerivedCategory.Q.obj D ⟶ T.obj) :
    let F := lowerStar AddCommGrpCat.{v + 1} t
    let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    let H := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}
    have := strictHenselizationScheme_globalSections_preservesFiniteColimits s
    let V := F.rightDerivedFunctorPlus.obj T
    let ℓ := DerivedCategory.Plus.ι.map
        (G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app V) ≫
      G.rightDerivedFunctorPlusCompatibility.hom.app V ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorPlusCompatibility.hom.app T) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{v + 1}
        t).hom.app T.obj
    G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj D) ≫
      G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj D)) ≫
      G.mapDerivedCategory.map
        (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D)) ≫
      G.mapDerivedCategory.map
        (F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D)) ≫
      G.mapDerivedCategory.map (F.rightDerivedFunctor.map r) ≫
      G.mapDerivedCategory.map (F.rightDerivedFunctorPlusCompatibility.inv.app T) ≫ ℓ =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} t).hom (.up ℤ)).app D) ≫
      (DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.app
        ((H.mapHomologicalComplex (.up ℤ)).obj D) ≫
      H.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D) ≫
      H.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D) ≫
      H.rightDerivedFunctor.map r
```

The removed file also contains only three proved private helpers:
sections_exact_bridge, leray_unit_fac and sections_unit_on_complex. They remain in the
existing small-model module with the same bodies.

## New

The obsolete module is withdrawn through deleted.txt; delivery represents it as an
empty module with no declarations. No alias or copy of the canonical source theorem
is added. The already existing replacement is, in namespace AlgebraicGeometry.Etale:

```lean
theorem smallModel_strictLocalSections_unit_leray {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Y : Scheme.{v}} (t : Y ⟶ Scheme.strictHenselizationScheme s)
    (D : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (T : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (r : DerivedCategory.Q.obj D ⟶ T.obj) :
    let F := lowerStar AddCommGrpCat.{v + 1} t
    let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    let H := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}
    have := strictHenselizationScheme_globalSections_preservesFiniteColimits s
    let V := F.rightDerivedFunctorPlus.obj T
    let ℓ := DerivedCategory.Plus.ι.map
        (G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app V) ≫
      G.rightDerivedFunctorPlusCompatibility.hom.app V ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorPlusCompatibility.hom.app T) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{v + 1}
        t).hom.app T.obj
    G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj D) ≫
      G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj D)) ≫
      G.mapDerivedCategory.map
        (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D)) ≫
      G.mapDerivedCategory.map
        (F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D)) ≫
      G.mapDerivedCategory.map (F.rightDerivedFunctor.map r) ≫
      G.mapDerivedCategory.map (F.rightDerivedFunctorPlusCompatibility.inv.app T) ≫ ℓ =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} t).hom (.up ℤ)).app D) ≫
      (DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.app
        ((H.mapHomologicalComplex (.up ℤ)).obj D) ≫
      H.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D) ≫
      H.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D) ≫
      H.rightDerivedFunctor.map r
```

The DAG attachment remains on this exact smallModel declaration. Its note records the
retirement. The replacement retains all hypotheses and the displayed unit/Leray identity
for arbitrary D and r, without an acyclicity or invertibility hypothesis.

## Users

The source census from tools/downstream.py reports zero downstream modules, and the
whole-live-library name search finds no consumer of the removed declaration. The
following table also records the existing replacement and the relevant parent.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalSectionsUnitLeray | unclaimed in snapshot; U2 assignment | Withdraw the obsolete zero-hole copy. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalSectionsUnitLeray | unclaimed | Keep its complete proof and identical mathematical statement. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeLeray | unclaimed | Already imports the replacement privately and calls smallModel_strictLocalSections_unit_leray. |

The archived quarantine/Sheaf/AlgebraicGeometry/StrictLocalDerivedExchangeLeray.lean
still names the old path. It has no current coord/rework.tsv entry. Its node
lem-weil-pbc-strict-local-derived-exchange-leray is already attached to the live proved
small-model parent above. Neither archive nor DAG node is deleted. The parent's
proof_deps and proof-step uses still retain the sections-unit node, whose exact
small-model realization is kept. Thus this retirement does not infer mathematical
unreachability from zero live importers. dag/units/sk-prop-h2.json is unchanged.

Validation compiles both existing realizations and the live parent through lcompile.py.
A scratch Lean probe proves equality of the two fully quantified theorem constants by
rfl, checking that the types are definitionally identical. The probe also prints their
axioms. All four compilations passed: original copy 16.5 s, existing replacement 0.1 s,
type-equality/axiom probe 2.7 s, live parent 12.6 s. Both axiom lists are exactly
propext, Classical.choice and Quot.sound. Scratch validation files are not delivered.

## Status

landed 20261021T024200-L-3041939 2026-10-21 (merge of deliver/U2/Sheaf.AlgebraicGeometry.StrictLocalSectionsUnitLeray)
