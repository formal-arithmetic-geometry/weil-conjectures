# AlgebraicGeometry.Etale.abelianRepresentableGenerator_coherence

## Reason

The assigned file has zero holes and is a retirement item in
`coord/retire-items.tsv`. Its coherence theorem is identical to the adopted
upstream theorem. The only additional public declaration is
`AlgebraicGeometry.Etale.sectionsEquiv_precomp`; upstream keeps its copy private.
Retire the duplicate module, reuse the official theorem, and preserve this public
helper in a small module importing only the existing open-cohomology comparison.
No source-library file is modified.

## Old

`Sheaf.AlgebraicGeometry.AbelianRepresentableGeneratorCoherence` declares:

```lean
theorem abelianRepresentableGenerator_coherence {X Y : Scheme.{u}}
    (h : Y ⟶ X) (W V : X.Etale) (v : V ⟶ W) :
    let g := pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp) (by simp)
    let i := upperStarComp AddCommGrpCat.{u + 1} g (pullback.fst h W.hom)
      (pullback.fst h V.hom) (by simp [g])
    abelianRepresentableGenerator h V ≫
        (upperStar AddCommGrpCat.{u + 1} (pullback.fst h V.hom)).map
          ((upperStar AddCommGrpCat.{u + 1} h).map ((abelianRepresentable X).map v)) ≫
        i.hom.app ((upperStar AddCommGrpCat.{u + 1} h).obj
          ((abelianRepresentable X).obj W)) =
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).inv.app
          (AddCommGrpCat.of (ULift ℤ)) ≫
        (upperStar AddCommGrpCat.{u + 1} g).map (abelianRepresentableGenerator h W)
```

It also declares this public helper:

```lean
lemma sectionsEquiv_precomp {X : Scheme.{u}} {A B : X.Etale}
    (a : A ⟶ B) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : (etaleOpenFreeSheaf X).obj B ⟶ F) :
    EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology A F
      ((etaleOpenFreeSheaf X).map a ≫ f) =
      F.obj.map a.op (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology B F f)
```

The item publicly imports
`WeilConjectures.AlgebraicGeometry.CyclicDerivedHomComparisonMap` and privately
imports `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence` and
`WeilConjectures.AlgebraicGeometry.ConstantSectionAdjunctPullback`.

## New

The old Sheaf module is withdrawn via `deleted.txt`. The unchanged theorem with
exactly the signature above is already proved in
`WeilConjectures.AlgebraicGeometry.AbelianRepresentableGeneratorCoherence`.
Its node now points there. Its upstream parent
`WeilConjectures.AlgebraicGeometry.AbelianRepresentableCohomologyMapNaturality`
already imports that official module. The mathematical proof route and its three
recorded dependencies are preserved.

The public helper with exactly the signature and proof above now lives in
`Sheaf.AlgebraicGeometry.EtaleRepresentableSectionsNaturality`, which publicly
imports `WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison`.
The one remaining direct consumer imports the helper module instead of the
withdrawn item. Its proof, signatures and visibility are unchanged.
The helper gets its own proved node, and the consumer's dependency on the old
combined node is narrowed to that helper node.

## Status

landed 20261020T235529-L-1185757 2026-10-20 (merge of deliver/A2/Sheaf.AlgebraicGeometry.AbelianRepresentableGeneratorCoherence)

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianRepresentableGeneratorCoherence | D2 (assigned retirement) | Withdraw duplicate module; attach coherence to official source theorem. |
| Sheaf.AlgebraicGeometry.EtaleRepresentableSectionsNaturality | D2 (new) | Preserve public helper with identical signature and proof. |
| Sheaf.AlgebraicGeometry.EtaleOpenCohomologyRestrictionCompatibility | unclaimed | Replace one private proof import; retain every declaration and proof. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen | unclaimed | Indirect importer; public mathematical API unchanged. |
| Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback | unclaimed | Indirect importer; public mathematical API unchanged. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison | B2 | Indirect importer; no edit and no signature change. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare | F4 | Indirect importer; no edit and no signature change. |

The user list is the full output of `tools/downstream.py` at preparation time.
There is one current direct importer. The second consumer listed in the older
retirement table, the Sheaf cohomology-map naturality twin, is already absent;
its official counterpart imports the official generator-coherence theorem.
No existing upstream declaration is removed or changed. No target type or
definition changes, so no target statement review is reopened.

