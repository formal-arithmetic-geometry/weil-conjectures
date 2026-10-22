# SheafOfModules.ScalarPullback.unliftInverseImage

## Reason

The complete module reached the 60-second compile limit. The private adapter packages
three data fields and seven generalized graph-law proofs. Elaborating its data
projections repeatedly unfolds and copies the large construction containing those
proofs. Keep the original construction as `unliftInverseImageAux`, and reconstruct
`unliftInverseImage` with the same explicit data and the auxiliary construction's
already proved graph laws. Its data projections now reduce through a small record.
No time limit is raised and the delivered module is not split.

The module functor, ring identification and underlying-module identification are
verbatim the old data expressions. Every graph-law field is a proof in `Prop`;
proof irrelevance identifies it with the former proof. Thus the private
presentation is definitionally the same object, with exactly the same operations.
No theorem signature or public definition changes, and target meanings are unchanged.
A diagnostic copy of the new wrapper, using the old adapter for its proof fields,
compiled together with a `by rfl` proof of equality to the old adapter (2.8 seconds
through `lcompile.py`). This checks the stated definitional equality directly.

## Old

```lean
set_option backward.isDefEq.respectTransparency false in
private noncomputable def unliftInverseImage
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (I : InverseImage L A B) : AlgebraicInverseImage L A B := by
  let eR := SheafOfModules.sheafUliftIso J CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eS := SheafOfModules.sheafUliftIso K CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eM := Functor.isoWhiskerLeft (toSheaf ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) <|
    SheafOfModules.sheafUliftIso J AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  let eN := Functor.isoWhiskerLeft (toSheaf ((sheafCompose K
    (forget₂ CommRingCat.{u} RingCat.{u})).obj B)) <|
    SheafOfModules.sheafUliftIso K AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  let er := L.mapIso (eR.app A).symm ≪≫ I.ringUnderlying ≪≫ eS.app B
  let em := Functor.isoWhiskerLeft I.modules eN.symm ≪≫ I.moduleUnderlying ≪≫
    Functor.isoWhiskerRight eM L
  refine
    { ringUnderlying := er
      modules := I.modules
      moduleUnderlying := em
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t h V x
    have hr := I.ringAdd T (a ≫ (eR.app A).inv) (b ≫ (eR.app A).inv)
      (t ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a b t h V x
    have hr := I.ringMul T (a ≫ (eR.app A).inv) (b ≫ (eR.app A).inv)
      (t ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringZero T (a ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringOne T (a ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleAdd M T (a ≫ (eM.app M).inv) (b ≫ (eM.app M).inv)
      (t ≫ (eM.app M).inv) h V x
    simpa [em, eM, eN, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a h V x
    have hr := I.moduleZero M T (a ≫ (eM.app M).inv) h V x
    simpa [em, eM, eN, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleSMul M T (a ≫ (eR.app A).inv) (b ≫ (eM.app M).inv)
      (t ≫ (eM.app M).inv) h V x
    simpa [er, em, eR, eS, eM, eN, SheafOfModules.sheafUliftIso, uliftTrivial,
      Functor.map_comp] using hr
```

## New

```lean
set_option backward.isDefEq.respectTransparency false in
private noncomputable def unliftInverseImageAux
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (I : InverseImage L A B) : AlgebraicInverseImage L A B := by
  let eR := SheafOfModules.sheafUliftIso J CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eS := SheafOfModules.sheafUliftIso K CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eM := Functor.isoWhiskerLeft (toSheaf ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) <|
    SheafOfModules.sheafUliftIso J AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  let eN := Functor.isoWhiskerLeft (toSheaf ((sheafCompose K
    (forget₂ CommRingCat.{u} RingCat.{u})).obj B)) <|
    SheafOfModules.sheafUliftIso K AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  let er := L.mapIso (eR.app A).symm ≪≫ I.ringUnderlying ≪≫ eS.app B
  let em := Functor.isoWhiskerLeft I.modules eN.symm ≪≫ I.moduleUnderlying ≪≫
    Functor.isoWhiskerRight eM L
  refine
    { ringUnderlying := er
      modules := I.modules
      moduleUnderlying := em
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t h V x
    have hr := I.ringAdd T (a ≫ (eR.app A).inv) (b ≫ (eR.app A).inv)
      (t ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a b t h V x
    have hr := I.ringMul T (a ≫ (eR.app A).inv) (b ≫ (eR.app A).inv)
      (t ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringZero T (a ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringOne T (a ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleAdd M T (a ≫ (eM.app M).inv) (b ≫ (eM.app M).inv)
      (t ≫ (eM.app M).inv) h V x
    simpa [em, eM, eN, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a h V x
    have hr := I.moduleZero M T (a ≫ (eM.app M).inv) h V x
    simpa [em, eM, eN, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleSMul M T (a ≫ (eR.app A).inv) (b ≫ (eM.app M).inv)
      (t ≫ (eM.app M).inv) h V x
    simpa [er, em, eR, eS, eM, eN, SheafOfModules.sheafUliftIso, uliftTrivial,
      Functor.map_comp] using hr

-- Keep the presentation's data projections small. The graph-law proofs live in the
-- auxiliary construction, so using a module or ring projection does not copy those proofs.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def unliftInverseImage
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (I : InverseImage L A B) : AlgebraicInverseImage L A B := by
  let eR := SheafOfModules.sheafUliftIso J CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eS := SheafOfModules.sheafUliftIso K CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eM := Functor.isoWhiskerLeft (toSheaf ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) <|
    SheafOfModules.sheafUliftIso J AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  let eN := Functor.isoWhiskerLeft (toSheaf ((sheafCompose K
    (forget₂ CommRingCat.{u} RingCat.{u})).obj B)) <|
    SheafOfModules.sheafUliftIso K AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  let er := L.mapIso (eR.app A).symm ≪≫ I.ringUnderlying ≪≫ eS.app B
  let em := Functor.isoWhiskerLeft I.modules eN.symm ≪≫ I.moduleUnderlying ≪≫
    Functor.isoWhiskerRight eM L
  exact
    { ringUnderlying := er
      modules := I.modules
      moduleUnderlying := em
      ringAdd := (unliftInverseImageAux I).ringAdd
      ringMul := (unliftInverseImageAux I).ringMul
      ringZero := (unliftInverseImageAux I).ringZero
      ringOne := (unliftInverseImageAux I).ringOne
      moduleAdd := (unliftInverseImageAux I).moduleAdd
      moduleZero := (unliftInverseImageAux I).moduleZero
      moduleSMul := (unliftInverseImageAux I).moduleSMul }
```

## Users

`python3 tools/downstream.py Sheaf.Paper.KFlatScalarComparisonNormalization
--uses unliftInverseImage` lists the eleven downstream modules below and finds
uses of this private declaration only inside the item module. A repository-wide
search also finds no other module mentioning it or importing this module with
`import all`. Only the item module changes. The public action comparison is still
specified uniquely by the same underlying formula; its proof's private presentation
does not change that specification.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.KFlatScalarComparisonNormalization` | K3 | Private adapter reconstructed with identical data; proofs compile in this packet. |
| `Sheaf.Paper.ClosedSupportedScalarComparison` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.ConstructibleAlgClTopologyComparison` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.ContinuousAlgClOpenScalarComparison` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.ProperIntegralRationalScalarComparison` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.PulledReductionNormalizationComparison` | E9 | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.QcqsProperConstructibleClosedBaseChange` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.QuotientExpressionKFlatNormalization` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.SupportedFiniteStageTopologyDefect` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.TameBoundaryScalarComparison` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.WholeTowerIntegralPullbackComparison` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.SixFunctors.OpenScalarConjugateNormalization` | unclaimed | No use of the private declaration; no adaptation or public interface change. |

## Status

landed 20261022T020104-L-15317 2026-10-22 (merge of deliver/K3/Sheaf.Paper.KFlatScalarComparisonNormalization)
