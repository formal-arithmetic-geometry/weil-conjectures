# SheafOfModules.ScalarPullback.compositeInverseImage

## Reason

The full module still reached the 60-second limit after controlling the unlifted
presentation. The concrete composite presentation similarly contains three data
fields and seven large graph-law proofs. Retain its former construction as
`compositeInverseImageAux` and reconstruct the same data in a small record whose
proof fields project the existing proofs. This controls repeated reduction of the
module-functor projection in the exact-localization composition proof. No delivered
file or theorem is split, and no limit is raised.

All three data expressions are verbatim the old expressions; graph-law proof fields
are propositions. The resulting private object is definitionally equal to the old
one. No public definition, theorem signature, binder, universe or visibility changes.
The composition and identity theorem signatures are unchanged; their component
calculations use the separate private projection API recorded in
`K3-kflat-scalar-comparison-projection-api.md`. There is no change of target meaning.
A diagnostic `rfl` equality between the new and former composite presentations
compiled in 3.4 seconds.

## Old

```lean
set_option backward.isDefEq.respectTransparency false in
private noncomputable def compositeInverseImage
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {H : GrothendieckTopology E}
    {F : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {G : Sheaf K (Type u) ⥤ Sheaf H (Type u)}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    {S : Sheaf H CommRingCat.{u}}
    (I : InverseImage F A B) (I' : InverseImage G B S) : InverseImage (F ⋙ G) A S := by
  let er := G.mapIso I.ringUnderlying ≪≫ I'.ringUnderlying
  let em : (I.modules ⋙ I'.modules) ⋙ underlying S ≅ underlying A ⋙ (F ⋙ G) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft I.modules I'.moduleUnderlying ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight I.moduleUnderlying G ≪≫ Functor.associator _ _ _
  refine
    { ringUnderlying := er
      modules := I.modules ⋙ I'.modules
      moduleUnderlying := em
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t h V x
    have hr := I'.ringAdd (F.obj T) (F.map a ≫ I.ringUnderlying.hom)
      (F.map b ≫ I.ringUnderlying.hom) (F.map t ≫ I.ringUnderlying.hom)
      (I.ringAdd T a b t h) V x
    simpa [er, Functor.map_comp] using hr
  · intro T a b t h V x
    have hr := I'.ringMul (F.obj T) (F.map a ≫ I.ringUnderlying.hom)
      (F.map b ≫ I.ringUnderlying.hom) (F.map t ≫ I.ringUnderlying.hom)
      (I.ringMul T a b t h) V x
    simpa [er, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I'.ringZero (F.obj T) (F.map a ≫ I.ringUnderlying.hom)
      (I.ringZero T a h) V x
    simpa [er, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I'.ringOne (F.obj T) (F.map a ≫ I.ringUnderlying.hom)
      (I.ringOne T a h) V x
    simpa [er, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I'.moduleAdd (I.modules.obj M) (F.obj T)
      (F.map a ≫ I.moduleUnderlying.inv.app M)
      (F.map b ≫ I.moduleUnderlying.inv.app M)
      (F.map t ≫ I.moduleUnderlying.inv.app M) (I.moduleAdd M T a b t h) V x
    simpa [em, Functor.map_comp] using hr
  · intro M T a h V x
    have hr := I'.moduleZero (I.modules.obj M) (F.obj T)
      (F.map a ≫ I.moduleUnderlying.inv.app M) (I.moduleZero M T a h) V x
    simpa [em, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I'.moduleSMul (I.modules.obj M) (F.obj T)
      (F.map a ≫ I.ringUnderlying.hom)
      (F.map b ≫ I.moduleUnderlying.inv.app M)
      (F.map t ≫ I.moduleUnderlying.inv.app M) (I.moduleSMul M T a b t h) V x
    simpa [er, em, Functor.map_comp] using hr
```

## New

```lean
set_option backward.isDefEq.respectTransparency false in
private noncomputable def compositeInverseImageAux
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {H : GrothendieckTopology E}
    {F : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {G : Sheaf K (Type u) ⥤ Sheaf H (Type u)}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    {S : Sheaf H CommRingCat.{u}}
    (I : InverseImage F A B) (I' : InverseImage G B S) : InverseImage (F ⋙ G) A S := by
  let er := G.mapIso I.ringUnderlying ≪≫ I'.ringUnderlying
  let em : (I.modules ⋙ I'.modules) ⋙ underlying S ≅ underlying A ⋙ (F ⋙ G) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft I.modules I'.moduleUnderlying ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight I.moduleUnderlying G ≪≫ Functor.associator _ _ _
  refine
    { ringUnderlying := er
      modules := I.modules ⋙ I'.modules
      moduleUnderlying := em
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t h V x
    have hr := I'.ringAdd (F.obj T) (F.map a ≫ I.ringUnderlying.hom)
      (F.map b ≫ I.ringUnderlying.hom) (F.map t ≫ I.ringUnderlying.hom)
      (I.ringAdd T a b t h) V x
    simpa [er, Functor.map_comp] using hr
  · intro T a b t h V x
    have hr := I'.ringMul (F.obj T) (F.map a ≫ I.ringUnderlying.hom)
      (F.map b ≫ I.ringUnderlying.hom) (F.map t ≫ I.ringUnderlying.hom)
      (I.ringMul T a b t h) V x
    simpa [er, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I'.ringZero (F.obj T) (F.map a ≫ I.ringUnderlying.hom)
      (I.ringZero T a h) V x
    simpa [er, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I'.ringOne (F.obj T) (F.map a ≫ I.ringUnderlying.hom)
      (I.ringOne T a h) V x
    simpa [er, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I'.moduleAdd (I.modules.obj M) (F.obj T)
      (F.map a ≫ I.moduleUnderlying.inv.app M)
      (F.map b ≫ I.moduleUnderlying.inv.app M)
      (F.map t ≫ I.moduleUnderlying.inv.app M) (I.moduleAdd M T a b t h) V x
    simpa [em, Functor.map_comp] using hr
  · intro M T a h V x
    have hr := I'.moduleZero (I.modules.obj M) (F.obj T)
      (F.map a ≫ I.moduleUnderlying.inv.app M) (I.moduleZero M T a h) V x
    simpa [em, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I'.moduleSMul (I.modules.obj M) (F.obj T)
      (F.map a ≫ I.ringUnderlying.hom)
      (F.map b ≫ I.moduleUnderlying.inv.app M)
      (F.map t ≫ I.moduleUnderlying.inv.app M) (I.moduleSMul M T a b t h) V x
    simpa [er, em, Functor.map_comp] using hr

-- Separate the composite presentation's explicit data from its graph-law proofs.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def compositeInverseImage
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {H : GrothendieckTopology E}
    {F : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {G : Sheaf K (Type u) ⥤ Sheaf H (Type u)}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    {S : Sheaf H CommRingCat.{u}}
    (I : InverseImage F A B) (I' : InverseImage G B S) : InverseImage (F ⋙ G) A S := by
  let er := G.mapIso I.ringUnderlying ≪≫ I'.ringUnderlying
  let em : (I.modules ⋙ I'.modules) ⋙ underlying S ≅ underlying A ⋙ (F ⋙ G) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft I.modules I'.moduleUnderlying ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight I.moduleUnderlying G ≪≫ Functor.associator _ _ _
  exact
    { ringUnderlying := er
      modules := I.modules ⋙ I'.modules
      moduleUnderlying := em
      ringAdd := (compositeInverseImageAux I I').ringAdd
      ringMul := (compositeInverseImageAux I I').ringMul
      ringZero := (compositeInverseImageAux I I').ringZero
      ringOne := (compositeInverseImageAux I I').ringOne
      moduleAdd := (compositeInverseImageAux I I').moduleAdd
      moduleZero := (compositeInverseImageAux I I').moduleZero
      moduleSMul := (compositeInverseImageAux I I').moduleSMul }
```

## Users

`python3 tools/downstream.py Sheaf.Paper.KFlatScalarComparisonNormalization
--uses compositeInverseImage` lists these eleven downstream modules and finds
uses of the declaration only in the item module. A repository-wide search finds
no other mention. No external module needs adaptation. The ordinary composite
is still the explicitly composed module functor with the same pasted ring and
underlying-module isomorphisms.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.KFlatScalarComparisonNormalization` | K3 | Private composite presentation reconstructed with identical data; proofs compile here. |
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
