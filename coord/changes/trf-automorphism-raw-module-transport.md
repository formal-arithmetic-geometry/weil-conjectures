# WeilConjectures.trfAutomorphismRawModules

## Reason

Construct raw site transport with PresheafOfModules.pushforward₀ directly,
retaining the continuous-pushforward sheaf condition. Previously the raw
transport used pushforward through an identity coefficient map, adding an
unnecessary restriction-of-scalars wrapper. Removing that wrapper keeps the
same carriers, scalar actions, restriction maps and module maps while reducing
the normalization needed for tensor comparisons. No mathematical statement or
public signature changes.

## Old

```lean
def trfAutomorphismRawModules : coefficientSequenceModules l E S ⥤
    ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (coefficientSequenceTopology (ProEt.topology S))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (trfAutomorphismRawRing l E g)) :=
  SheafOfModules.pushforward (F := trfAutomorphismSystemSite g) (𝟙 _)

```

## New

The generic constructor is public because the public raw transport definition
uses it. Its construction is the original presheaf transport plus continuity;
all its data are explicit. It is attached to the existing item node.

```lean
/-- Continuous site transport with its original coefficient action, without an
identity restriction-of-scalars wrapper.
Source: Stacks 03CZ, 09A5
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
def trfRawModuleTransport
    {C D : Type t} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{v}) :
    SheafOfModules.{v} R ⥤
      SheafOfModules.{v} ((F.sheafPushforwardContinuous RingCat J K).obj R) where
  obj M :=
    { val := (PresheafOfModules.pushforward₀ F R.obj).obj M.val
      isSheaf := ((F.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj
        ⟨M.val.presheaf, M.isSheaf⟩).property }
  map f := { val := (PresheafOfModules.pushforward₀ F R.obj).map f.val }

def trfAutomorphismRawModules : coefficientSequenceModules l E S ⥤
    ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (coefficientSequenceTopology (ProEt.topology S))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (trfAutomorphismRawRing l E g)) :=
  trfRawModuleTransport (trfAutomorphismSystemSite g)
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology S))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (coefficientSequenceCommRingSheaf l E S))

```

## Users

The downstream audit of the item module reports no downstream modules.
Only the assigned item uses this declaration; all its consumers are compiled
in the same file. No other module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.AutomorphismTensorReductionComparison | S1 | Same raw transport; omit identity scalar restriction. |

## Status

landed 20261026T070924-L-3699055 2026-10-26 (merge of deliver/S1/Sheaf.TraceFormula.AutomorphismTensorReductionComparison)
