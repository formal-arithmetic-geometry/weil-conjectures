# SheafOfModules.PrincipalReduction.Setup.extension

## Reason

The stage-3 static checker classifies added commands as a visibility change. This
record documents the proof elaboration commands added while completing all five
original holes. No public declaration signature or public definition body changes.
Local irreducibility keeps the chosen derived-extension model and tensor comparison
from being expanded during unrelated type conversions. Other local attributes apply
only to private helpers. Proof imports stay non-public.

## Old

The module had no local reducibility attributes. Its options were:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
```

The unchanged public definitions affected by local attributes are:

```lean
noncomputable def extension :=
  (nonempty_derivedChangeOfRingsCochainModel.{u, v, r, wO, wS} D.φ).some

noncomputable def tensorSingleIso (K : CochainComplex (ModuleCat.{r} R) ℤ) :
    (((ModuleCat.mixedTensor D.quotientMap).flip.map₂CochainComplex).obj K).obj
      D.quotientSingle ≅
      ((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).obj K :=
  CochainComplex.mapBifunctorSingle₂Iso (ModuleCat.mixedTensor D.quotientMap).flip
      (𝟙_ (ModuleCat.{r} D.A)) K ≪≫
    (NatIso.mapHomologicalComplex
      (isoWhiskerLeft (ModuleCat.extendScalars D.quotientMap)
        (leftUnitorNatIso (ModuleCat.{r} D.A)) ≪≫ Functor.rightUnitor _) (.up ℤ)).app K
```

## New

The two definition bodies above remain verbatim. Their attributes are local:

```lean
attribute [local irreducible] extension
attribute [local irreducible] tensorSingleIso
```

Private helper attributes are likewise local:

```lean
attribute [local irreducible] restrictedSheafification
attribute [local irreducible] tensorUnitIso tensorQuotientPresheafIso tensorQuotientIso
```

The module uses the following elaboration options, switching transparency between
ordinary scalar calculations and categorical calculations, and local overrides for
individual proofs:

```lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 128
```

No new global notation, variable, open declaration, public instance or persistent
reducibility attribute is introduced. Existing variable and open commands remain.

## Users

`tools/downstream.py Sheaf.Paper.DerivedReductionResolutionIndependence --uses
extension tensorSingleIso` reports zero downstream modules; its only textual user
is the item itself. Local attributes do not alter imported elaboration behavior.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedReductionResolutionIndependence | Q2 | Proof elaboration only; all five holes closed. |

No consumer adaptation is required.

## Status

landed 20261020T132023-L-1402659 2026-10-20 (merge of deliver/Q2/Sheaf.Paper.DerivedReductionResolutionIndependence)
