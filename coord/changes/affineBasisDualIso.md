# AlgebraicGeometry.affineBasisDualIso

## Reason

The original nested `mapIso` construction expands localization colimits and
finite biproduct comparisons during projection and definitional comparison.
Saved attempts reached the kernel timeout or the 60-second file limit.
Use shared named coordinate isomorphisms, and construct dual transport with
explicit forward and inverse maps. The inverse identities are proved from
the original composite, using associativity. The concrete projection formula
is proved through the generic transport formula, and the final naturality
assembly uses proved categorical equalities without rewriting concrete maps.

`affineBasisSheafIso` is an abbreviation of the shared coordinate isomorphism,
so there is one construction of this notion. The dual coordinate construction
chooses its decidable equality internally, independently of the coordinate
projection instances. Its signature uses the underlying sheaf category to
avoid expansion through the definitionally equal scheme-module category.
`affineBasisDualIso` is irreducible; its proved forward-map equation supplies
the unfolding needed by the proof. No mathematical hypothesis or conclusion
changes, and all existing elaborated signatures and visibility are retained.
No data are chosen from an unproved theorem. Targets using these definitions
require the usual meaning review of this data refactor under AGENTS.md §4.

## Old

```lean
noncomputable def affineBasisDualIso {Y : Scheme.{u}} (U : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, U.1)) {I : Type u} [Fintype I]
    (b : Basis I Γ(Y, U.1) M) :
    SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
      ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj M)
      (SheafOfModules.unit U.1.toScheme.ringCatSheaf) ≅
    (tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj
      (ModuleCat.of Γ(Y, U.1) (M ⟶ ModuleCat.of Γ(Y, U.1) Γ(Y, U.1))) := by
  classical
  exact
    ((SheafOfModules.homFunctor U.1.toScheme.toRingedSpace.sheaf).flip.obj
      (SheafOfModules.unit U.1.toScheme.ringCatSheaf)).mapIso
        (affineBasisSheafIso U M b).symm.op ≪≫
      SheafOfModules.homObjFreeUnitIso I ≪≫
      ((Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso
        ((tilde.functor Γ(Y, U.1)).mapIso
          ((ModuleCat.homLinearEquiv.trans b.dualBasis.repr).toModuleIso) ≪≫
            tildeFinsupp I) ≪≫ Scheme.Modules.restrictFreeIso U.2.isoSpec.hom I).symm
```

## New

```lean
@[irreducible]
noncomputable def affineBasisDualIso {Y : Scheme.{u}} (U : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, U.1)) {I : Type u} [Fintype I]
    (b : Basis I Γ(Y, U.1) M) :
    SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
      ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj M)
      (SheafOfModules.unit U.1.toScheme.ringCatSheaf) ≅
    (tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj
      (ModuleCat.of Γ(Y, U.1) (M ⟶ ModuleCat.of Γ(Y, U.1) Γ(Y, U.1))) := by
  classical
  exact affineDualTransportIso
    ((SheafOfModules.homFunctor U.1.toScheme.toRingedSpace.sheaf).flip.obj
      (SheafOfModules.unit U.1.toScheme.ringCatSheaf))
    (affineBasisCoordinatesIso U M b) (affineDualBasisCoordinatesIso U M b)
    (SheafOfModules.homObjFreeUnitIso.{u} (R := U.1.toScheme.toRingedSpace.sheaf) I)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineFiniteFreeDualNaturality | X2 | Same elaborated signature and mathematical maps; shared coordinates and proved assembly. |
| Sheaf.AlgebraicGeometry.AffineFiniteFreeDualComplexComparison | unclaimed | Only uses the signature and naturality theorem; compile the original against this delivery. |

The complete downstream import closure was checked with tools/downstream.py
--uses; these are all textual declaration users. No downstream module is
adapted. The original direct consumer is checked separately against the new
compiled module.

## Status

landed 20261013T171520-L-1984152 2026-10-13 (merge of deliver/X2/Sheaf.AlgebraicGeometry.AffineFiniteFreeDualNaturality)
