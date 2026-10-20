# exteriorPower.isLocalizedModule_of_wedge

## Reason

This is the retirement item in coord/retire-items.tsv for
Sheaf.LinearAlgebra.ExteriorPowerLocalization. The source library now provides
exteriorPower.isLocalizedModule_of_wedge with the identical public signature.
The only differences in the local module are its proof and three private helpers.
Redirect its sole direct consumer, then withdraw the duplicate module and point
its DAG attachment at the source theorem. No source-library file is edited.

## Old

Module: Sheaf.LinearAlgebra.ExteriorPowerLocalization.

```lean
theorem isLocalizedModule_of_wedge
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (S : Submonoid R) [IsLocalization S B]
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} B)
    (f : M ⟶ (ModuleCat.restrictScalars (algebraMap R B)).obj N)
    [IsLocalizedModule S f.hom] (n : ℕ)
    (g : ModuleCat.of R (⋀[R]^n M) ⟶
      (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B (⋀[B]^n N)))
    (hg : ∀ a : Fin n → M,
      g (ιMulti R n a) = ιMulti B n (fun i ↦ f (a i))) :
    IsLocalizedModule S g.hom
```

The local module also contains the proved private helpers extend_multilinear,
localized_multilinear_ext and extend_alternating. Its sole direct importer,
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit, uses the public theorem.

## New

Module: WeilConjectures.LinearAlgebra.ExteriorPowerLocalization, already in the
source library. Its existing public signature is verbatim the same:

```lean
theorem isLocalizedModule_of_wedge
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (S : Submonoid R) [IsLocalization S B]
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} B)
    (f : M ⟶ (ModuleCat.restrictScalars (algebraMap R B)).obj N)
    [IsLocalizedModule S f.hom] (n : ℕ)
    (g : ModuleCat.of R (⋀[R]^n M) ⟶
      (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B (⋀[B]^n N)))
    (hg : ∀ a : Fin n → M,
      g (ιMulti R n a) = ιMulti B n (fun i ↦ f (a i))) :
    IsLocalizedModule S g.hom
```

The consumer replaces its private import of the Sheaf module with the source
module. Its theorem statement, proof and public imports remain verbatim.
The node new-v2-exterior-power-localization points at the source theorem and
records its proof from new-v2-generic-exterior-power-localization.
The old module is listed in deleted.txt; no declaration is retained there.

## Users

Computed with tools/downstream.py and --uses exteriorPower.isLocalizedModule_of_wedge.
All ten downstream modules are listed below; only the first mentions the theorem.
Holder information was read before preparing this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit | unclaimed | Replace the private proof import; theorem statement and proof are identical. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent | unclaimed | Indirect consumer; no edits or statement changes required. |
| Sheaf.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates | unclaimed | Indirect consumer; no edits or statement changes required. |
| Sheaf.AlgebraicGeometry.SelfTorCompatibleAffineMaps | unclaimed | Indirect consumer; no edits or statement changes required. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart | unclaimed | Indirect consumer; no edits or statement changes required. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections | unclaimed | Indirect consumer; no edits or statement changes required. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartSectionEquiv | unclaimed | Indirect consumer; no edits or statement changes required. |
| Sheaf.AlgebraicGeometry.SelfTorIdealWedgeCoordinates | unclaimed | Indirect consumer; no edits or statement changes required. |
| Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates | unclaimed | Indirect consumer; no edits or statement changes required. |
| Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates | unclaimed | Indirect consumer; no edits or statement changes required. |

Validation: the direct consumer compiles alone via lcompile.py in 3.0 seconds.
An independent import probe of the source theorem compiles in 1.6 seconds and
#print axioms reports only propext, Classical.choice and Quot.sound.
The overlaid import graph has no remaining import of the withdrawn module and
introduces no new Sheaf/source twin pair in the consumer's import closure.
All statements, definitions and target meanings are unchanged.

## Status

landed 20261020T135402-L-1817899 2026-10-20 (merge of deliver/F1/Sheaf.LinearAlgebra.ExteriorPowerLocalization)
