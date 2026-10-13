# Shared additive comparison constructor

## Reason

The original equivalence constructor rechecks a large scalar-cohomology and Ext
expression. Use the existing bundled additive maps and a typed local binding instead.
The signature, visibility, exported attributes and underlying function are unchanged.
The equality check certifies that no target meaning changes. Per AGENTS.md §4,
the definition edit nevertheless reopens the semantic review of affected targets.
No consumer is adapted.

## Old

```lean
def scalarCohomologyExtEquiv (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ) :
    scalarCohomology f F n ≃+
      Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) (scalarSheaf f F) n :=
  { Equiv.ofBijective (scalarCohomologyExtMap f F n)
      (scalarCohomologyExtMap_bijective f F n) with
    map_add' := scalarCohomologyExtMap_add f F n }
```

## New

```lean
def scalarCohomologyExtEquiv (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ) :
    scalarCohomology f F n ≃+
      Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) (scalarSheaf f F) n := by
  let T : scalarCohomology f F n →+
      Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) (scalarSheaf f F) n :=
    (((Abelian.Ext.precomp (Abelian.Ext.mk₀ (scalarUnitMorphism f))
      (scalarSheaf f F) (zero_add n)).comp
      ((scalarFunctor f).mapExtAddHom (SheafOfModules.unit X.ringCatSheaf) F n)).comp
        (moduleExtEquiv F n).toAddMonoidHom)
  have hb : Function.Bijective T := by
    have hb := scalarCohomologyExtMap_bijective f F n
    unfold scalarCohomologyExtMap scalarExtMap at hb
    exact hb
  exact AddEquiv.ofBijective T hb
```

## Equality and edge cases

`scratchpad/TacticEquivExtEqualityFixed.lean` compiled through lcompile.py.
It proves equality of the complete additive equivalences by AddEquiv.ext, unfolding
both constructors and the composed maps, then rfl. In particular inverse functions
also agree. This checks every field and characteristic, every degree, zero sheaves,
and the empty scheme; no nonzero or nonempty hypothesis is introduced.

## Users

The downstream script found 253 transitive importers and the following 15 textual
users of the definition at search time. The table also includes later textual users
found by rg during this session. All signatures remain unchanged; no forced adaptations.

| module | holder | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ExternalCupScalarBalance | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations | T3 | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupCochain | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyExtZeroGlobalSections | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackSquare | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupCoefficientNaturality | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackCoefficientNaturality | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackNaturality | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupUnitIdentities | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupZeroGlobalSections | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarPullbackZeroGlobalSections | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitClassPullback | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitCohomologyPullbackNaturality | unclaimed | Equal additive equivalence; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitExtClass | unclaimed | Equal additive equivalence; no adaptation. |

## Status

landed 20261013T144157-L-615218 2026-10-13 (merge of deliver/T3/Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations)
