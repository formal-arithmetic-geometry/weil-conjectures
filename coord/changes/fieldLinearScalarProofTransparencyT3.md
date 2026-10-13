# Field-linear scalar proof elaboration

## Reason

The retained proof and the unchanged repository module exceeded the single-file compiler
limit. The scalar proof is completed using an explicit scalar endomorphism and cocycle
representatives. The existing resolution comparison is made explicit to avoid repeated
unfolding of derived-functor constructions. The static interface checker conservatively
flags local attribute commands, so this record documents their scope. No declaration
signature, public visibility, or exported reducibility is changed here.
The equal additive-equivalence constructor change is documented separately in
fieldLinearSharedAdditiveComparisonT3.md.

## Old

There were no additional local irreducibility commands for the following Mathlib
constructions before exists_moduleExtEquiv and scalarCohomologyExtMap_smul.
The existing proof of exists_moduleExtEquiv used a transparent chosen resolution,
implicit scheme inference, simplification of its descent compatibility, and a categorical
inverse-composition rewrite. scalarCohomologyExtMap_smul was sorry.

## New

In a section containing only exists_moduleExtEquiv:

```lean
attribute [local irreducible] Functor.rightDerived InjectiveResolution.isoRightDerivedObj
```

Inside the pre-existing nested section containing scalarCohomologyExtMap_smul:

```lean
attribute [local irreducible] Functor.rightDerived InjectiveResolution.isoRightDerivedObj
  Abelian.Ext.comp Abelian.Ext.mk₀ Abelian.Ext.mapExactFunctor
```

Both commands are local and end before leaving their section. Local respectTransparency
options keep these constructions folded. All old exported attributes keep their original
placement and values. The existing resolution-comparison proof uses proved resolution
existence, explicit scheme arguments, desc_commutes_zero, and toLinearEquiv's inverse
identity. The private scalarModuleEnd explicitly multiplies sections by scalarMap f U r.
No importer sees the helper or the proof-only ConcreteCategory import.

## Users

The only newly proved exported declaration is scalarCohomologyExtMap_smul, whose statement
is unchanged. Its textual users are listed below. Other importers see identical existing
interfaces. The separate additive-constructor record documents its equality check
and the semantic review reopened by that definition edit.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations | T3 | Same signatures and exported attributes; equal comparison constructor; no adaptation. |
| Sheaf.AlgebraicGeometry.ExternalCupScalarBalance | unclaimed | Same signatures and exported attributes; equal comparison constructor; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupCochain | unclaimed | Same signatures and exported attributes; equal comparison constructor; no adaptation. |

## Status

landed 20261013T144157-L-615218 2026-10-13 (merge of deliver/T3/Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations)
