# Private scalar-model proof transparency

## Reason

The proof transports ordinary module sheaves through the module-sheafification
adjunction. Repeated unfolding of that adjunction and its sheafification functor
expands the construction during equivalence inference. After proving the generic
unit lemma, local irreducibility keeps later proofs on the named API. The mate
comparison is similarly kept abstract after its factorization has been proved.
The imported `pbcRestriction_isRightAdjoint` instance causes unrelated derived-adjoint
search during the concrete mate conversions. Disable it during these proofs and
restore it at the end, preserving the imported instance table for consumers.

## Old

The existing local attribute is retained:

```lean
attribute [local irreducible] upperStar
```

There are no local irreducibility attributes for module sheafification or the
fixed scalar direct-image mate. The imported
`AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint` instance is active throughout.

## New

The following local attributes are added, after their required unfolding proofs:

```lean
attribute [local irreducible] PresheafOfModules.sheafification
  PresheafOfModules.sheafificationAdjunction
attribute [local irreducible] fixedScalarRestrictionDirectImageMap
```

During proof elaboration the existing adjoint instance is removed and then restored:

```lean
attribute [-instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint
-- private lemmas and proofs
attribute [instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint
```

All declaration signatures, definition bodies and final exported attributes are unchanged.
The settings expire at the end of this module; no target meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage | T5 | Local proof elaboration only. |

No consumer is affected and no consumer adaptation is needed. In particular the
module retains all existing public imports and definitions verbatim.

## Status

landed 20261020T132045-L-1407774 2026-10-20 (merge of deliver/T5/Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage)
