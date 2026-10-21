# Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism proof elaboration commands

## Reason

The proof compares module sheaves presented through commutative and noncommutative
completed rings, chosen inverse limits, tensor functors and strict mapping cones.
Local irreducibility prevents expensive unfolding of existence witnesses; elaboration
options permit the explicit definitional transports. These commands change no declaration
signature or definition. The local attributes expire at the end of this module.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
```

There was no local irreducibility command.

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
```

After the four unchanged public definitions:

```lean
attribute [local irreducible] integralScalarReductionWitness scalarReductionExistence
  scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
```

Individual theorem proofs also have scoped heartbeat budgets and explanatory comments.
All original public imports and the signatures and bodies of tower, product, inclusion
and leg remain verbatim. The existing public theorem has its original signature.

## Users

`python3 tools/downstream.py Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism
--uses regular_scalar_unit_quasi_isomorphism` reports zero downstream modules and only
the declaration's own module as a textual user. No consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism | X3 | Filled proof; private helpers and proof elaboration commands only. |

The DAG parents still refer to the unchanged theorem. Their statements and meanings are
unchanged. No target definition changes and no target statement review is reopened.

## Status

landed 20261021T162134-L-296773 2026-10-21 (merge of deliver/X3/Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism)
