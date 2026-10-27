# Sheaf.Paper.DerivedPullbackTensorConstraints

## Reason

The three normalized common-stage constraints bundled existence and uniqueness in
one theorem. Their uniqueness halves are elementary after naming the existence
halves, so the existence obligations are exposed as separate named statements.

## Old

The item module had only the three `*_existsUnique` declarations, each admitted.

## New

The module adds `pullbackTensorCommonComposition_exists`,
`pullbackTensorCommonAssociator_exists`, and
`pullbackTensorCommonBraiding_exists`, each asserting only the corresponding
stagewise representative existence. The parent declarations now prove uniqueness
by comparing two candidates at a common finite stage. Existing signatures and
definitions are unchanged.

## Users

The new declarations are additional public names. Existing downstream users of
the original declarations remain source compatible and need no adaptation.

## Status

landed 20261027T210131-L-1661663 2026-10-27 (merge of deliver/M1/Sheaf.Paper.DerivedPullbackTensorConstraints)
