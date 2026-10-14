# Proof elaboration settings for singleton tensor Čech cofaces

## Reason

Prevent expansion of tensor-pullback constructions during proof elaboration.
Removing the local transparency commands produces a deterministic `whnf` timeout
at 200000 heartbeats in `singletonTensorCech_coface_map_down`.
The static delivery checker classifies added attribute commands as potential
interface changes and requests this record.

## Old

Module `Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechCofaceEvaluation` had no local
transparency settings and left `singletonTensorCech_coface_map_down` unproved.
All original public signatures, definitions, and imports are preserved verbatim.

## New

The file's section locally marks `Modules.tensorPullback`,
`Modules.tensorPullbackObj`, and `Modules.etaleTensorSectionsRestriction` irreducible,
and sets both `backward.isDefEq.respectTransparency` elaboration options to true.
These commands prevent unnecessary unfolding during elaboration. They do not change
any definition, public signature, or the kernel's definitional equality.
A scoped `linter.unusedVariables false` setting suppresses the existing unused `P`
let-binding warning without changing the original public statement.
The previously open theorem now has a complete proof using three proved private helpers.

## Users

The module is held by S1 (this item). No other module is adapted.
The attributes are local to this section and the settings control only elaboration
of this file; importing modules see identical mathematical interfaces. No public
statement or definition changes, no forced adaptations, no new nodes, no new imports.

## Status

landed 20261014T010853-L-3167585 2026-10-14 (merge of deliver/S1/Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechCofaceEvaluation)
