# System tensor mate proof scopes and returned-base repair

## Reason

The batch rollback restored the ten original theorem holes in
`Sheaf.Paper.SystemTensorMateArrows`. This delivery retains five of H8's proofs, replaces its continuity and ordinary
open-unit proofs by shorter varying-ring applications, and retains B8's
`Operations.alpha_existsUnique` proof against that current file.
The scoped commands and private instances require a change record.

## Old

The current source has ten theorem holes and none of the retained proof helpers
or private proof imports. Its public interface is the original one.

## New

Eight theorem proofs are complete; two original theorem holes remain. Every
existing declaration signature, definition body, public import, visibility and
instance attribute is preserved. No public declaration or new hole is added.
The coefficient, additive, K-injective, tensor and compositor proof bodies are
H8's original constructions. Continuity applies varying-ring continuity; the
ordinary open unit is transported by uniqueness of adjoints. The clopen Hom
bijection argument is B8's proof. No definition body changes.

The wrappers `open SheafOfModules in` and
`open CategoryTheory.MonoidalCategory in` affect only enclosed declarations.
Selected proofs locally set the backward transparency options to true.
Section-local irreducibility of `coefficientSequenceCommRingSheaf` and
`laxTensorPresheaf` controls elaboration only. All pre-existing global options
are unchanged.

The private instance `commRingSheafify` supports the coefficient proof. All
other added declarations are private and fully proved. The three new imports
are proof-only imports. The earlier duplicate open-site construction and its
two private continuity instances are removed from the retained packet, as is
its private `Mathlib.CategoryTheory.Adjunction.Triple` import.
The node's proof, proof dependencies and proof origin describe these arguments;
all other node fields come from the current source.

## Users

| Module | Current holder | Effect |
| --- | --- | --- |
| Sheaf.Paper.SystemTensorMateArrows | B8 | Proofs and private support only. |
| Sheaf.Paper.FiniteFreeCompactComposition | Unchanged consumer | Public interface preserved. |
| Sheaf.Paper.SystemClopenTensorCompatibility | Unchanged consumer | Public interface preserved. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | Unchanged consumer | Public interface preserved. |

The latter three consumers are quarantined and preserved. No consumer source is
adapted. No target statement review reopens because no definition or statement
meaning changes. No adopted source-library module is edited.

## Validation

The complete sandbox module compiled through `lcompile.py` (33.6 seconds
on the final shortened proof check). The delivery
runs the compiler probe, axiom audit and server preflight. The two remaining
holes are named in report.md.

## Status

landed 20261020T230719-L-604533 2026-10-20 (merge of deliver/B8/Sheaf.Paper.SystemTensorMateArrows)
sandbox compiles. Eight current theorem holes are closed, no holes are added,
and two original theorem holes remain. Public signatures and definitions are
unchanged; no consumer adaptation is required.
