## What changed

Replaced the proof of `WeilConjectures.integralScalarPullbackLevelReduction`.
The statement, universes, normalization hypothesis, public imports, and all existing
definitions remain unchanged. Added a proved private generator-extensionality lemma:
transpose ordinary scalar extension, lift completed-linear maps to finite-linear
maps using local surjectivity of the quotient projection, transpose finite pullback,
and apply finite scalar tensor extensionality. The theorem then computes both
composites on the normalized generators using the existing transition specifications
and ordinary scalar tensor naturality.

Private proof imports expose existing proved helpers from
`ScalarExtensionComposition`, `IntegralOperationsWellDefined`, and
`IntegralReductionTowerUnrestricted`. Local irreducibility keeps large chosen
constructions out of elaboration; no shared transparency or instances change.
Updated the item's DAG proof to describe this underived argument.

Validation: `lcompile.py` compiled the complete module cleanly in 19.9 seconds
(exit 0). The public theorem statement matches the original node's recorded
statement verbatim. The module contains zero `sorry` tokens; all lines are at most
100 characters, and the DAG proof dependency list equals the union of step uses.

## Proved and sorry left

Closed the original one hole:
`WeilConjectures.integralScalarPullbackLevelReduction`
(`lem-pur-integral-scalar-pullback-level-reduction`).
Added zero holes; zero holes remain in the delivered module. The private helper
`WeilConjectures.scalar_pullback_hom_ext` is proved in full. No split-off statements
or new nodes were introduced.

## No longer needed

The planned dependency `lem-pur-sheaf-ring-derived-coefficient-adjunction`
(`Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`) is unnecessary
for this lemma and has been removed from its DAG proof dependencies. The proof
uses the ordinary adjunction and its unit formula, already proved in the existing
scalar composition implementation. This does not assert that the module is unused
by other parents or withdraw any declaration.

No existing import was removed: both public imports are needed by the unchanged
statement. All three added private proof imports supply helpers used by the proof.
The other original dependencies remain needed. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned derived coefficient adjunction was stronger than needed for this
chain-level equation. Finite-linearity lifting is necessary before the pullback
adjunction can test only coefficient-one generators; it is supplied by the existing
local-surjectivity proof and `IntegralScalarProof.liftMap`.

The shared checkout lacked this newly landed source and had no rework or quarantine
entry for it. Read the exact current file from the project server and used it as
the starting source, preserving the declaration and documentation verbatim.
No statement defect was found. The argument applies also to level zero, identity
scalar extensions, zero complexes, and empty sites, without additional assumptions.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
