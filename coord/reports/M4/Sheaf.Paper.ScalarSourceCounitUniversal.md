## What changed

Proved `WeilConjectures.PurStrictScalar.scalarSourceCounit_universal` in
`Sheaf.Paper.ScalarSourceCounitUniversal`, preserving its statement and all public
imports. Two proved private categorical helpers transfer the absolute right-derived
limit universal property through adjunction mates and through the fully faithful
precomposition functor of the homotopy quotient. The concrete proof then transports
the counit through the existing ordinary and exact derived functor factors.

Updated the node `lem-pur-scalar-source-counit-universal` proof and proof origin to
record this route. Both original coefficient-data dependencies remain in use. No
other module, definition, statement, target, or unit route changes.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.PurStrictScalar.scalarSourceCounit_universal`
(node `lem-pur-scalar-source-counit-universal`). Added zero holes and zero split-off
statements. The delivered module has zero `sorry` occurrences. The private helpers
are proved in full. Existing upstream obligations are used through their unchanged
interfaces, as required by stage 3.

Validation: the delivered module compiled cleanly through `lcompile.py` in 53.1 s.
The original theorem statement was checked byte-for-byte unchanged; the node diff
changes only `proof` and `proof_origin`.

## No longer needed

No original import, DAG dependency, or module is withdrawn. The proposed K-flat
replacement argument and the extra claim that restriction and finite free tensor
preserve its acyclic replacements are unnecessary: absolute K-injective right
derivation and the existing adjunction imply the postcomposed left-derived
universal property directly. No new modules are needed for those proposed steps.

## Where the brief, the DAG or earlier work was wrong

The original proof plan was longer than necessary. The recorded adjunction already
identifies the native counit as the mate of the right-derived limit unit. Its
absolute K-injective universal property gives precisely the needed universal
property after the entire restriction/tensor postcomposition, without a separate
K-flat compatibility argument. No statement was disputed or repaired.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
