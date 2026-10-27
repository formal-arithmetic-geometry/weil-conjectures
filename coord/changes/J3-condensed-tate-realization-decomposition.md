# Normalized condensed Tate realization: two independent comparison steps

## Reason

The final theorem mixes the strict derived-limit comparison with the scalar-extension
comparison, then has to establish uniqueness and apply the prescribed shift. Separate
these independent comparison steps and prove the final assembly. This is a decomposition,
with two new holes; it does not claim to finish the geometric or tensor calculations.

## Old

All constructions and two holes are in Sheaf.Paper.CondensedTateRealization:
`integralComparison_existsUnique` and `condensed_tate_realization`.
The assigned quarantine archive has been read and preserved. The live item was restored
while this session was working; its content agrees with that archive.

## New

Move all constructions, existing proved helpers, and the unchanged integral-comparison
statement into Sheaf.Paper.CondensedTateIntegralData and
Sheaf.Paper.CondensedTateRealizationData. The namespace, names, signatures,
instance attributes and definition bodies are retained. The integral-data module has one hole,
`integralComparison_existsUnique`, now attached to its own coefficient-comparison node.
The item publicly imports this data module, preserving the previous public declarations
and public import closure for its consumers. Private proof helpers move with their uses.
No source-library declaration or target signature changes.

The new modules Sheaf.Paper.CondensedTateAugmentation and
Sheaf.Paper.CondensedTateScalarPower state invertibility of, respectively, the original
`derivedAugmentation` and the scalar adjoint of `derivedBalancedPower`. Each is an actual
step of the old proof and has its original source and complete proof in words.
Neither asserts an isomorphism from the realized reconstructed shifted object to the
Tate twist. Their statements are independent of each other: one is about reconstruction
before scalar extension, the other about scalar extension before reconstruction.

The item constructs the unshifted isomorphism as the inverse image of the augmentation
followed by the scalar transpose. The private generic categorical proof checks its
adjunction normalization and proves uniqueness by cancellation. The public theorem then
uses exactly the old `shiftedComparison` to transport it. All hypotheses of the public
theorem, including its canonical-reduction hypothesis, stay verbatim.

## Users

The three direct importers below were found in quarantine and were also temporarily
available in the live Lean tree during this session. Their full preserved sources are checked
against the delivery without changing or withdrawing their archives or attachments.
Their content needs no adaptation because every original public declaration is reexported
under exactly its old name with the same construction and instance registrations.

| Module | Holder | Effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedOpenCounitRealization | archive/restoration; no adaptation | Same API via public reexport; baseline compiler failure recorded below. |
| Sheaf.Paper.CondensedOpenCounitComparisons | archive/restoration; no adaptation | Same API via public reexport. |
| Sheaf.Paper.CondensedOpenCounitUnits | archive/restoration; no adaptation | Same API via public reexport; baseline compiler failure recorded below. |

The unchanged Comparisons consumer compiles against the delivery. Units fails at
its existing CounitNormalized definition, line 213, with kernel error
`unknown constant 'instEssentiallySmallProfinite_sheaf'`. An isolated compile
without any delivery outputs reproduces the same failure (also at lines 125 and
150). Realization also fails identically with and without the delivery:
`generalize` fails at line 89 and the kernel reports the same unknown constant at
line 80. No forced adaptation to these consumers is made. Their full archives are
retained and all temporary validation copies are removed from the packet.

The new proof dependencies are below the original node, and every old geometric and
coefficient dependency remains below one of those split nodes. No unit route is bypassed.
The main node's mathematical statement and statement dependencies are unchanged.

## Status

Prepared for independent review; compiler verification is recorded in report.md.
