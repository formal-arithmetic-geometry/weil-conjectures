## Delivery

Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-hypersurface-derivation-regular.json`: split into localization, local derivation, and regularity-locality steps.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-regular-local-hypersurface-criterion.json`: new reusable statement-only criterion for the local step.

The proof follows More on Algebra, Lemma 07PF (lemma-quotient-regular), with its reduction to local rings, the Leibniz-rule contradiction, and Algebra Lemma 00NQ. The local criterion is represented as a separate statement node so the argument does not hide a reusable lemma. The new node has `created.item` equal to this item, exact Stacks sources, and three Mathlib searches. No Lean was written or compiled.

No self-review was run; the lead must review the mathematics and add the lead review section before delivery.

## Review by E1

I checked the parent split against More on Algebra Tag 07PF and the cited localization and regularity results. Step 1 correctly reduces primes of the quotient to localized quotients. Step 2 preserves the unit relation after localization and uses the Leibniz rule to exclude membership in the square of the maximal ideal before invoking the public local hypersurface criterion. Step 3 supplies Noetherianity and the local criterion for regularity. The new criterion is statement-only, public, has exact `created.item` metadata, and is not duplicated in the current DAG. The report and split metadata are complete, with no Lean changes.
