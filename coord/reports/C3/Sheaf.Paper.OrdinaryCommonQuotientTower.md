## What changed

Completed `SheafOfModules.nonempty_ordinaryCommonQuotientTower` without changing any
existing declaration signature, public import, or public definition. All added
helpers are private and proved in the item module.

The ordinary comparison uses the existing ordinary coefficient comparison. Its
multiplication-counit hypothesis follows from the ring-sheaf pushout: the
sectionwise tensor pushout becomes the specified common quotient after
sheafification. The corresponding module multiplication is locally injective and
pointwise surjective, hence invertible after sheafification. Its identification
with the adjunction counit is checked on the explicit unit sections. The standard
normalization supplies an auxiliary ordinary presentation; object and map
identities transport the result to the prescribed models, with the required
pure-tensor formula.

Constructed coefficient transitions by transposing the explicit composite
quotient unit under the ordinary extension/restriction adjunction. The adjunction
identity proves the formula on `1 tensor x`; linearity proves it on `s tensor x`.
Transport and tower naturality give the required adjacent maps. The final proof
assembles these maps and the comparisons into the tower record.

Added proof imports for ring-presheaf pushouts, ring sheafification on an
essentially small site, and the existing ordinary adjunction, normalization, and
coefficient comparison. Updated the existing node's proof, proof dependencies,
and proof origin to describe this route.

The requested scope-command change record is
`coord/changes/C3-ordinary-common-quotient-proof-context.md`; its consumer table
records the unchanged interfaces and absence of necessary adaptations. The previously proved quotient-unit,
kernel, epimorphy, compatibility, and uniqueness arguments remain intact.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.nonempty_ordinaryCommonQuotientTower`
(node `lem-weil-pbc-ordinary-common-quotient-tower`).

Validation: the completed proof compiled without warnings in 39.6 seconds.
A later delivery compile hit the time limit. Profiling identified unnecessary
unfolding outside the helper section; limiting the new transparency option to
that section and making the proved private transition locally irreducible
reduced a profiled full-file run to 24.1 seconds. Development profiling commands
have been removed.

Holes closed: 1. Holes added: 0. Holes left in the item: 0. Split-off statements: 0.

## No longer needed

No original imports, nodes, or modules are pruned: the original dependencies
remain used by the existing unit and kernel proofs. No new nodes are needed.
The old planned construction of `B/(I B)` and its comparison by local scalar lifts
is unnecessary for the remaining existence proof; the ring-presheaf pushout and
the existing ordinary coefficient comparison replace that argument. The unit's
blueprint route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was required. The DAG's remaining quotient
comparison route was longer than necessary given the already proved ordinary
coefficient comparison. Despite that theorem's name, its hypothesis is precisely
invertibility of the multiplication counit, which the common-quotient pushout
provides; no flatness assumption is introduced.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
