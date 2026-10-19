## What changed

Proved `WeilConjectures.PurityFiniteSetting.smoothPurityTensorPresentation` by unfolding
`ProEtale.derivedTensor` and applying congruence. All signatures, definitions, imports,
and visibility are unchanged. The complete item module compiles through `lcompile.py`
in 7.8 seconds.

## Proved and sorry left

Closed one of the original three holes:
`WeilConjectures.PurityFiniteSetting.smoothPurityTensorPresentation`.
No holes were added and no statements were split off.

The two original holes retained, both belonging to `def-pur-smooth-purity-map`, are:

- `WeilConjectures.PurityFiniteSetting.existsUnique_smoothPurityTensorShift`.
- `WeilConjectures.PurityFiniteSetting.existsUnique_smoothPurityTensorMap`.

## No longer needed

None. No imports, modules, or declared dependency nodes were removed. The proved
interface identity needs only the definition already imported by the original module.

## Where the brief, the DAG or earlier work was wrong

The first interface identity is a direct congruence proof and needs no new result.
For the shift uniqueness theorem, direct rewriting, generalization and transport through
equality elaborate but trigger excessive kernel reduction of the specialized derived
monoidal instances. Several generic transport proofs were tested; none was accepted
within the existing single-file limit. They are not included in this delivery. The
remaining tensor-map theorem also remains unchanged. A categorical descent argument
was explored using the comparison adjunction and naturality, but was not completed.
No mathematical statement is disputed and no target or definition has changed.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
