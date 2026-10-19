## What changed

Proved `WeilConjectures.fieldRationalPullComp_existsUnique` in
`Sheaf.Paper.FieldWeilShriekShiftData`. A private tensor-localization comparison transports
an integral natural isomorphism to the prescribed rational functors. Naturality is proved
by tensor induction; equality of the prescribed components gives uniqueness.
No public signature, instance, definition, or target was changed.

## Proved and sorry left

Closed one of the seven original holes:
`WeilConjectures.fieldRationalPullComp_existsUnique`.
Added zero holes; split off zero statements.

The six remaining holes, all unchanged and attached to
`def-zl-field-weil-shriek-shift-data`, are:

- `WeilConjectures.fieldIntegralPullShift_existsUnique`.
- `WeilConjectures.fieldRationalPullShift_existsUnique`.
- `WeilConjectures.fieldCommonPullShift_existsUnique`.
- `WeilConjectures.fieldWeilPull_adjoints`.
- `WeilConjectures.fieldWeilExchange_isIso`.
- `WeilConjectures.fieldWeilShriek_recorded`.

The item compiled through lcompile.py with exit 0 in 34.7 seconds.

## No longer needed

None. The original public imports remain necessary for the statements and definitions.
No new proof import is needed for rational composition. No node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The retained sandbox had no report and its rational-shift proof did not compile.
Its generic rational-composition argument was retained and checked against current sources.
The assigned definition node has no numbered proof steps or proof dependencies; its
statement dependencies and the declarations in its module supply the intended interfaces.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
