## What changed

Filled `automorphismConstructibleStage_integral_shifts` with a real composition of two
strict auxiliary witnesses: one for signed integral pullback shifts at every morphism,
and one for the normalized shifts and commuting square at the three maps in the theorem.
The two auxiliary statements are public split-off theorems in
`Sheaf.Paper.AutomorphismConstructibleIntegralShiftData` and
`Sheaf.Paper.AutomorphismConstructibleIntegralShiftWitness`; the item imports them as
proof-only imports.

## Proved and sorry left

Closed the `automorphismConstructibleStage_integral_shifts` sorry. Added the strictly
smaller named holes `automorphismConstructibleStage_integral_shift_data` and
`automorphismConstructibleStage_integral_shift_witness`, each with its own DAG node.
The common-stage square theorem and descended-shifts theorem remain unchanged and still
contain their original sorries.

## No longer needed

No existing imports or DAG dependencies were removed. The integral-shift proof now uses
the two new auxiliary nodes listed above.

## Where the brief, the DAG or earlier work was wrong

The original node's shift proof plan was too coarse to implement in one declaration under
the available interfaces. Its integral shift argument naturally separates into the
all-morphism signed Roos shift and the normalized three-map square witness. No statement
or definition was weakened.

## New nodes

`new-h2-integral-shift-data` records the signed shift data for every integral pullback;
its Lean declaration is `WeilConjectures.automorphismConstructibleStage_integral_shift_data`.

`new-h2-integral-shift-witness` records the normalized integral shift witnesses and
square compatibility; its Lean declaration is
`WeilConjectures.automorphismConstructibleStage_integral_shift_witness`.

## Related modules compiled before delivery

11 related module(s) compiled against this delivery by deliver3.py: 10 OK, 1 SLOW.

```json
{"capped": false, "direct": 11, "left_out": 0, "own": {"Sheaf.Paper.AutomorphismConstructibleIntegralShiftData": "bfc012d5f9077f466b37ca18c174f5610132601d", "Sheaf.Paper.AutomorphismConstructibleIntegralShiftWitness": "a2289855aac2f6e93007ebe7bdaba4a14c838acc", "Sheaf.Paper.AutomorphismConstructibleStageEquivalence": "96d5edca7d4a1fab66ad0d460a4ebbddef48da06"}, "results": {"Sheaf.Paper.AutomorphismSquareRationalScalar": {"hash": "3f633ada8bff092437f93fb7723baa024f6035b2", "status": "OK"}, "Sheaf.Paper.CommonStageOpenHeartAdjunction": {"hash": "9c5fc8eee1c11e239dcc5d8b35671125e5703e3e", "status": "OK"}, "Sheaf.Paper.FieldWeilShriekShiftData": {"hash": "5c0b9354c99c9e73728a547bd4397bc11046c209", "status": "OK"}, "Sheaf.Paper.FixedPairTruncationCohomology": {"hash": "2d664b1e22e47b4d2c2480150ffe682699b01589", "status": "SLOW"}, "Sheaf.Paper.FrobeniusPullbackOrdinaryExchange": {"hash": "9a3d90de23be8c6da1565d784f371530b6cd875f", "status": "OK"}, "Sheaf.Paper.ResidueCompatiblePullbackFrobenius": {"hash": "3809fb3bf7cf447f73328d73f4943b7fdf05fed4", "status": "OK"}, "Sheaf.Paper.SfNormalizedRationalWeilSquares": {"hash": "f6275bc1a5725a9b6de7b033c4b5b3b89996817f", "status": "OK"}, "Sheaf.Paper.SfOpenClosedTriangleAllStages": {"hash": "f6be17105c0c75668b15a4398ff58ce2cbce0a37", "status": "OK"}, "Sheaf.SixFunctors.OpenClosedWeilMateFinite": {"hash": "8c1cddfd4a509daed116b18d02a8678db143e7ed", "status": "OK"}, "Sheaf.SixFunctors.OpenClosedWeilMateIntegral": {"hash": "d42f07b1e8972be9600efb177069f4a042a6ce6d", "status": "OK"}, "Sheaf.SixFunctors.SupportedWeilMateLift": {"hash": "dd593ad91ee5296e4c3c0ffc281f23c784a54726", "status": "OK"}}, "seconds": 246, "time": "2026-10-28T07:27:43+0800", "transitive": 0, "version": 1}
```

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
