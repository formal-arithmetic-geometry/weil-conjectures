# WeilConjectures.coefficientTwistPower

## Reason

The paper-specific and general-site tensor powers have the same recursive equations,
but their separately compiled recursors are not definitionally equal at a variable
exponent. A pointwise equality is proved by two-step induction (zero, one, and the
same right tensor functor applied to the induction hypothesis). That equality cannot
be rewritten across the dependent signed-comparison family and its unit/tensor/dual
normalizations as though it were definitional equality. Use the existing general
construction as the canonical one, and make the paper-specific construction an
abbreviation, as required by brief-stage3 section 4 for duplicate definitions.

This is a definition repair in an unclaimed Sheaf module. It adds no data choice and
no theorem hole. No declaration or import in the adopted WeilConjectures source tree
is changed. The paper's definition has precisely the same zero, one, and successor
objects, using the same module unit and tensor functor. Every target whose statement
uses this definition is reopened for semantic review; its mathematical meaning is
preserved and no target signature changes.

## Old

```lean
def coefficientTwistPower {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    ℕ → SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  | 0 => SheafOfModules.unit.{u, u + 1, u + 1} _
  | 1 => L
  | n + 2 => (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) L).obj
      (coefficientTwistPower L (n + 1))
```

## New

```lean
abbrev coefficientTwistPower {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    ℕ → SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
  SheafOfModules.scalarTensorPower R L
```

The definition requires the public import
`Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions`. Its import direction was
checked: that module does not reach `Sheaf.Paper.CoefficientTwistsDetailed`.

## Users

`tools/downstream.py Sheaf.Paper.CoefficientTwistsDetailed --uses
coefficientTwistPower coefficientTwistLine` lists 754 transitive importers; the
following is the complete union of its two declaration-use lists. The mathematical
check is uniform for every row: the objects agree at zero and one and their common
successor tensor functor preserves the preceding equality, hence the power functions
are equal by two-step induction; both definitions of signed lines then agree by
integer cases. No hypothesis, action, evaluation pairing, or conclusion changes.
The unclaimed consumer `Sheaf.Paper.IntegralLineReductionDefinitions` requires
three proof adaptations. Its old `scalar_power_eq` proof simplifies with the
induction hypothesis, which becomes reflexive after the abbreviation is introduced:
compilation fails at line 91 with `maximum recursion depth has been reached`.
The equality proof and the two signed-power equality proofs are now `rfl` (after
integer cases for the latter). Their signatures and visibility stay identical.

The unclaimed consumer `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` also needs
a forced proof adaptation, as requested by reviewer C-78a5a for returned head
`78a5acd199b`. Its original `scalarExtensionFunctor_line` fails at line 583:6
against the delivered abbreviation with `Type mismatch: After simplification`:
the supplied isomorphism uses
`(SheafOfModules.scalarTensorPower R L 1).siteSheafTensorRight`, whereas the
expected isomorphism uses `SheafOfModules.siteSheafTensorRight L`.
Add `SheafOfModules.scalarTensorPower` to the `simpa only` list at lines 583-585
so that the degree-one tensor power reduces to `L`. This is the only proof change;
all declarations, signatures, visibility, definitions and imports stay identical.
The prior row claiming compatibility passed without this adaptation was wrong.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | same objects and statements; compatibility compilation passed |
| `Sheaf.Paper.CartesianCoefficientTwists` | P2 | same objects and statements; complete item compilation passed in this repair (59.4 seconds with compiled output, 51.3 seconds single-file); local transparency settings avoid repeated construction expansion |
| `Sheaf.Paper.CoefficientTwistsDetailed` | unclaimed | definition consolidated; existing theorem holes unchanged |
| `Sheaf.Paper.DiagonalTowerLimit` | unclaimed | same objects and statements; changed and original controls both reach the 60-second limit |
| `Sheaf.Paper.FiniteTateSiteDescent` | unclaimed | same objects and statements; compatibility compilation passed |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | unclaimed | same objects and statements; compatibility compilation passed |
| `Sheaf.Paper.IntegralLineReductionDefinitions` | unclaimed | three forced proof simplifications; signatures and definitions unchanged; recompilation passed (14.7 seconds in this repair) |
| `Sheaf.Paper.PbcCoefficientTwists` | unclaimed | same objects and statements; compatibility compilation passed |
| `Sheaf.Paper.ProEtaleTateTwists` | unclaimed | same objects and statements; compatibility compilation passed |
| `Sheaf.Paper.ProEtaleTateTwistsOfUniverses` | unclaimed | same objects and statements; compatibility compilation passed |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | same objects and statements; compatibility compilation passed |
| `Sheaf.Paper.SignedLineTensorEquivalence` | unclaimed | same objects and statements; compatibility compilation passed |
| `Sheaf.Paper.SignedTwistReductionComparison` | unclaimed | same objects and statements; compatibility compilation passed |
| `Sheaf.Paper.TateTwistLisseLine` | unclaimed | same objects and statements; compatibility compilation passed (35.3 seconds) |
| `Sheaf.Paper.TateTwistLocallyFree` | unclaimed | same objects and statements; compatibility compilation passed |
| `Sheaf.Paper.TwistPreservesFiniteness` | unclaimed | same objects and statements; compatibility compilation passed |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | unclaimed | forced adaptation in `scalarExtensionFunctor_line`: unfold `SheafOfModules.scalarTensorPower` in the `simpa only` list; original fails at 583:6 with tensor power at one versus `L`; adapted compilation passed (36.0 seconds) |

Compiler checks: the consolidated definition compiled in 39.9 seconds in the full
consumer batch, and the adapted consumer compiled in 17.2 seconds. The earlier
compatibility claim for `ScalarExtensionFunctor` was incorrect; its
original failure and the forced adaptation are recorded above. Other consumers
marked passed above were checked in the original session against the consolidation. A separate compatibility
probe checked definitional equality with the generic powers and signed-line functions.
`TateTwistLisseLine` passed on retry in 35.3 seconds; its original-source control
passed in 33.3 seconds. `DiagonalTowerLimit` reached the 60-second compile limit;
its byte-identical original-source control also reached the same limit, so this
check has not established a regression from the definition consolidation. The
assembled item originally passed in 54.9 seconds. In this repair, all five packet
modules pass the import-order compile, with the item taking 59.4 seconds including
compiled output and 51.3 seconds in the single-file check after local transparency
adjustments; all public statements and
definition bodies are unchanged. Temporary byte-identical consumer
copies are used only for these checks and will not be included in the packet. The
forced adapted `ScalarExtensionFunctor` is included in this repaired packet and
compiles in 36.0 seconds. The repair-session batch also recompiled the consolidated
definition (28.6 seconds), `IntegralLineReductionDefinitions` (14.7 seconds), and
`NativeIntegralTateTowerLimit` (5.0 seconds).

## Status

landed 20261022T040211-L-2832816 2026-10-22 (merge of deliver/P2/Sheaf.Paper.CartesianCoefficientTwists)
