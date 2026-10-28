## What changed

The statement, public imports and definitions of
`Sheaf.Paper.CompletedIntegralFiniteTowerTransport` are unchanged. Its original theorem
`WeilConjectures.IntegralCompletedComparison.completedIntegral_finiteTowerTransport`
now has a complete Lean assembly proof from two smaller statements in new modules.
Proof imports expose the existing strict/actual comparison construction and completeness
transport helpers; no other existing Lean module is changed.

The proved private helper `strictActualComparison` constructs a global unit-normalized
strict-to-actual isomorphism from the existing reduction, tower and completion comparisons.
The main proof identifies its restriction with the published `towerIso` using uniqueness,
precomposes the strict projection equation, and uses `NatTrans.shift_app_comm` after
proving completeness stable under shifts with the private helper `complete_shift`.
Neither `completedToFiniteTower` nor the finite projection definitions change.

All three files compile cleanly together, in import order, through `lcompile.py --all`:
FiniteIntegralCoefficientComparison 4.6 s, StrictIntegralCoefficientTowerTransport
6.1 s, CompletedIntegralFiniteTowerTransport 15.5 s. There are no compiler warnings.
The new ordinary comparison was checked against the zero module, empty scheme and
n=0 (exponent n+1); its maps are balanced pure-tensor maps. The strict comparison
uses the whole strict tower and its derived limit, not finite evaluations to detect
arbitrary derived arrows. The zero complex, identity map and arbitrary signed shifts
respect the stated counit and generator formulas.

## Proved and sorry left

This is a decomposition, not a net proof of the original obligation: one upper hole
is closed and two lower holes are added (net change +1 hole). No axiom is introduced,
no definition contains a hole, and no data is selected from either existential lemma
in a definition. The witnesses are used only inside a theorem proof.

The original module now has zero `sorry`. Its single former hole belongs to
`WeilConjectures.IntegralCompletedComparison.completedIntegral_finiteTowerTransport`.
The proof of that declaration combines the following two remaining holes:

- `WeilConjectures.IntegralCompletedComparison.finiteIntegral_coefficientComparison`,
  in `Sheaf.Paper.FiniteIntegralCoefficientComparison`, node
  `lem-a1-finite-integral-coefficient-comparison` (one `sorry`).
- `WeilConjectures.IntegralCompletedComparison.strictIntegral_coefficientTowerTransport`,
  in `Sheaf.Paper.StrictIntegralCoefficientTowerTransport`, node
  `lem-a1-strict-integral-coefficient-tower-transport` (one `sorry`).

The private helpers `strictActualComparison` and `complete_shift` are proved without
new holes. Count for the assigned original obligation: 0 of 1 fully proved,
1 decomposed, 2 split off. Existing dependency holes are unchanged.

## No longer needed

No existing import is removed and no module or node is globally pruned. In particular,
`IntegralPullbackRoosFiniteTower` remains a public import for the finiteTowerLimit
interface; its integralPullback_roosFiniteTower theorem is not invoked. The original
coefficient, balanced-generator, finite strict-tower, homotopy-limit and shift
arguments remain dependencies of the new smaller statements. They are not claimed
as pruning merely because the upper theorem now imports their assembly lemma.
The unit route is preserved. No adopted-source declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The old proof plan passed from coefficient
identifications to a normalized derived tower comparison in prose. The available
statements do not directly supply the cross-presentation module isomorphism or its
strict-limit projection and shift compatibility. These are the two remaining steps,
now separated explicitly. The global strict-to-actual comparison is available by
retaining the construction in the existing proof before its restriction to complete
inputs, so no additional existence assumption is needed for that part.

The finite lemma is underived and independent of C, derived limits and completeness.
The strict lemma assumes the normalized finite maps and concerns strict-limit
projections before precomposition with towerIso. It does not assert completeness
stability or identify the restriction of a global comparison with towerIso. Those
steps are proved in the original module. Thus neither new statement is the original
statement renamed; the combining proof includes the global comparison construction,
unit uniqueness, projection composition and completeness/shift argument.

## New nodes

`lem-a1-finite-integral-coefficient-comparison` records the ordinary finite tensor
comparison, with its generator normalization, sourced in Stacks 03EK/03EL and the
finite part of 099N(5). Its module is
`Sheaf.Paper.FiniteIntegralCoefficientComparison`.

`lem-a1-strict-integral-coefficient-tower-transport` records transport of the strict
pulled quotient tower, its normalized computation projection and retained shifts,
before the reflector-to-strict comparison. It uses the finite maps as inputs and
preserves the original strict-tower route from 099N(5), 0941 and 011G/014E. Its module
is `Sheaf.Paper.StrictIntegralCoefficientTowerTransport`.

The original node's proof, proof_deps and proof_origin now follow the written Lean.
No existing statement, Lean attachment, source, blueprint ancestry or unit is changed.
The new-declaration change record is
`coord/changes/J8-completed-integral-coefficient-transport.md`.

## Related modules compiled before delivery

19 related module(s) compiled against this delivery by deliver3.py: 19 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompletedIntegralFiniteTowerTransport": "ed59e58103aba97025c3c2fdacb49518f5813e69", "Sheaf.Paper.FiniteIntegralCoefficientComparison": "25016c6a15556c88caec0b428d03b979912839e3", "Sheaf.Paper.StrictIntegralCoefficientTowerTransport": "f30b0fd633b0b35146f6d5fde56e0d3e7918e3d6"}, "results": {"Sheaf.Paper.ContinuousRationalDerivedRealization": {"hash": "2e9ed7ed16cdb547dfc39c20d3cb1761cdce7562", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemComparison": {"hash": "e493085b773fc372045148189085652d1b924450", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemComparisonData": {"hash": "97d81f9bdad7450a1e62daa9216f167abc5a0124", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemCoordinates": {"hash": "14fe2d2274a0f77c19cbfcaa3f2fd61332279406", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemFiniteOrientation": {"hash": "eb0e96fdd2f148cfa9bfa178452d4305f8ea3ca7", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemHeart": {"hash": "9a070f47bd829208725e5f5eeee2aac22cacda63", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemNormalizations": {"hash": "e22be0a0e93d29067a2ae0db451474bb52136641", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemRigidity": {"hash": "18765b5e9e7e37f176463311133d1039cd0b9129", "status": "OK"}, "Sheaf.Paper.FieldPuritySystemTranspose": {"hash": "76d579b774387bd695951bbf5d80a728fd3f189f", "status": "OK"}, "Sheaf.Paper.FieldPuritySystemTransposeBase": {"hash": "0882a7a028b9479a0000159cb4ff3ff179ff9277", "status": "OK"}, "Sheaf.Paper.FieldPurityTransposeArrows": {"hash": "bd6e29a7c71ad614a10743bd1517519239715b5d", "status": "OK"}, "Sheaf.Paper.FieldPurityTransposeLevelWords": {"hash": "d261fe7d404f063aa06890a477215a246d53f6ac", "status": "OK"}, "Sheaf.Paper.FiniteRestrictionDiagramNaturality": {"hash": "81365072e344a50c7cddc314c30b496374b0359e", "status": "OK"}, "Sheaf.Paper.IntegralPullbackCompletedComparison": {"hash": "ea10a66d440f76e3b816535000641df36809eb32", "status": "OK"}, "Sheaf.Paper.RamifiedScalarSystemTranspose": {"hash": "53ac490826ec5a0fa35c7c8f9a5ca4c9b3fca77d", "status": "OK"}, "Sheaf.Paper.RationalModuleRealizationFunctor": {"hash": "d0272af84131d530b5c2167f5f13bb9a2b270b51", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityCommonComparisons": {"hash": "2b8a76033ed0141a0c750ad88d4f804323a159e7", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityLineComparisons": {"hash": "7dfea4a2aa9ca58786b61db04994341c85d15175", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityTraceCoherence": {"hash": "0091913289529cd60ce8938cc38e96ee7a2ce7a4", "status": "OK"}}, "seconds": 287, "time": "2026-10-28T14:20:56+0800", "transitive": 18, "version": 1}
```

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
