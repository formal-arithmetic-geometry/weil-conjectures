## What changed

Proved AlgebraicGeometry.ProEtale.CondensedRing.coefficientComparisonData_exchangeSteps
with its original signature. Specialize the existing threeStepComparison theorem,
reverse its four vertex isomorphisms, identify the restricted factors with their
ambient factors, and append the two specified total-arrow factorizations.
The restricted square is compared at the isomorphism level before taking its hom.
This avoids normalizing large derived constructions through morphism projections.

The coefficient API and the etale MorphismDefs keep three existing construction
bodies behind no_expose and supply proved equations. The mathematical objects are
unchanged. Two unclaimed consumer modules use the square equation in place of
unfolding its body. Updated the existing item, coefficient API and derived square
node records to describe the actual proof and equation APIs. No new DAG node is added.

Change record: coord/changes/B2-coefficient-exchange-derived-caches.md.

Repair of the returned delivery (2026-10-17): removed the duplicate private
triple_app declaration from CoefficientDerivedFunctorAPI. Its component equation
now uses Mathlib NatIso.trans_app twice, followed by a definitional change and
reflexivity. The existing upstream triple_app is private; no duplicate or new
public helper is introduced. The generic ambient specialization is now written
directly in the main proof. An explicit proof import of
WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB supplies the shortcut instance
that the kernel needs.

Rebased the retained etale MorphismDefs copy onto the current shared source,
retaining only the intended no_expose attribute and proved square equation.
This removes the obsolete root Mathlib and lower-shriek imports from the retained
copy. Added the newly separated LowerShriek.MorphismDefs consumer to the change
record's user table. The prior independent reading below describes the returned
version; the second reader must check these repair edits anew.

## Proved and sorry left

Closed 1 of 1 original holes:
AlgebraicGeometry.ProEtale.CondensedRing.coefficientComparisonData_exchangeSteps
(node lem-weil-pbc-coefficient-exchange-from-comparisons).
Added 0 holes and split off 0 statements. The item has 0 remaining sorry.
Every remaining helper and every new equation is proved. The five delivered Lean modules
contain no sorry; imported pre-existing obligations are unchanged.

All five repaired files compile with lcompile.py --all: coefficient API 18.1 s,
item 13.2 s, etale MorphismDefs 6.0 s, DerivedComparison 12.0 s, and
OpenInjectiveCoefficientLowerComparisonFactorization 22.1 s. The original newly
separated lower-shriek MorphismDefs consumer also compiles unchanged against
the sandbox overlay in 4.8 s. The two original consumer files were rechecked
against the same overlay: DerivedComparison fails at lines 83 and 85, and
OpenInjectiveCoefficientLowerComparisonFactorization fails at line 209 as
recorded below; their delivered adaptations compile.
The repaired item with its original local instance compiles in 14.1 seconds.
Its original statement, instance and visibility remain unchanged.
Final validation commands: lcompile.py --all on this five-file sandbox and
deliver3.py B2 Sheaf.Paper.CoefficientExchangeFromComparisons --no-push.
Repair dry run returned OK: commit bb0854864a compiles and passes the preflight.
Nothing was pushed. The delivery remains CODEX for the independent reader.

## No longer needed

Return repair: removed the duplicate private triple_app declaration. The ambient_steps
helper is inlined into the main proof. Pruned the stale root Mathlib and the two
lower-shriek public imports from the retained etale MorphismDefs copy, matching
the current source module. No additional DAG node or module is pruned.

Removed proof import WeilConjectures.SixFunctors.BaseChange.Derived.
The second reader also removed its redundant replacement proof import
WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs: it is already
publicly available through FiniteDiscreteDerivedCoefficientData and the
coefficient API's FiniteDiscreteRealizationFunctor import.
The proof uses the component and factorization API in the two MorphismDefs modules.
The derived exchange node is still needed for the specified exchange morphism;
threeStepComparison and the coefficient API also remain needed. No blueprint unit
statement or realized proof step is bypassed, and no DAG node becomes unnecessary.

## Where the brief, the DAG or earlier work was wrong

The mathematical proof plan works. The exposed concrete square implementations made
an otherwise elaborated specialization fail kernel checking within the file limit.
Caching the same objects and using component equations resolves this implementation
issue without changing statements, constructions, hypotheses or compiler limits.

The arbitrary-coefficient restricted direct-image preservation statement is already
marked STATEMENT-DISPUTED upstream. This delivery retains the finite-discrete
coefficient statement and does not alter that source interface or its existing hole.

## Forced adaptations

Both consumers are unclaimed. Existing signatures, visibility and all conclusions stay
identical; only the forced square-unfolding lines change.

- WeilConjectures.SixFunctors.BaseChange.DerivedComparison: the original line 83
  reports Invalid simp theorem pullbackSquareComparison: Expected a definition with
  an exposed body, followed by failure of rfl at line 85. Replace the single simp
  entry Etale.pullbackSquareComparison with Etale.pullbackSquareComparison_def.
- Sheaf.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparisonFactorization:
  the original line 209 cannot unfold the non-exposed pullbackSquareComparison.
  Replace the single simp entry pullbackSquareComparison with
  pullbackSquareComparison_def. The remaining proof is identical.

Consumer checks: of 52 original textual users of the etale adjunction and square,
49 compile unchanged and the two necessary one-line adaptations compile. The
unchanged FailureOverField.ClosedOpen reaches the 60-second limit both with the
published baseline alone and with the repair; no new error was observed there.
FailureOverField.Transition passes unchanged in 59.0 seconds and
FailureOverField.Survival passes unchanged in 59.3 seconds with the minimal repair.
The six consumers that required adaptations in an earlier, broader experiment all
compile in their original form after retaining the original etale adjunction interface.
Only the two square-unfolding adaptations are included in this delivery.

## Earlier second reading (a previous round; superseded)

1. **Signatures and accidental changes — pass.** Compared all five delivered
   modules with the shared repository. The target theorem and every existing
   declaration keep their original signatures, hypotheses, visibility and
   conclusions. The only interface changes are the declared `no_expose` cache
   attributes and the three proved equation APIs in the accompanying change
   record; the two consumer edits are the forced one-line adaptations described
   above.
   Independently recompiled both original consumers against the final sandbox
   overlay: DerivedComparison fails at its square-unfolding simp argument and
   subsequent `rfl`; OpenInjectiveCoefficientLowerComparisonFactorization fails
   at its square-unfolding simp argument. Their delivered one-line repairs
   compile. No additional adaptation is needed for the etale adjunction.
2. **Proof and axioms — pass.** Compiled all five files with `lcompile.py --all`.
   The item closes its sole original `sorry`; no delivered file contains `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern` or `implemented_by`. The proof uses the
   existing three-step comparison, restriction identities, and component APIs;
   no arbitrary witness is introduced.
   An explicit scratch-copy `#print axioms` check gives only `propext`,
   `Classical.choice`, and `Quot.sound` for all three new equation lemmas.
   The item theorem additionally uses `sorryAx` from imported pre-existing
   obligations, including the disputed restricted direct-image preservation
   statement; it is locally closed, not yet axiom-clean in its import closure.
3. **Statements and split nodes — pass.** No statement was split off and no
   new hole or DAG node was added. The three equation lemmas are true
   definitional equations for unchanged constructions, and the updated node
   records list their declarations and proof dependencies. The existing target
   statement is unchanged and the finite-discrete coefficient hypotheses are
   retained.
   The component equations and inverse-cancellation helper require no nonempty
   object or nonzero ring hypothesis, so zero coefficients, zero objects and
   empty schemes introduce no exceptional case. The specialization needs only
   the supplied commutative square, not Cartesianity or properness.
4. **Shortest route and pruning — pass.** The proof uses the stated
   three-step-comparison and derived-exchange route, with the coefficient API
   for the restricted factors. The obsolete `BaseChange.Derived` proof import
   is removed; no unit statement or realized step is bypassed, and no remaining
   proof dependency is unused. Removed the redundant explicit etale MorphismDefs
   proof import after a scratch-copy compile confirmed it was unnecessary.
5. **DAG agreement — pass.** The item node's proof, `proof_deps`, and
   `proof_origin` match the compiled proof, and the two changed definition nodes
   record their equation APIs. The unit `sk-thm-properbasechange` and chapter
   `sec-proper-base-change` remain attached.

Changed during this second reading: removed one redundant proof import and added
this review record with the explicit axiom results. No mathematical proof, DAG,
or change-record repair was needed.

## Second reading by B2

1. **Signatures and accidental changes — pass.** Compared all five delivered
   modules with the shared repository. The target theorem and all existing
   declarations retain byte-for-byte signatures. The only interface changes are
   the declared `no_expose` attributes and proved equation APIs recorded in the
   change record; the two consumer edits are forced one-line proof adaptations.
2. **Proof and axioms — pass.** `lcompile.py --all` compiles all five files.
   The target closes its sole original hole, with no delivered `sorry`, forbidden
   declaration, or hollow definition. The helper and equation declarations are
   proved; imported upstream `sorryAx` obligations are unchanged.
3. **Statements and split nodes — pass.** No statement was split off and no new
   hole or DAG node was added. The target statement, coefficient constructions,
   and equation APIs are unchanged in mathematical meaning. Empty schemes and
   zero objects require no extra hypotheses.
4. **Shortest route and pruning — pass.** The proof follows the existing
   three-step comparison and restricted-factor route, keeps the unit attachment,
   and removes only the stale `BaseChange.Derived` and redundant proof imports.
   No proof dependency or realized unit step is bypassed.
5. **DAG agreement — pass.** The target and changed definition nodes record the
   actual declarations, proof dependencies, proof origins, and equation APIs.
   The change record lists all textual users and both forced adaptations.

Changed during this second reading: compiled the final five-file set, rechecked
all diffs and node records, and appended this review. No further source repair
was needed.
