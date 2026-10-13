## What changed

Corrected `Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime` so it exposes only
the independent conversion from `IsQuasiFiniteAtPrime` to Mathlib's
`QuasiFiniteAt`.  The duplicate Zariski-main conclusion is removed; callers apply
`Algebra.ZariskisMainProperty.of_finiteType` directly.  The three affected callers
were adapted at their old wrapper call sites.

## Proved and sorry left

`Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime` is proved with its corrected
statement. No `sorry` remains.

Holes closed: none (the baseline declaration was already proved). Holes added:
none. This delivery repairs a duplicate intermediate interface; it does not claim
a net decrease in the sorry ledger. The three adapted caller declarations
`Algebra.ringKrullDim_le_of_isQuasiFiniteAtPrime`,
`Algebra.exists_finite_subalgebra_away_of_isQuasiFiniteAtPrime`, and
`integralClosure_finiteFibrePart_localization` remain proved.

## No longer needed

The duplicate wrapper conclusion and its unfolded existential form are no longer
needed. The callers now use Mathlib's `ZariskisMainProperty.of_finiteType` directly.
The public import of `Mathlib.RingTheory.ZariskisMainTheorem` is replaced with
a plain proof import and the public signature import `Mathlib.RingTheory.QuasiFinite.Basic`.
No DAG proof dependency or module is pruned: all four old proof dependencies
remain necessary for the unchanged localization node, realized by Mathlib plus
the conversion helper. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier theorem duplicated Mathlib's `Algebra.ZariskisMainProperty.of_finiteType`,
contrary to upstream review #1428.  The existing DAG record already points to
Mathlib's declaration; this repair aligns the module and callers with that record.

The interface change is recorded in `coord/changes/zariskisMainProperty-wrapper-removal.md`.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading; forced caller adaptations are included for review.

## Second reading by K2

1. Compared all four delivered modules with the repository using unified diffs.
   Verdict: only the declared conversion-helper result type changes; all existing
   caller signatures and definitions are byte-for-byte unchanged. The change record
   now contains the exact old and new signatures and all declaration users.
2. Compiled all four modules in import order with lcompile.py: no errors or warnings,
   no sorry, no forbidden declarations, and no hollow definitions. A scratch-copy
   `#print axioms Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime` reports only
   propext, Classical.choice, and Quot.sound. The delivery tool also audits every
   declaration's axioms. Verdict: genuine proofs. There is no new hole closure:
   the baseline was already proved and this is a duplicate-interface repair.
3. No split-off statements or new theorems are added. A new-wording msearch grep
   search found only Mathlib's singleton-fibre theorem and equivalence. A local rg
   search also found a private equivalence in QuasiFiniteOverPolynomialAlgebra,
   which is unavailable to importers. Read the isolated-fibre-point
   definition and Mathlib's QuasiFiniteAt.of_isOpen_singleton_fiber proof. The repaired
   conversion transports exactly the singleton along the canonical fibre
   homeomorphism. It covers arbitrary commutative rings and prime ideals; for the
   zero ring there are no prime inputs. No finiteness or nonemptiness hypothesis
   is added. Verdict: the conversion is true and supplies exactly the required
   instance, without repeating the localization conclusion.
4. Read Mathlib's ZariskisMainProperty.of_finiteType and the principal-localization
   conclusion it defines. The three callers now apply that proved declaration
   after the conversion. Both imports in the helper are needed: QuasiFinite.Basic
   for the public result and ZariskisMainTheorem privately for the proof. Reviewed
   dag/units/sk-thm-p1.json realized fields: this below-unit repair keeps the route.
   Verdict: shortest existing route retained; no module or proof dependency pruned.
5. Read lem-weil-pbc-integral-closure-zariski-main-away.json in full. Its unchanged
   localization statement is realized by the conversion plus Mathlib in the
   callers, not by pretending the conversion alone proves it. Updated only proof,
   proof_origin, and lean.how to identify the helper accurately; proof_deps remain
   the union of the steps' uses. Verdict: node and Lean now agree.

Changed during this reading: made the Zariski-main import private, exposed only
QuasiFinite.Basic for the new signature, added explicit proof imports to the
three necessary caller adaptations, removed a redundant nested by block, repaired
verbatim signatures and user documentation in the change record, corrected the
report's hole accounting, and clarified the existing node's proof realization.

## Forced adaptations

Compiled untouched originals against the sandbox's repaired compiled dependencies.
Sheaf.RingTheory.QuasiFiniteLocalDimension fails with `Unknown identifier ZariskisMainProperty` and
`Unknown identifier zariskisMainProperty_iff.mp`; Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway
fails with `Unknown identifier ZariskisMainProperty`. Both need the explicit plain
Mathlib import and the conversion instance before applying of_finiteType.
Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization fails at its old wrapper call with
`QuasiFiniteAt A p.asIdeal` where the existential bijective-awayMap conclusion is
required. Its new conversion instance followed by of_finiteType restores exactly
that conclusion. All three adapted files compile, and all their signatures stay
unchanged. Only these forced imports and call-site lines are changed.

## Forced adaptations

### Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization
Original against changed dependencies failed:
```
/tmp/forced-adaptation-fq9vqyi2/lean/Sheaf/Paper/IntegralClosureFiniteFibrePartLocalization.lean:128:4: error: Type mismatch
  Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime A B p (hqf p hp)
has type
  Algebra.QuasiFiniteAt A p.asIdeal
but is expected to have type
  ∃ r, ι r ∉ p.asIdeal ∧ Function.Bijective ⇑(Localization.awayMap ι r)

(with the modules compiled into /tmp/forced-adaptation-fq9vqyi2/.lbuild) [6.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway
Original against changed dependencies failed:
```
/tmp/forced-adaptation-6l9x9w1t/lean/Sheaf/RingTheory/QuasiFiniteAtFiniteSubalgebraAway.lean:55:11: error(lean.unknownIdentifier): Unknown identifier `ZariskisMainProperty`
/tmp/forced-adaptation-6l9x9w1t/lean/Sheaf/RingTheory/QuasiFiniteAtFiniteSubalgebraAway.lean:57:9: error: Tactic `rcases` failed: `x✝ : ?m.54` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-6l9x9w1t/.lbuild) [1.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.RingTheory.QuasiFiniteLocalDimension
Original against changed dependencies failed:
```
/tmp/forced-adaptation-k6vqne2r/lean/Sheaf/RingTheory/QuasiFiniteLocalDimension.lean:52:15: error(lean.unknownIdentifier): Unknown identifier `ZariskisMainProperty`
/tmp/forced-adaptation-k6vqne2r/lean/Sheaf/RingTheory/QuasiFiniteLocalDimension.lean:54:30: error(lean.unknownIdentifier): Unknown identifier `zariskisMainProperty_iff.mp`
/tmp/forced-adaptation-k6vqne2r/lean/Sheaf/RingTheory/QuasiFiniteLocalDimension.lean:54:9: error: Tactic `rcases` failed: `x✝ : ?m.54` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-k6vqne2r/.lbuild) [1.5 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
