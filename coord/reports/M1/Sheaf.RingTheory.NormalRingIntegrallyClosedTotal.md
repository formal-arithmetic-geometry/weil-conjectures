## What changed

Proved `integral_totalFraction_mem_range_of_normal` in
`Sheaf.RingTheory.NormalRingIntegrallyClosedTotal` without changing its signature.
Added the proof-only import `Mathlib.RingTheory.LocalProperties.Basic`.
Represent x as a/s; map it into the fraction field of each maximal localization;
local normality implies that a belongs to the localized principal ideal (s).
`Ideal.mem_of_localization_maximal` gives global divisibility, which identifies
x with the image of its quotient. Updated the node proof and proof dependencies.
The unit sk-thm-p1 route is preserved: this node is below its realized steps.

## Proved and sorry left

Closed 1 hole: `integral_totalFraction_mem_range_of_normal`
(node `lem-weil-pbc-normal-ring-integrally-closed-total`).
Added 0 holes; no sorry remains in the delivered module. No new declarations.
The local compile is clean; the delivery dry run checks axioms as well.

## No longer needed

No existing imports removed: both public imports are needed by the unchanged statement.
The direct proof dependency `lem-weil-pbc-proper-ideal-contained-in-maximal`
is removed. Its separate maximal-ideal contradiction is replaced by Mathlib's
`Ideal.mem_of_localization_maximal`. This node is a Mathlib leaf, with no Sheaf
module to remove. No other planned dependency is pruned. No conductor helper module
or node is delivered.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The existing theorem docstring records the
original valid conductor-ideal plan; the delivered node records the shorter actual
proof through membership in the principal denominator ideal. Mathlib's theorem
`IsIntegrallyClosed.of_localization_maximal` alone does not apply, since R need
not be a domain; the local ideal membership criterion does apply to arbitrary
commutative rings. The proof needs no nontriviality assumption on R and therefore
also covers the zero ring.

## Second reading by M1

1. Compared the sole delivered module and node with the repository using diff.
   The existing declaration signature and docstrings are byte for byte unchanged;
   only its proof and a plain proof-only import change. No definitions, public
   imports, statement changes, or change records are added. Verdict: pass.
2. Independently compiled the module locally with lcompile.py: clean, no warnings.
   Inspected the entire proof and scanned for forbidden declarations and sorry:
   none occur. A scratch copy with `#print axioms
   integral_totalFraction_mem_range_of_normal` reports only `propext`,
   `Classical.choice`, and `Quot.sound`. All witnesses come from proved Mathlib
   results. Verdict: pass.
3. There are no new or split-off statements and no remaining holes. Reviewed the
   zero-ring case (the local membership criterion is vacuous and still proves
   membership), domains, and rings with zero divisors such as products of fields:
   the proof only assumes domains for the prime localizations, never for R.
   Verdict: pass; no decomposition or restatement of the item.
4. Searched Mathlib independently with grep and Lean Finder, and searched both
   library roots with rg. Read LocalProperties/IntegrallyClosed.lean and the exact
   Ideal.mem_of_localization_maximal statement: the former's local-to-global
   integral-closedness results require IsDomain R and cannot replace this proof.
   The numerator's local membership in (s) is a direct valid route, with no
   unnecessary helper. Both public imports support the unchanged statement;
   LocalProperties.Basic is used only in the proof and imported privately.
   The report accounts for the only removed old proof dependency, the maximal
   ideal existence leaf. Read sk-thm-p1's realized record: this node is below its
   realized steps, so the unit route is retained. Verdict: pass.
5. Checked the delivered node's three proof steps against the Lean construction,
   integrality transport, local denominator identity, and global divisibility.
   Its proof_deps is exactly the union of its step uses, and proof_origin records
   the actual Mathlib-assisted route. Other node fields are unchanged; no new
   nodes need validation. Verdict: pass.

Second reading changed only this report, adding the independent checks above.
The Lean proof and node record required no repair.
