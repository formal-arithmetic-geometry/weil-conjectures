# Q119 — def-nagata-rees-algebra

## Files written

- `dag/nodes/sec-nagata-compactification/def-nagata-rees-algebra.json`: definition; exact Mathlib leaf `reesAlgebra` at `Mathlib/RingTheory/ReesAlgebra.lean:39`, with `mem_reesAlgebra_iff` at line 64.
- `citations.json`: empty list, since this definition leaf has no proof steps or cited DAG nodes.
- `report.md`: this report. The required search command wrote `searches.jsonl`.

No new nodes; one Mathlib leaf (the item).

## Attachments

None. I searched the live `lean/WeilConjectures/` tree by the exact blueprint tag, by `reesAlgebra`, and by “Rees algebra”. Its declarations use Mathlib's object; `reesGrading`, `reesMonomial`, `reesPresentation`, and the sheaf Rees object concern other notions and do not replace this exact definition. The item's existing `lean` entry is already Mathlib's declaration, which the brief explicitly requires delivering as a leaf rather than ATTACH.

## Wanted sources

None.

## Errors and corrections

No statement error or route change. The first dry run rejected the empty statement-dependency list. I repaired that omission by citing the existing Mathlib leaf `def-weil-polynomial-ring`, whose complete statement I read: it defines precisely the finite-support polynomial ring, its coefficients, and multiplication. This is the ambient A[t] used in the item; it creates no new notion or proof obligation. The main-20261015 copy moved this definition from `sk-def-nagata-sketch-data` to `sk-def-nagata-admissible` (order 22), without changing its statement. I read both copies and the unit/chapter records; I retained imported chapter/unit metadata and the original source field, and identified the current place in `split_report.blueprint`. The former `mathlib_match: null` and `status: unsplit` did not express the exact existing definition; those fields now record the verified leaf. The historical search is preserved and five actual new invocations are appended. One file-scoped grep printed malformed file/line labels; I reran it against the RingTheory directory and read the actual numbered source. Both invocations remain honestly recorded.

## Unfinished work

None for this item. There is no proof to split further and no new lemma to queue.

## Not duplicates

No new nodes. A whole-DAG declaration/title search and `tools/blueprint_refs.py search 'Rees algebra'` found this item as the ordinary Rees-algebra definition. The other blueprint hits define the pieces, the sheaf algebra, or a base-change map, or state grading/localization/base-change properties. None is another definition of this same object, so `same_as` is empty.

## Review by Q119

I read the full current main-20261015 source `sk-def-nagata-admissible/def-nagata-rees-algebra.md`, the original master source (including its explicit Mathlib implementation note), the current admissible-blow-up unit, and the recorded chapter and unit. The definition asks for the ordinary Rees subring of polynomials, not a new graded-ring construction. Its displayed direct sum denotes the finite sums of monomials with coefficients in the corresponding ideal powers. A polynomial has precisely finitely many nonzero coefficients, so this is exactly the coefficient-defined carrier; the separate `prop-nagata-rees-graded` concerns installing the grading.

I read Mathlib `RingTheory/ReesAlgebra.lean` lines 33–77, rather than relying on search snippets. At lines 39–40 `reesAlgebra I` has carrier `∀ i, f.coeff i ∈ I ^ i`. Lines 41–62 supply multiplication, addition, zero, one, and the base-algebra map, and lines 64–65 make the same carrier criterion a theorem by `Iff.rfl`. The only relevant hypotheses are `CommRing A` and `I : Ideal A`, matching the commutative-algebra/scheme context of the blueprint. The unused ambient module variables on line 33 do not occur in either declaration. No Noetherian, finite-generation, domain, nonzero-ideal, or nontrivial-ring hypothesis is required. The direct-sum and underlying-ring clauses therefore match the definition literally, without a comparison theorem between different constructions. No statement was weakened or changed.

I checked small cases directly against the carrier: for I=0, all positive coefficients vanish and the algebra is A in degree zero; for I=A, every polynomial belongs; in degree zero I^0=A, so all constants belong even when I is proper. The zero ring, zero divisors, and nilpotent ideals present no exception, since the carrier and multiplication proof use only ideal powers and the coefficient convolution. This also checks the empty/zero polynomial and finite-support interpretation.

For delivery-errors B1–B10, no new node or notion is introduced, the exact declarations and source lines are named, the old fields/import flags are retained, and every appended search was actually run with msearch.py. LeanFinder, LeanSearch, and Loogle all returned the exact coefficient criterion, and the directory grep located its declaration. For C1–C8, there are no proof steps or DAG citations: `citations.json` is therefore empty, no cited statement is being used beyond its content, no off-unit tool is needed, and the only added dependency is the existing polynomial-ring definition, whose statement gives the ambient ring and coefficients used here; it introduces no cycle. For D1–D5 the result is a verified Mathlib leaf, not a relabelled proof or a moved clause. For E1–E7 the binders and carrier have been checked as above; no scheme-level hypotheses, transports, omitted argument, or disputed source claim is used. There are no proof steps over 2000 characters. I wrote no Lean and invoked no compiler, Lake, build, or local DAG validation script.

The repaired statement-dependency audit cites `def-weil-polynomial-ring` for A[t], finite support, coefficients, and convolution multiplication. Its Mathlib status permits this notion independently of the unit route. This is a statement dependency, not a proof-step citation, so the required per-step quote list remains empty.
