## What changed

Verified `Sheaf.Paper.CartierEquality.cartier_equality` (global declaration
`cartier_equality`) against its node and Stacks Tag 07E1
(https://stacks.math.columbia.edu/tag/07E1). The checked-out module already has the
correct `(⊤ : IntermediateField k K).FG` hypothesis and a complete proof.
The assigned item is still listed in `coord/repairs.txt` for the old, overly
restrictive `Algebra.FiniteType k K` hypothesis. No signature change is needed.

Simplified the kernel dimension calculation using Mathlib's
`LinearMap.finrank_range_add_finrank_ker`, with its proof-only import
`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`. Discarded the unused embedding,
injectivity, fraction-representation, and fraction-map equation witnesses when
unpacking the complete-intersection model. The domain witness remains necessary
for the cotangent-model theorem. Updated the existing node's third proof step
to name the rank-nullity theorem actually used; its dependency list and route
are unchanged. All existing signatures and public imports are unchanged.

The finite transcendence basis and complete-intersection coordinate model remain
the route of the proof. Rank-nullity and the quotient dimension formula give the
natural-number dimension identity; casting gives the cardinal formula. For the
finite extension clause, transcendence degree zero gives the required equality.

## Proved and sorry left

`cartier_equality` is proved from the recorded model declarations, and the revised
module compiles. The baseline module already contains zero direct holes: holes
closed by this delivery are zero, and holes added are zero. No `sorry` remains in
the item's module; no new module or holed theorem is added. This is validation
and proof simplification of an already repaired queued item, not a new proof or
a decomposition. Any transitive holes of the existing model dependencies are
unchanged and are not claimed closed.

## No longer needed

No imports, DAG nodes, or modules are pruned. Both complete-intersection model
theorems are used, as are the finite transcendence-basis result and the dimension
and transcendence-degree notions. No unit-level statement or proof step is
bypassed. The explicit quotient-kernel equivalence calculation is replaced by
Mathlib's rank-nullity theorem; its ambient modules remain necessary.

## Where the brief, the DAG or earlier work was wrong

The brief says the module still contains `sorry`; the actual source has none,
and compiles before editing. The queue marks it as a repair of the earlier
`Algebra.FiniteType`-on-a-field hypothesis, but the checked-out hypothesis is
already the required field-generation hypothesis. This stale repair should be
closed without counting new holes proved.

The local `literature/stacks-project/more-algebra.tex` and unit `_section.md`
files are absent, so the source statement and proof were checked at the official
Stacks Tag 07E1 page; the unit route was read from `dag/units/sk-thm-p1.json`.
No disagreement in the current statement or mathematical route was found.

Real shorter-route searches were run with `msearch.py`: Lean Finder on the
Cartier dimension formula, Loogle on `Algebra.H1Cotangent, Module.finrank`, and
grep on `cartier|trdeg.*H1Cotangent|H1Cotangent.*trdeg`. Finder returned smooth
Kähler-rank theorems, which require smoothness and do not give this general
formula; Loogle and Mathlib grep returned no match. Repository grep found only
this theorem and its existing application. The search log is `searches.jsonl`
in the sandbox. No new declarations require duplicate checking or new nodes.

## Second reading by U1

1. Interface: PASS. Compared the sole delivered Lean module with the repository
   version using `diff -u`. The existing declaration signature and docstring are
   byte-for-byte unchanged; there are no new declarations or definitions. All
   public imports are unchanged. The only added import is proof-only.
2. Proof: PASS. Independently compiled the delivered file with `lcompile.py`
   (exit 0, no warnings). Compiled a scratch copy with
   `#print axioms cartier_equality`: exactly `propext`, `Classical.choice`, and
   `Quot.sound`, with no `sorryAx`. Scanned the delivered Lean source: no `sorry`
   or prohibited declaration mechanisms. Checked the model interfaces, transport
   of module finiteness, rank-nullity, the quotient dimension identity, the
   natural-number cancellation using `c ≤ n`, and the cardinal casts. The
   domain witness is retained for instance synthesis. Finite-dimensionality of
   the extension supplies zero transcendence degree in the final clause.
3. Split statements: PASS (none). No new statements, modules, nodes, or holes.
   The formula also handles the trivial extension and a transcendental
   extension: zero transcendence degree gives equal dimensions, and a positive
   transcendence degree contributes additively without truncated subtraction.
   No arbitrary data is defined by choosing an unproved existence witness.
4. Route and pruning: PASS. Read the two model modules and the unit's `realized`
   record. The finite transcendence basis and complete-intersection route are
   preserved, and no unit step is bypassed. Independently read Mathlib's
   `finrank_range_add_finrank_ker`: it packages exactly the old two-line
   calculation. Searched the repository for Cartier and the transcendence-degree/
   H1 formula, and Mathlib's field/cotangent sources for Cartier and H1 results;
   found no shorter general formula. All imports support the statement or proof;
   no old proof dependency is removed, so `No longer needed` is complete.
   Checked the source statement and displayed complex against
   [Stacks Tag 07E1](https://stacks.math.columbia.edu/tag/07E1).
5. DAG: PASS. The sole node diff changes only proof step 3 to name the actual
   Mathlib rank-nullity lemma. `proof_deps` remains the union of the steps' uses;
   the source-based `proof_origin` still describes this argument. The node's
   recorded Lean statement matches the unchanged declaration. No new-node
   requirements apply.

Second-reader changes: added this review and the independent axiom-check result
below; no Lean or node repairs were needed. The existing theorem is fully free
of `sorryAx` in the compiled library. This delivery closes zero baseline holes
and adds zero holes; it validates and simplifies the already repaired theorem.
