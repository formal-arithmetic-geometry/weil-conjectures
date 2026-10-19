# Stage 1 report: lem-sf-flat-model

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-flat-model.json`: item split into three declaration-backed steps.
- `dag/nodes/sec-smooth-purity/lem-sf-proetale-flat-model.json`: statement, closed Mathlib-search verdict (no match).
- `dag/nodes/sec-smooth-purity/lem-sf-etale-flat-model.json`: statement, closed Mathlib-search verdict (no match).
- `dag/nodes/sec-smooth-purity/lem-sf-etale-flat-constructible.json`: statement, closed Mathlib-search verdict (no match).
- `citations.json`: verbatim quotes for all step citations.

## Attachments

- `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_iff_exists_flatModel` belongs to `lem-sf-proetale-flat-model` (FlatModel.lean:56).
- `AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatModel` belongs to `lem-sf-etale-flat-model` (FlatModel.lean:91).
- `AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatConstructibleModel` belongs to `lem-sf-etale-flat-constructible` (FlatModel.lean:160).

## WANTED:

None.

## Not duplicates

- `lem-sf-proetale-flat-model` vs existing DAG: no node states the pro-etale `torAmplitudeIn_iff_exists_flatModel` declaration.
- `lem-sf-etale-flat-model` vs existing DAG: no node states the etale `hasTorAmplitudeIn_iff_exists_flatModel` declaration.
- `lem-sf-etale-flat-constructible` vs existing DAG: no node states the etale constructible-model declaration.

## Review by NI

I read the imported item and its blueprint section, then read both source files `SixFunctors/ProEtale/Derived/FlatModel.lean` and `SixFunctors/Etale/Derived/Finiteness/FlatModel.lean`. The pro-etale source theorem has the exact bounded-flat-model equivalence used in step 1; its hypotheses are a scheme, derived object, bounded-constructibility proof, and integers with the required order. The etale source theorem has the corresponding equivalence used in step 2. The constructible theorem in the etale file adds the finite coefficient-ring and Noetherian scheme hypotheses and gives flat constructible terms, exactly the extra hypotheses and conclusion in step 3. I checked each new node's declaration name, module, line range, and `sorry: false` status in the source. I ran LeanFinder, Loogle, and Mathlib grep searches for the item and each new declaration; all returned no Mathlib theorem, so the nodes are declaration attachments rather than Mathlib leaves. I corrected the imported proof from an unsupported long agent argument to three explicit steps whose cited nodes state the complete facts, and added verbatim citation quotes.

## What was wrong or changed

The imported proof attempted to reprove substantial resolution and flatness results while omitting their dependencies. The source already contains sorry-free declarations for all three clauses. I therefore split by those declarations and preserved the item statement without changing its hypotheses.

## What remains

Nothing; the sandbox is ready for dry run.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against the blueprint node and the pro-etale and etale `FlatModel.lean` declarations; all hypotheses (scheme, coefficient ring, invertibility context, bounded constructibility, interval, and constructible variant) are retained.
- Step 1: checked against `torAmplitudeIn_iff_exists_flatModel` (FlatModel.lean:56–70); the cited node supplies the exact bounded flat-complex equivalence, so no unsupported resolution argument remains.
- Step 2: checked against `hasTorAmplitudeIn_iff_exists_flatModel` (FlatModel.lean:91–107); the cited node supplies the exact small-etale equivalence and interval condition.
- Step 3: checked against `hasTorAmplitudeIn_iff_exists_flatConstructibleModel` (FlatModel.lean:160–209); the cited node supplies the finite-ring, Noetherian, bounded-constructible hypotheses and the termwise flat-constructible model.
- `lem-sf-proetale-flat-model`: checked as a statement-only attachment with a self-contained scheme, ring, interval, and bounded-constructibility context; its wording agrees with lines 56–70. Searches for existing DAG/Mathlib declarations found none; the closed slopmaster2 declaration is recorded.
- `lem-sf-etale-flat-model`: checked as a statement-only attachment against lines 91–107, including the coefficient ring and bounded-constructibility hypotheses; no duplicate DAG or Mathlib declaration was found.
- `lem-sf-etale-flat-constructible`: checked as a statement-only attachment against lines 160–209, including finite commutative ring and Noetherian scheme hypotheses; no duplicate DAG or Mathlib declaration was found.

I removed proof-sketch prose (“This uses …” and the Stacks generation discussion) from all three new statement nodes, because unsplit nodes must carry statements only. I made each statement self-contained and updated `citations.json` to quote the repaired statements verbatim. Small cases (zero complex, a field coefficient ring, empty scheme, and intervals with a = b) satisfy the stated equivalences; no statement dispute was found.


## Repair of returned delivery

I repaired every reviewer point. Both étale attachment statements now introduce integers a and b together with the explicit hypothesis `hab : a ≤ b`, matching the theorem binders at FlatModel.lean lines 91 and 160. The constructible attachment now cites the exact Lean source file and theorem lines rather than the blueprint. I removed the pro-étale site and inverse-image-flat nodes from the étale statement dependencies because those nodes do not define the étale notions used by these statements. Each newly created node now has complete creation metadata including `group: NI`. I re-read the corresponding Lean declarations and verified that the citation quotes still match the repaired statements; no other item proof or citation required changes.

## Second reading by NI

- Item statement: checked against blueprint `lem-sf-flat-model` and the three source declarations in `ProEtale/Derived/FlatModel.lean` (56–70) and `Etale/Derived/Finiteness/FlatModel.lean` (91–107, 160–209); the global datum, invertibility context, bounded constructibility, interval, and constructible variant clauses are all retained.
- Step 1: checked against the statement of `lem-sf-proetale-flat-model`; its scheme, coefficient ring, integers with `a ≤ b`, bounded-constructibility hypothesis, flat complex, support interval, and derived isomorphism match the pro-etale theorem. No elementary step is claimed.
- Step 2: checked against `lem-sf-etale-flat-model`; the explicit `a ≤ b` hypothesis and bounded constructible small-etale object match the theorem, and the cited statement supplies exactly the flat bounded complex and isomorphism. No elementary step is claimed.
- Step 3: checked against `lem-sf-etale-flat-constructible`; finiteness of `Λ`, Noetherianity of `X`, bounded constructibility, interval, termwise flat constructibility, and derived isomorphism match the constructible theorem. No elementary step is claimed.
- `lem-sf-proetale-flat-model`: statement-only attachment checked for self-contained `A`, scheme, interval, bounded constructibility, site, flatness, and Tor-amplitude notions; source lines 56–70 and closed declaration agree. Existing-node and Mathlib searches were checked in `searches.jsonl`; no duplicate was found.
- `lem-sf-etale-flat-model`: statement-only attachment checked against source lines 91–107, including `hab : a ≤ b` and the small-etale site; no duplicate DAG node or Mathlib declaration was found.
- `lem-sf-etale-flat-constructible`: statement-only attachment checked against source lines 160–209, including finite coefficient ring and Noetherian scheme hypotheses; no duplicate DAG node or Mathlib declaration was found.

I changed nothing in this second reading: the earlier repairs already removed proof prose from unsplit nodes, supplied the interval hypotheses, removed irrelevant statement dependencies, and synchronized citation quotes with the node statements. I retained the three closed declaration attachments and the three explicit item proof steps.
