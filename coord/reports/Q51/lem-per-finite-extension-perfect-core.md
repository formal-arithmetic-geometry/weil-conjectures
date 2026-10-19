# Stage 1 report: lem-per-finite-extension-perfect-core

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-extension-perfect-core.json`: split statement.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-extension-separable-core-bounded-exponent.json`: statement-only Mathlib leaf (`IsPurelyInseparable.hasExponent_of_finiteDimensional` and `IsPurelyInseparable.HasExponent.has_exponent`).
- `dag/nodes/sec-deligne-laumon-a1/lem-per-separable-closure-perfect-core.json`: statement-only supporting lemma; Mathlib searches found no exact match.
- `citations.json`: verbatim statement citations for every proof-step dependency.

## Attachments

None. I searched the read-only project source trees for the item tag and its mathematical names; no sorry-free project declaration states this item.

## WANTED

None.

## Source error and repair

The sandbox contained an earlier split with malformed JSON in the supporting node, stale Q134 metadata, and a local pure-inseparable node that was absent from the shared DAG. I repaired the JSON, corrected the supporting-node metadata to Q51 (the item retains its original Q134 creation provenance), reused the existing Mathlib-backed `lem-weil-pbc-separable-first-purely-inseparable` node, and made the only new Mathlib leaf the genuinely missing bounded-exponent assertion. The item statement and its finite-dimensional hypothesis agree with ILO Exposé IV §3.2.3(ii). The proof uses a uniform exponent because an exponent depending on the chosen root would not preserve the original element under Frobenius.

## Review by Q51

I read the item’s source, ILO Exposé IV Lemma 3.2.2 and Proposition 3.2.3(ii) on printed page 56, the `sk-p-dl-a1-perverse` unit and its chapter, and every cited DAG statement. Step 1 introduces the relative separable closure S using `def-weil-pbc-relative-separable-closure`, proves elementwise algebraicity from finite-dimensionality by linear dependence of powers, and uses `lem-weil-pbc-separable-first-purely-inseparable` for the separable-algebraic core and purely inseparable tail. Its hypotheses are exactly an algebraic field extension and characteristic p; finite-dimensionality supplies algebraicity.

Step 2 uses the new bounded-exponent Mathlib leaf together with the existing purely-inseparable-tail statement. A finite K-spanning set of L is also an S-spanning set, so the finite-dimensional hypothesis needed for L/S holds without a tower-degree theorem. The existing Mathlib leaf `lem-weil-pbc-separable-extension-embeds-separably-closed` supplies the K-embedding of S into K^sep from separable algebraicity and the separably closed target. For x in the perfect core, roots at exponent n+e give z_n in S with z_n^(p^n)=x; transporting these roots proves the image of x lies in every p-power image in K^sep. I checked the exponent calculation and the edge cases L=K, a finite separable extension, and a finite purely inseparable extension.

Step 3 applies the statement-only node realizing ILO Lemma 3.2.2. That node says exactly that the intersection of all p-power images in K^sep is the subfield separable algebraic over K_perf; the separable-closure and relative-closure definitions supply the ambient objects. The resulting separable algebraicity gives the required nonzero polynomial over K_perf, and the embedding fixes K_perf so the polynomial pulls back to x.

The new exponent node was checked against Mathlib/FieldTheory/PurelyInseparable/Exponent.lean line 215 and the following `HasExponent.has_exponent` theorem. The supporting node was checked against the displayed minimal-polynomial proof in ILO Lemma 3.2.2. Mathlib searches were run for the item and both new nodes with LeanFinder, Loogle, grep, and LeanSearch; the item’s retained unavailable Loogle result is recorded as unavailable; the supporting nodes now record the successful reruns described below. I also searched the whole DAG and blueprint: the existing separable-first node is a stronger reusable Mathlib leaf, while neither new statement is duplicated.

## Not duplicates

- `lem-per-finite-extension-separable-core-bounded-exponent` vs `lem-weil-pbc-separable-first-purely-inseparable`: the existing node gives only elementwise purely inseparable membership for an arbitrary algebraic extension; the new node gives a single uniform exponent under finite-dimensionality.
- `lem-per-separable-closure-perfect-core` vs `lem-weil-pbc-separable-first-purely-inseparable`: the existing node concerns a relative separable closure inside an arbitrary algebraic extension; the new node identifies the perfect-core intersection inside a separable closure with the separable closure of the base perfect core.

## Continuation review and repaired dry-run diagnostics

The required first dry run exited with SEARCH CHECK FAILED and pushed nothing. Its diagnostics showed that the earlier supporting-node search records had no matching entries in the retained log. I ran the missing queries using the prescribed msearch.py command, read the returned declarations, and replaced their results with the actual hit lists and log digests. The bounded-exponent search finds the exact finite-dimensional instance; `HasExponent.has_exponent` is the structure field at line 55, not a later theorem. The separable-core searches find only relative perfect closures (the union of purely inseparable elements), which are different from intersections of all Frobenius images; a second semantic phrasing also found no matching theorem. Existing successful item searches and their log entries were reused. The extra identical grep and LeanSearch calls in the continuation log were redundant readings, not extra claims of mathematical progress.

I re-read delivery-errors B–E against all three files. The new nodes introduce their fields, characteristic, finite-dimensional and purely inseparable hypotheses, or define their intersection and relative subfield explicitly; both remain statement-only. I corrected a missing closing math delimiter in the exponent statement and normalized doubled TeX escapes in all three sandbox nodes. The item’s mathematical statement is unchanged. Its original creation metadata is restored from the current repository. The source read again was ILO IV Lemma 3.2.2 (printed pp. 55–56) and Proposition 3.2.3(ii) (p. 56), including its reduction to the bounded radicial case; this is the parent’s prescribed Epp input, not a new chapter route.

For C1/C4, step 1 uses exactly the relative-separable-closure definition and the existing separable-first theorem. The latter gives both separable algebraicity of S/K and pure inseparability of L/S. Step 2 uses the exponent leaf only after explicitly proving finite-dimensionality over S using the original spanning set. I repaired the previously implicit embedding assertion by adding the existing embedding leaf: its statement gives the required injective K-algebra homomorphism into any separably closed extension, and the separable-closure definition gives that target hypothesis. The equalities sigma(z_n)^(p^n)=sigma(x) are written out. Step 3 uses only the new ILO equality: it yields a nonzero polynomial over K_perf, and the displayed coefficient calculation plus injectivity pulls that relation back to L. No definition node is cited in place of the embedding theorem. citations.json was regenerated from the exact current statements, one entry per step/node pair.

I tested the uniform-exponent node on E=F and on F_p(t^(1/p^r))/F_p(t), where e=r works; finiteness excludes the unbounded perfect-closure tower. For the equality node, perfect K gives all of K^sep on both sides, and K=F_p(t) gives the algebraic constant field on both sides; 0 and the n=0 intersection impose no hidden exclusions. For the item, L=K, finite fields, finite separable extensions and purely inseparable finite extensions are all covered. No non-elementary step exceeds 2000 characters. No node is a restated clause of the item: one is a general exponent bound; the other is an equality in a separable closure, without a finite-extension conclusion. Searches for both statements in the whole DAG and blueprint found no replacement beyond the reused separable-first and embedding nodes. The existing off-unit uses are Mathlib leaves or a finished definition; the original tool-use explanation is retained.

The second dry run passed the search gate and reported missing inline definition citations in the new equality statement and null elementary fields. I added its three definition citations and fixed the fields to false; the null values were introduced by my TeX-normalization traversal failing to return scalar booleans. I also closed the final math delimiter. These are presentation/schema repairs; no hypotheses or mathematical assertions changed.
