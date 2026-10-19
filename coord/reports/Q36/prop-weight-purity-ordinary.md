# Stage-1 report: prop-weight-purity-ordinary

## Files written

- `dag/nodes/sec-zeta-weil/prop-weight-purity-ordinary.json`: statement, split; no Mathlib match. Statement unchanged; two proof steps, entirely using existing nodes.
- `citations.json`: verbatim statement excerpts for all three step/node pairs.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

New nodes: 0. New Mathlib leaves: 0. No unit file changed: this item is the ordinary-purity clause, not the unit's key bundled statement.

## Attachments

None. Searched all project files under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for cohomological purity by concept. No exact declaration found. Read `WeilConjectures/ZetaLinearAlgebra/Purity.lean:57-140`: `TraceDatum.isPureOfWeight_map_P_of_pairing` and `TraceDatum.norm_eq_of_mem_roots_charpoly_map_of_pairing` concern an abstract trace datum and assume perfect pairings, similitude and the mixed upper bound. They do not supply the geometric hypotheses-to-cohomology assertion of this item. The affine-curve degree-two purity declarations cover different objects and degrees. No master sorry declaration is treated as a finished proof.

## Literature wanted

None. The original blueprint proof and all statements needed for this one-level split are present. No Stacks theorem or SGA source is invoked; this is a projection of an already existing theorem, not a new proof of smooth purity.

## Findings and corrections

The master source `literature/blueprint/master/blueprint/sec-zeta-weil/sk-input-weights/prop-weight-purity-ordinary.md`, Proof, says to take clause (4) of `thm-weil-deligne-purity`. The current `literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-input-weights/prop-weight-purity-ordinary.md` has exactly the same statement and no proof. The current purity theorem also retains the explicit hypothesis that both displayed cohomology groups are finite-dimensional. The imported one-paragraph proof did not explain how that extra hypothesis follows from the setting of `prop-weight-purity`.

I discharged it with clause (3) of the existing `lem-weil-smooth-proper-purity-hypotheses`, which directly states finite-dimensionality for ordinary AND compact-support cohomology with algebraically closed coefficients. This avoids incorrectly applying the finite-extension coefficient statement of `prop-cohomological-finiteness` directly to the infinite field Qlbar. I retained all of the original item's statement, so no STATEMENT-DISPUTED or new hypothesis is necessary. Added `def-weil-frobenius-module-weights` to statement dependencies, since the item's conclusion uses that predicate; removed proof citations that merely supplied the statement's setting. All imported provenance and flags are retained.

## Searches and reuse

Used `tools/blueprint_refs.py search` for `purity ordinary`, `smooth proper purity`, `pure of weight`, and `ordinary cohomology`; also searched the whole DAG by the purity/cohomology keywords and opened the existing candidate statements. `cor-zl-purity-smooth-proper` is a stronger existing result (all integer degrees and a mixed compact-support conclusion, without the admissibility hypothesis). The imported packaged `thm-weil-deligne-purity` already states the desired clause and is exactly the source's route, so no duplicate was created. `same_as` is []: no other imported node has precisely this standalone proposition and hypotheses.

All six Mathlib searches in `searches.jsonl` were run through the required msearch command and read: two LeanFinder phrasings, one Loogle query, two grep queries, and one LeanSearch query. All services answered successfully. Semantic results concerned finite-field Frobenius or Witt-vector isocrystals; none state cohomological purity. Loogle and the second grep found `AlgebraicGeometry.Scheme.EllAdicCohomology`; read the full `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean`, especially lines 75-85. It defines integral cohomology and the empty-scheme case, with no geometric-Frobenius purity theorem. Queries are copied literally from the log into `mathlib_searches` with no invented search.

## Not duplicates

No new nodes, so there are no new/existing pairs to justify. The existing hypotheses lemma and bundled purity theorem are cited directly.

## Review by Q36

I read the chapter `sec-zeta-weil` and unit `sk-input-weights` before the item, and read the original item's proof together with the current main-20261015 statement. The unit obtains ordinary purity by its existing smooth-proper purity input; selecting clause (4) of the packaged Deligne theorem retains that route. No cross-unit statement tool is introduced. The only cross-unit citation is the definition of Frobenius-module weights, which the route rules allow as a notion.

For Step 1 I opened `lem-weil-smooth-proper-purity-hypotheses` in full. Its hypotheses fix precisely the finite-field datum, unequal primes, algebraically closed coefficient category and smooth proper geometrically connected pure-dimensional X0 in the item's setting. Its third conclusion, quoted in citations.json, gives finite-dimensionality and the global geometric-Frobenius actions for both H^j and H_c^j for every integer j, hence every displayed group of the theorem we will apply. I take only this third conclusion; I do not rely on a definition of a cohomology group as if it were a finiteness theorem.

For Step 2 I compared the full statement of `prop-weight-purity` with `thm-weil-deligne-purity`, including p, a>=1, q=p^a, k0 and its algebraic closure k, ell!=p, Qlbar, the fixed isomorphism iota to C, X0 and its pure dimension d, geometric fiber X, the same constant Weil object on the small pro-etale site and the same global geometric Frobenius. The parent setting explicitly assumes exceptional-adjoint admissibility and a dualizing Weil complex with the canonical functorial Weil structure; these are exactly the corresponding theorem hypotheses. Step 1 supplies its remaining explicit finite-dimensionality hypothesis. Its fourth conclusion is quoted literally in citations.json and gives the ordinary cohomology module, not just compact-support cohomology. I also read `def-weil-frobenius-module-weights`: its eigenvalue norm definition is exactly the weight predicate in that conclusion, with the same q and iota. No Frobenius inversion, coefficient change, or identification with reciprocal polynomial roots is needed.

Checked delivery-errors B1-B10: no new unsplit statements, definitions, leaves or source tags to introduce; existing notions are named; source prose and TeX preserved; blueprint references searched and filled; no alleged attachment on a partial algebraic theorem. C1-C8: every non-elementary input is an existing cited statement; citations use their statements, not proofs; the finiteness gap is explicitly repaired; all uses are exactly the proof-dependency union. Read-only dependency traversal found neither proof input depends on this item, so these edges do not create a cycle through the item. D1-D5: no new node repackages a clause; the source's actual projection is written out after hypothesis verification. E1-E7: verified all hypotheses and coefficient categories above; no altered statement or source error was found.

Small cases: when d=0 the interval contains only i=0, and the same theorem clause applies without any positive-dimensional assumption. If an H^i is zero, the module definition's eigenvalue condition is vacuous, so this proof does not assume existence of an eigenvalue. Both endpoints i=0 and i=2d are included in the theorem's exact interval. The coefficient isomorphism iota remains arbitrary but fixed throughout. There are no new statements needing separate counterexample tests. Both non-elementary steps are shorter than 2000 characters (under 1000), and neither hides an auxiliary comparison or a separate inline lemma.

## Unfinished work

None for this one-level split. Existing cited nodes remain subject to the project's own later work; they are not claimed proved or newly split here. No Lean files were written, no compiler or Lake command was run, and all worker writes were confined to this sandbox.
