# Maintenance: reuse the five prior obstruction reports

Item: lem-sfb-profinite-field-scalar-annihilator-hull. Maintenance NA,
2026-10-26. This repairs the retry handoff; it does not certify a proof or a
counterexample to the item's statement. Continue dispatching the item.

The previous five workers all reached the same obstruction. Their sandboxes
were archived on ABANDON, so an empty active sandbox does not mean that no
prior work exists. Read these read-only archives, newest first:

- /home/ubuntu/weil-launcher-all/abandoned/NA/lem-sfb-profinite-field-scalar-annihilator-hull.1792941523/
- /home/ubuntu/weil-launcher-all/abandoned/NA/lem-sfb-profinite-field-scalar-annihilator-hull.1792937902/
- /home/ubuntu/weil-launcher-all/abandoned/NA/lem-sfb-profinite-field-scalar-annihilator-hull.1792936198/
- /home/ubuntu/weil-launcher-all/abandoned/NA/lem-sfb-profinite-field-scalar-annihilator-hull.1792933203/
- /home/ubuntu/weil-launcher-all/abandoned/NA/lem-sfb-profinite-field-scalar-annihilator-hull.1792929742/

Each has report.md and searches.jsonl (five genuine searches per attempt).
These paths are explicitly authorized read-only evidence for this item.
Preserved server copies are under
`tools/maintenance/20261026-NA-annihilator-handoff/evidence/`; the local
workspace also has exact copies and their SHA-256 manifest. Compare the live
statement before copying any archived node; reuse reports and searches with
their original provenance, without overwriting current work. Full search hits
remain in the corresponding run/NA/<item>.<time>/log.txt.

## Established obstruction, not a refutation of the theorem

Take P = beta(N_{>=1}), E = Q_ell, a(n) = ell^n with its continuous extension.
Let U_k be the clopen closure of {n >= k}, and M_k = 1_{U_k} R_E with inclusion
transitions. On every profinite test Q -> P, lim M_k(Q) = K_a(Q). Each M_k is
a retract of R_E. Nevertheless 1-shift on the product is not an epimorphism.
For y_k = ell^{-k} 1_{ {k} }, a solution x_k - x_{k+1} = y_k would force
x_k(n) = ell^{-n} for all n >= k. This is unbounded, whereas continuous
E-valued functions on a compact profinite space have bounded image. The same
argument works after every jointly surjective finite profinite cover. Thus
the two-term product complex has extra H^1 and is not K_a[0]. Product
exactness alone does not remove it; the class has no assumed truncation
closure.

`lem-sfb-relative-finite-bundle-roos` provides exact products here, but its
additional Roos surjectivity requires finite locally constant underlying
bundles. The E-valued M_k do not satisfy that hypothesis. Integral reductions
O_E/pi^n are not nonzero E-modules; one cannot place their tower in J.
Rationalizing an integral product also cannot be interchanged with product:
(prod O_E)[1/pi] -> prod E misses (pi^{-n})_n.

HRS Example 4.2 and Remark 6.4 explain the nonzero boundary sheaf kernel with
zero terminal sections, not the requested hull-generation assertion. Theorem
6.12(2) concerns the global-section ring's annihilator ideal. Do not replace
the actual sheaf kernel by extension of its global kernel. The parent
`lem-sfb-profinite-constant-model-relation-hull`, step 5, uses this item;
citing the parent to prove this item is circular. The earlier parent repair
note's non-clopen recollement/rank-induction suggestion was not an established
replacement: the reviewed parent report explains why it did not use that
shortcut.

## What the next worker must resolve

The live item is still unsplit, with proof = [] and proof_deps = []; its exact
generation reference is WANTED. No false statement has been established, so
no statement_change is justified by the Roos obstruction alone. Preserve the
statement, coefficient category and closure conditions. The next meaningful
step is a construction or a precisely applicable source that removes the
extra cohomology, or a different justified generation argument. State which
new step addresses this known obstruction before repeating the clopen-tower
approach. A renamed copy of the desired hull membership is not a split.
If an actual statement counterexample is found, use statement_change and
audit the sole direct citer (the parent above); do not silently add kernel or
truncation closure to J. This maintenance note does not claim such a source,
construction or refutation has been supplied.
