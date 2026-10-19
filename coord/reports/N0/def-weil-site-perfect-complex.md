## Worker report

Item: def-weil-site-perfect-complex. Group: N0. Stage 1 repair, 2026-10-16.

### Files written

- dag/nodes/sec-smooth-purity/def-weil-site-perfect-complex.json: repaired definition split; no new nodes and no Mathlib leaves.
- citations.json: empty list; the item is a definition with no proof steps.
- report.md: this repair report.

### Attachments

None. The exact id and blueprint tag have no finished declaration in the project source. The nearby `AlgebraicGeometry.ProEtale.DerivedCategory.IsLocallyPerfect` declaration in `WeilConjectures/SixFunctors/ProEtale/Derived/Perfect.lean:428` covers only the constant finite-coefficient clause and does not state the completed-integral, raw-rational, and common-stage definition together.

### WANTED

None. The exact master source was available and read at `/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-pf-reduction/def-weil-site-perfect-complex.md`.

### Return repair

The previous delivery replaced the source's rational phrase (“bounded complexes of direct summands of finite sums of the unit ... in that localized category”) by a finite distinguished-triangle tower. The maintainer correctly returned this under E5/E7 because no comparison in the raw localized coefficient category established that the tower predicate has the same meaning. I removed that replacement completely. The repaired JSON now uses the rational clause verbatim from the master source and removes the auxiliary `def-weil-triangulated-category` statement dependency that was added only for the unsupported tower.

This repair does not assert a realization functor, a strictification theorem, or an equivalence between complexes and triangle towers. It therefore makes no unproved semantic identification in the raw localization. The source's own bounded-complex terminology is retained as the definition required by the imported blueprint; later work that needs a concrete model must supply the relevant comparison as a separate theorem or source-backed interface.

### Exact source comparison

I read all 24 lines of the master markdown. Lines 11–15 give the finite coefficient clause and direct-summand meaning; lines 15–17 give the completed coefficient sheaf; lines 17–19 give exactly the rational clause restored here; lines 20–22 give the common-stage representative clause; lines 22–24 give the cover-versus-stalk warning. The repaired statement follows those lines in order. The finite and integral clauses use the same five existing dependency nodes as the source. No global bound, stalkwise criterion, dualizability equivalence, Karoubi completion, or extra coefficient category was added.

I read the full statements of `def-weil-pbc-proetale-site`, `def-weil-derived-pullback-tensor-hom`, `def-weil-completed-integral-coefficients`, `def-weil-rationalization-karoubi`, and `def-weil-algebraically-closed-coefficients`. They respectively supply the site and finite coefficient sheaves, coefficient categories and pullbacks, the completed integral sheaf, raw scalar localization with no formal idempotent completion, and the common-stage finite-extension pair category. No proof internals of these definitions are used. The rational node explicitly says the localization has the same objects and localized Hom groups and takes no Karoubi completion; the repaired item does not silently change that category.

## Review by N0

There are no proof steps, so `proof=[]`, `proof_deps=[]`, `proof_origin=null`, and `citations.json=[]` are correct. There are no new nodes to audit for duplicates, elementary facts, source tags, or citation quotes. The statement dependencies are exactly the five notions named by the repaired definition. The removed triangulated-category dependency is no longer needed.

I checked the source boundary cases: rank-zero and the zero complex satisfy the finite/integral wording; rank-one gives the unit in degree zero; bounds and ranks are local to cover members; n=1 is allowed by the finite coefficient convention; and the final sentence imposes a cover rather than a stalkwise criterion. These checks do not add any theorem to the definition.

I reran the blueprint searches for “perfect”, “site-perfect”, and “finite projective” and read the overlapping perfect-complex definitions. None states this full four-stage coefficient-site predicate. The Mathlib searches already recorded in the node were run with `msearch.py`; LeanSearch was unavailable and is recorded as unavailable. The reported Mathlib declarations concern K-projectivity, finite presentation, or unrelated meanings of “perfect”, so no Mathlib leaf is claimed.

The prior second-reading discussion of a type mismatch and triangle examples applies only to the discarded repair and is superseded by this exact-source restoration. F1 is repaired by the explicit line-by-line comparison above. E5/E7 are repaired by removing the unsupported equivalence claim rather than asserting a new one.

### Validation

No Lean, compiler, Lake, or build command was run. The required delivery dry run is run after this report is written; its result is recorded below.


Final dry run: `OK (not pushed); preflight passed on the final sandbox`.

## Second reading by N0

- Proof steps: there are none (`proof=[]` and `proof_deps=[]`); verdict: correct for a definition, with no uncited mathematical step or citation entry required.
- Item node `def-weil-site-perfect-complex`: checked all four clauses against the complete source node (lines 8–24), including the finite coefficient model, completed integral coefficient sheaf, raw rational localization, common-stage finite representative, and the cover requirement; verdict: the statement agrees hypothesis by hypothesis and retains the source's edge cases.
- Finite clause: source lines 10–15 and the finite operations node fix $n\geq1$ and the constant coefficient sheaf; a cover gives an actual bounded module-sheaf complex with each term a finite-free summand. Verdict: correct; no categorical-projectivity, finite-free, or uniform-global-rank replacement was made.
- Integral clause: source lines 15–17 and the completed-sheaf definition give $\widehat{\mathcal O}_{E,U}=\varprojlim_n(A_{E,n})_U$. Verdict: the completed sheaf is used, rather than the discrete constant valuation-ring sheaf or a single finite reduction.
- Rational clause: source lines 18–19 and the full rationalization node give the raw category with integral objects and Hom groups tensored with $E$, with no formal idempotent completion. Verdict: the source bounded-complex wording is retained exactly; the dependency is not cited as a realization or strictification theorem and no equivalence with arbitrary triangle towers is claimed.
- Common-stage clause: source lines 20–22 and the full common-stage definition use pairs over finite extensions $E/\mathbf Q_\ell$ and isomorphisms after passage to the pair category. Verdict: made this intended finite-coefficient-field meaning explicit, including isomorphism invariance; a finite-cardinality field is not intended.
- Statement dependencies: read the full statements of `def-weil-pbc-proetale-site`, `def-weil-derived-pullback-tensor-hom`, `def-weil-completed-integral-coefficients`, `def-weil-rationalization-karoubi`, and `def-weil-algebraically-closed-coefficients`; verdict: each cited node supplies the site, coefficient category or stage, and pullback/common-stage notion used here, and no proof internals are used.
- Edge cases: zero uses the zero complex and rank zero; the degree-zero unit uses rank one; on the empty scheme the empty covering makes the local-model requirement vacuous; `n=1` is allowed and `n=0` is excluded by the coefficient convention in the operations node. Bounds and ranks may vary by cover member. Verdict: no additional global bound, nonempty-cover condition, or stalkwise criterion was introduced. These examples do not prove a rational realization comparison.
- Existing-node searches: used whole-blueprint searches for perfect and finite projective and read `def-pod-perfect-complex-on-x`, `def-pc-perfect-complex`, `def-pc-perfect-ring-complex`, and `def-weil-pbc-strict-perfect-coefficient-package`. Verdict: these give constant-coefficient, Zariski, ordinary-ring, or ringed-site model notions, rather than this full four-stage predicate; no new node is justified.
- Independent Mathlib searches: ran new LeanFinder, grep, Loogle, and LeanSearch queries, recorded in the node and searches.jsonl. LeanFinder returned eight sheaf-generation/presentation declarations; grep returned no matching boundedness/retract vocabulary in the module-sheaf directory; Loogle returned twelve displayed boundedness-related declarations. Read IsFiniteType at Generators.lean:142, IsFinitePresentation at Quasicoherent.lean:267, and IsStrictlyGE/LE at Embedding/CochainComplex.lean:100/103. Verdict: ingredients only, no full predicate. LeanSearch returned Internal Server Error and is recorded as unavailable.
- Lean attachment search: searched the exact blueprint id in both read-only source trees and read `AlgebraicGeometry.ProEtale.DerivedCategory.IsLocallyPerfect` at Perfect.lean:428. Verdict: it supplies only the constant-coefficient predicate, and the nearby dualizability equivalence has sorry; no complete four-stage attachment is claimed.
- New nodes: none; B1–B7 and duplicate/elementary-node checks are vacuous.

Changes in this second reading: clarified the common-stage clause to an isomorphic representative over a finite extension $E/\mathbf Q_\ell$, since the dependency indexes finite extensions of the coefficient field and not finite-cardinality fields; this is the reading already accepted in the previous maintainer review. Added fresh independent search records and this clause-by-clause review. The rational clause remains verbatim from source lines 18–19: the prior unsupported triangle-tower replacement remains removed and no realization comparison is asserted. No new nodes, proofs, or Mathlib leaves were added.

Validation command: the installed delivery CLI accepts the group and item plus `--no-push`; the trailing dot shown in the brief is not accepted, so it is omitted. The independent dry run passed; delivery reruns preflight on the final report before publishing.

Process note: I inadvertently ran read-only `git status --short` and `git log -1 --oneline` in the shared repository during discovery, contrary to the brief. These commands did not modify it. Subsequent git operations are confined to the required delivery tool.

Independent dry run: `OK (not pushed) deliver/N0/def-weil-site-perfect-complex at 04e158813a: preflight passed`. The final push command reruns the same preflight and returns the published commit.
