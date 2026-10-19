## Files written

- `dag/nodes/sec-smooth-purity/cor-pur-affine-space-purity.json`: corrected statement node and two-step split; no new nodes and no Mathlib leaves.
- `citations.json`: eight verbatim statement quotations, one for each citation in each step.
- `report.md`: replacement repair report and signed self-review. `repair.py` is a sandbox-only editing aid, not a delivery file.

## Attachments

None. I searched the read-only `WeilConjectures/` source for the blueprint id and affine-space purity declarations and read `WeilConjectures/EtaleCohomology/Purity/Smooth/AffineSpace.lean:356–398`. `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpace` proves existence of an object isomorphism, and its docstring expressly says that the ordered comparisons are not constructed. It therefore does not prove that this item's specified comparison is invertible. Reversing an isomorphism would be elementary; the missing specified-map assertion is the actual obstruction to attachment.

## WANTED

None.

## What was wrong in the node, blueprint, or brief

The returned split applied `thm-pur-affine-line-purity` without checking the coefficient hypothesis carried by its affine-line datum. The comparison definition now permits every finite coefficient index, but that does not enlarge the theorem asserting its isomorphy. I repaired this by the return's option (a), restoring the blueprint's standing hypothesis explicitly, rather than asserting an unproved reduction to all indices.

The previously repaired dimension issue remains repaired: `prop-pur-affine-space-composition-law` assumes both blocks positive, so the split treats dimensions zero and one separately and uses the formula only for dimension at least two. The input to the induction over the changed base remains justified by `thm-sf-preservation-class` (2).

## What could not be finished

The corrected item is fully split. Three other nodes currently use it without the restored hypothesis; their uses need maintenance as detailed below. I have not edited their files or claimed that their mathematical conclusions are false.

## Statement corrected

STATEMENT-DISPUTED: the imported unqualified coefficient range omits the standing assumption of the named affine-line theorem. In both snapshots the affine-line datum says that the hypothesis `e(E/Q_l) | n` is “assumed from now on”: master `sec-smooth-purity/sk-def-purity-conv/def-pur-affine-line-datum.md:28` and main-20261015 `sec-six-functors-basics/sk-def-purity-conv/def-pur-affine-line-datum.md:28`. The current DAG datum states it explicitly, the affine-line theorem introduces its base as the scheme of that datum, and Step 1 of its proof takes `r=n/e`.

The explicit failing type/domain check is `e=2, n=3`: the required `N=n/e=3/2` is not an integer. Thus neither affine-line-purity invocation in the returned proof was justified at that level. This is not a counterexample to purity for an independently defined all-level map. A general comparison definition supplies a map, not the missing theorem about that map.

The old statement began with the purity conventions and `A=A_{E,n}` and asserted isomorphy for every `d>=0` and finite-Tor `K`. The corrected statement fixes `Lambda=A=A_{E,n}`, `n>=1`, and explicitly assumes `e(E/Q_l) | n` as in `def-pur-affine-line-datum`; it also spells out the separated finite-type base already imposed by the comparison definition. The conclusion is the isomorphy of the same specified comparison, for every `d>=0`. I added the datum to `stmt_deps` and removed two unused direct notion references. This implements exactly repair (a) authorized by the return; it neither changes a target nor claims an all-level extension. The old statement and the complete citer audit are also recorded under the split-owned `split_report.statement_correction`, not a maintainer-owned top-level field.

I scanned every current node's `stmt_deps` and `proof_deps`; the six direct citers are exactly those in the return. “Holds” below means that its current use of this corollary remains justified after the correction.

| Citer | Holds | What I checked |
| --- | --- | --- |
| `cor-pur-affine-space-zero-section-purity` | false | Its statement is unrestricted in `n` and explicitly calls the named comparison an isomorphism by this corollary. The normalized affine-line orientation has the same datum restriction. That use requires the divisibility assumption or a separate all-level extension. |
| `thm-pur-regular-immersion-purity` | false | Step 3 uses affine-space purity for the structural projections in the linear model, and then its zero-section normalization, without restricting the coefficient index. The present justification only covers divisible levels. Its all-level conclusion needs a separate reduction argument. |
| `thm-pur-trace-normalization-transitivity` | false | Its fiber normalization step uses this corollary and the named affine-line classes for unrestricted `A_{E,n}`. It must restrict that model calculation or prove and apply transport to other levels. The transitivity conclusion itself is not disproved by this audit. |
| `prop-pur-affine-space-purity-compatibilities` | true | Its statement begins “In the situation of [cor-pur-affine-space-purity]”, so it inherits the restored divisibility assumption. Its two named map factors remain in that situation. |
| `det-sp-finite-existence-chart` | true | Its coefficient is `Z/ell^n`. Specialize `E=Q_l` and `varpi=ell`; the ramification index is one, so the added hypothesis holds for every index in that statement. Clause (2)'s invocation remains valid. |
| `lem-pur-projection-purity-agreement` | true | The current statement constructs `Gamma` at all levels but expressly identifies it with the named affine-space comparison only on `e(E/Q_l) | n`. This citation is already restricted to the corrected domain; it does not derive all-level isomorphy from this corollary. |

The three false entries report unsupported current uses, not counterexamples to the three theorems. Their files are outside this worker's scope and remain unchanged.

## Source error

The corollary in both blueprint snapshots leaves the standing coefficient hypothesis implicit, whereas its current convention and comparison definition do not impose it. I made the hypothesis explicit by reference to the source datum's standing convention. The separate source-proof phrase “for d>=1 the composition law” is also inaccurate when using blocks `(d-1,1)`; at `d=1` that law's positive-block hypothesis fails. The two base cases in this split repair that omission without changing the induction route.

## Tool use for maintainer review

`thm-sf-preservation-class` (2) is used only as the generic statement that the constructible exceptional inverse image of a separated finite-type morphism preserves `D^b_ctf`. The induction needs it for `p:A^1_Y -> Y`; no statement of the historical affine-space unit supplies that preservation assertion. The return already accepts this use mathematically. In response to C8 I removed the worker-written `split_report.tool_uses` declaration and set no top-level `tool_uses`. The maintainer may record the accepted tool at merge; the reason is given here for that review.

## Review by Q113

I read the master corollary and the relocated main-20261015 corollary and its `.proof.md` in `sk-lem-sp-finite-existence`, the affine-line datum in both snapshots, the current DAG datum, the current affine-line theorem's entire statement and its coefficient-verification Step 1, and its main-20261015 statement source. These readings expose the exact omitted hypothesis; reading the comparison definition alone, as the earlier report did, cannot verify the theorem's domain. I also read the full current statements of `def-pur-affine-space-comparison`, `prop-pur-affine-space-composition-law`, and `thm-sf-preservation-class`, alongside their main-20261015 sources in `sk-prop-an`, `sk-prop-sp-composition`, and `sk-prop-sp-et-proet`. The DAG's more precise constructible preservation statement, not an unrestricted ambient adjoint assertion, is the tool used here. I read the historical unit and chapter records and the three levels in SETUP; the split still performs the affine-space iteration of the affine-line calculation and changes no unit or chapter record.

For Step 1 I checked three actual cited statements. The comparison definition explicitly sets the zero-dimensional map to the identity and defines the positive-dimensional map recursively with the stated unit identifications. The datum explicitly constructs the affine line and requires the divisibility condition, which the corrected statement now provides at the fixed coefficient ring for every separated finite-type base `T` in the induction. The affine-line theorem asserts that precisely the specified comparison is an isomorphism for every finite-Tor input on a base of that datum. These justify the zero and one cases; the length-one recursive composite consists of the line isomorphism and the defining identity/unit isomorphisms. The coefficient data do not vary when the base changes.

For Step 2 I checked all five cited statements. The comparison definition supplies separated finite-type schemes and projections, so preservation clause (2) applies to `p:A^1_Y -> Y` and puts `M=Rp^!K` in exactly the induction's input category. Its hypotheses are verified by the polynomial charts and coordinate-difference diagonals already written in that definition. The datum remains available for the fixed `E,n` over both `Y` and `T=A^1_Y`; the affine-line theorem therefore applies to `gamma_{p,K}`. The induction is universally quantified over bases and inputs, so it applies to `gamma_{q,M}` with base `T`. The composition-law statement gives exactly the displayed formula with block lengths `(d-1,1)`, both positive for `d>=2`, source reassociation `J`, direction `c^{-1}`, and twist/shift `(d-1)[2d-2]`. Applying a functor to the two inverse equations and composing inverses in reverse order are the elementary operations completing this step. No proof-internal claim of a cited node is being substituted for its statement. All eight uses have a verbatim quotation in `citations.json`.

I tested `d=0`, `d=1`, and `d=2` separately; the last has blocks `(1,1)`. The zero complex and empty base cause no exception. For `e=1,n=1` the datum is available; for `e=2,n=2` it uses `N=1`; for `e=2,n=3` it is deliberately outside the corrected statement. Although the dimension-zero identity exists for every index, the corrected corollary uniformly retains the source standing coefficient domain. These tests concern the actual cited theorem, not just the existence of the comparison map.

B1–B9 and C5 introduce no new-node obligations: there are no new nodes, no duplicate lemmas, and no elementary operations promoted to nodes. I searched the whole blueprint with `tools/blueprint_refs.py search` and checked the existing Lean result rather than attaching its weaker existence conclusion. For the corrected item I reran the prescribed `msearch.py` searches: LeanFinder with a coefficient-aware description, Loogle, Mathlib grep, LeanSearch, then a second LeanFinder phrasing using the relative dualizing complex. I read all returned types/descriptions. The hits concern ramification ideals, affine-space schemes, ordinary homological-complex projections, or compiler purity; none proves this comparison. The five exact queries and actual hits, logged by the command, replace the older search summaries in the node. No unavailable service was recorded as an absence result.

Point by point for the return: E1 is repaired by making the source standing divisibility hypothesis explicit in the statement and verifying it in both steps; E7 is repaired by the named statement-correction section with the explicit failed `N=3/2` domain check and all six citers audited; F4 is repaired by reading the affine-line theorem and its datum, and testing the coefficient edge cases rather than inferring its domain from a different definition; C8 is repaired by removing the worker tool-use declaration and reporting the requested acceptance only in prose. I rebased the retained split-owned fields on the current shared node without running git or changing its maintainer metadata. No Lean file was written, no compiler was run, and nothing was delivered.

## Validation

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q113 cor-pur-affine-space-purity --no-push .` printed `OK (not pushed)` at `848362f358` on 2026-10-17: server preflight passed. That command runs the server's DAG and split checks; no local checker, compiler, Lake or build was invoked. After replacing the pending-validation sentence with this result, I rerun the same dry run and leave the sandbox exactly as accepted. No delivery push is authorized or performed.


## Second reading by Q113

- Item statement: checked against the main-20261015 `sk-lem-sp-finite-existence/cor-pur-affine-space-purity.md` statement and proof, the master corollary, and both snapshots of `def-pur-affine-line-datum.md`, especially the standing hypothesis at line 28; PASS for the repaired statement. The source's standing ramification-index divisibility is now explicit, the base is separated finite type, and the conclusion concerns the specified comparison on every finite-Tor input. The existing `STATEMENT-DISPUTED` account correctly distinguishes the failed datum check at e=2,n=3 from a counterexample to an all-level purity theorem.
- Step 1: opened all three cited DAG statements and the corresponding main-20261015 comparison definition, affine-line datum, and affine-line theorem; PASS. The comparison definition gives the dimension-zero identity and the length-one recursive composite; the affine-line theorem gives invertibility of its actual comparison, with the coefficient restriction supplied by the datum. The induction quantifies over every permitted base and input, so its later change of base is legitimate. Identity/unit identifications are invertible and introduce no additional theorem obligation.
- Step 2: opened all five cited DAG statements and the main-20261015 composition-law and preservation statements; PASS. The polynomial projections are separated finite type as expressly recorded in the comparison definition. Preservation clause (2) puts Rp^!K in the induction's input category. The affine-line comparison is invertible at the fixed permitted coefficient level. Substituting block lengths (d-1,1) in the composition law gives exactly the displayed twist, shift, reassociation and inverse composition map for d>=2. Applying a functor to inverse equations and composing the displayed inverses proves invertibility in a few elementary lines. No proof-internal property of a cited node is used.
- New nodes: none; PASS. There are no B1–B9 form, duplication or unnecessary-node issues, and no new Mathlib leaf. I searched the existing DAG by the affine-space purity/comparison vocabulary and read the slopmaster2 declaration `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpace` at `WeilConjectures/EtaleCohomology/Purity/Smooth/AffineSpace.lean:356–398`; it asserts existence of an object isomorphism and explicitly says the ordered comparisons are unconstructed, so it does not close this item. The split's direct sources are blueprint files, not Stacks tags; no Stacks TeX assertion or forbidden SGA route is introduced.
- Edge cases and citers: PASS. Checked d=0 (identity), d=1 (one line comparison), d=2 (blocks 1,1), the zero complex, Y=Spec(k), and the empty base; the current preservation statement explicitly covers the empty-chart case. Checked e=1,n=1 and e=2,n=2 (N=1); e=2,n=3 fails the datum's integer requirement and is excluded. Independently scanned all current statement/proof dependency lists and opened all six citers: the report correctly flags the three unrestricted uses in zero-section purity, regular-immersion purity and trace normalization, while compatibilities inherit the corrected domain, the chart node has e=1, and projection-agreement explicitly limits agreement with the named maps to divisible levels. These maintenance needs remain reported without changing other items.
- Citations: PASS. All eight (step,node) pairs have exactly one quote in `citations.json`; each quote is verbatim from the current cited statement. No quote needs repair.

Changes made in this second reading:

- Appended this independent review, preserving all first-worker sections including `## Review by Q113`.
- Ran fresh LeanFinder, Loogle, Mathlib grep and LeanSearch queries with different phrasing; retained their actual `searches.jsonl` records and appended matching summaries to the item's `mathlib_searches`. The returned types concern ordinary affine-space scheme maps, mapping cones, ordinary left-derived functors, Euclidean projection, or Lean state declarations; none states the specified purity comparison. No result was promoted to a leaf.
- Retained the repaired statement, both proof steps, dependency lists and citation quotations: their hypotheses, maps and source route passed the independent reading. The maintainer-owned `tool_uses` field remains untouched; the existing report explains why preservation is the needed generic tool.

The earlier Validation section records the first worker's dry run and its then-current decision not to push. This second-reading brief explicitly authorizes the final delivery. The required server dry run and delivery follow this review; no live project, launcher or Lean source file was written, no git command was run in the shared repository, and no compiler was invoked.

Second-reading validation: the required `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q113 cor-pur-affine-space-purity --no-push .` completed with `OK (not pushed)` at `8df4e9ae99`; server preflight passed. The final delivery command reruns preflight on this report and the same checked mathematical split.
