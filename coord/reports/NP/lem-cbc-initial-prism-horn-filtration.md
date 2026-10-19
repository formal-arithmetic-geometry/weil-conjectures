# Stage-1 report: lem-cbc-initial-prism-horn-filtration

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-initial-prism-horn-filtration.json`: item split into four proof steps; no Lean attachment and no Mathlib exact match.
- `dag/nodes/sec-smooth-purity/lem-cbc-horn-image-pushout.json`: statement-only auxiliary node; no Mathlib match.
- `citations.json`: verbatim quotations for every node used by every proof step.

## Attachments

None. I searched both read-only project source trees under `WeilConjectures/` for the item id, its title terms, `01DN`, and prism/horn-filtration declarations. No project declaration states the item without `sorry`.

## WANTED:

WANTED: Kerodon Lemma 4.4.4.7 (tag 01DN), for the free-simplex filtration and its endpoint condition; read online 2026-10-17, with no archival copy in `literature/`.

WANTED: Kerodon Lemma 3.1.2.11 (tag 03X4), for the general horn-image pushout criterion in `lem-cbc-horn-image-pushout`; read online 2026-10-17, with no archival copy in `literature/`.

No Stacks or SGA source is being substituted for these Kerodon results, and no SGA source is used.

## What was wrong in the node, the blueprint, or the brief

The imported item had the exact intended statement but no proof. The blueprint ancestry points to the finite-prism opening of `thm-cbc-finite-level-proetale`; the current main-20261015 and older blueprint trees contain no standalone statement of this combinatorial lemma, so the proof is marked agent-written from Kerodon. The Mathlib searches found `SSet.prodStdSimplex` coordinate/pairing declarations, `SSet.horn₂₀/₂₁/₂₂.isPushout`, and general pairing/relative-cell infrastructure, but no exact finite filtration with the prescribed initial subset and endpoint condition. I therefore added only the genuinely reusable horn-image pushout criterion; the product enumeration and ordering remain proof steps of the item rather than clause-sized duplicate nodes.

## Not duplicates

- `lem-cbc-horn-image-pushout` vs `lem-weil-pbc-simplicial-set-glue-simplex`: the existing node attaches a simplex along its full boundary under degree hypotheses, whereas the new node attaches an arbitrary simplex along an arbitrary horn identified by an inverse-image condition.
- `lem-cbc-horn-image-pushout` vs `lem-coef-infinity-right-prism-boundary`: the existing node states a special interval-by-simplex right-horn filtration, whereas the new node is the general pushout criterion used to verify one attachment.
- `lem-cbc-initial-prism-horn-filtration` vs `lem-coef-infinity-right-prism-boundary`: the item handles arbitrary `m` and `n≥2`, starts from `(∂Δ^m×Δ^n)∪(Δ^m×Λ₀^n)`, and allows inner or outer horns with an endpoint clause; the existing node handles only `Δ¹×Δ^m` and successive positive-index horns.

## Review by NP

I read the item, its `sk-prop-sf-cbc` unit, the `sec-smooth-purity` chapter, the current blueprint ancestor `thm-cbc-finite-level-proetale`, the inherited ancestry through `lem-cbc-invertible-prism-extension` and `lem-cbc-enhanced-functor-cone-calculus`, and delivery-errors B–E. I also read the exact online Kerodon 01DN proof: its free simplices are ordered first by dimension and then by decreasing index, and its three face cases establish the old inverse image as one horn. I checked the endpoint statement directly from the vertex chain. The helper node follows Kerodon 03X4 and is statement-only.

Step 1 uses only the standard-simplex and horn definitions in `def-cbc-enhanced-diagrams-cones`; I verified that the product has finitely many nondegenerate simplices and that the ordering is finite. Step 2 uses the same definition for coordinate projections and the initial boundary/zeroth-horn union; I checked both cases of the smallest occurring `(p,1)` and the inserted `(p,0)` face. Step 3 uses the same horn definition and spells out all three omitted-face cases, including the earlier tie-broken simplex and the contradiction for the missing `p`th face. Step 4 uses the exact statement of `lem-cbc-horn-image-pushout`: the image union is `X_s` and the inverse image is the indexed horn, so the cited pushout criterion applies. It also checks `q_s≥2` and, when `p_s=0`, the vertices `(0,0),(0,1)`.

I opened every cited node and copied the relevant sentences into `citations.json`; each quote is verbatim. No step relies on a cited node's proof. The new helper is strictly smaller than the item and does not restate an item clause. I tested edge cases `m=0`, `m=1`, `n=2`, and the empty boundary `∂Δ⁰`; the construction remains finite, and the endpoint condition is meaningful only for the `p=0` attachments. No hypotheses on coefficient categories or base-change maps occur here. No statement dispute or dependency cycle was found. The recorded LeanFinder, Loogle, grep, and LeanSearch commands were actually run through `msearch.py`; all returned no exact match for the helper or item.

## Unfinished work

None for this one-level split. The Kerodon sources remain WANTED because they are not archived locally; the next reader should independently verify the combinatorial cases and then run the required delivery dry run.

## Second reading by NP

The earlier sections record the first worker's submission. This independent reading supersedes their helper-node choice; the final delivery has **zero new nodes and zero new Mathlib leaves**. I read delivery-errors B–E, `coord/dag-sync.md`, `GOAL.md`, the unit/chapter records, the main-20261015 compact-support base-change proof, and both online Kerodon sources (01DN and 03X4).

- Item statement: compared hypothesis by hypothesis against Kerodon Lemma 4.4.4.7 (01DN), statement and clauses (1)–(2): $m\geq0$, $n\geq2$, finite filtration, initial subset, $q\geq2$, $0\leq p<q$, pushout, and the two endpoint values all agree; no statement correction is needed.
- Step 1: checked against 01DN's definition and ordering of free simplices and the full statements of `def-cbc-enhanced-diagrams-cones` and `def-weil-pbc-simplicial-set`; verdict: sound after expanding why degeneracy is repetition, why chains have bounded length, why the initial chain is forced, and why the index is unique. Every subset generated here is explicitly the union of the simplex images, since those images are closed under every operator.
- Step 2: checked against 01DN's exhaustion argument and the horn definition in `def-cbc-enhanced-diagrams-cones`; verdict: sound after explaining why all coordinates below the first $(p,1)$ must occur with second coordinate zero, giving the exact position for inserting $(p,0)$. Collapsing repetitions covers degenerate simplices without a hidden general decomposition theorem.
- Step 3: checked each omitted-face case against 01DN's predecessor-horn argument and the cited simplex/horn definition; verdict: sound after expanding the inserted $(p+1,0)$ case and classifying every possible free enlargement of the missing face. For $p>0$ the distinct enlargement has index $p-1$ and is later; for $p=0$ none exists. The old subset cannot contain the top simplex without its missing face. This proves the entire inverse-image equality, not just the inclusion of the horn.
- Step 4: checked against 01DN's pushout conclusion, Kerodon Lemma 3.1.2.11 (03X4), `def-weil-pbc-simplicial-set` (morphisms are natural transformations), and `def-weil-pbc-category-colimit` (existence and uniqueness of a compatible cocone map); verdict: the present attaching simplex is embedded, so define the extension separately on the two closed subsets and check agreement on their intersection, naturality, and uniqueness. These elementary lines replace the general criterion. Surjectivity of the second projection gives $q\geq n\geq2$, and the initial chain gives the endpoint clause.
- Submitted new node `lem-cbc-horn-image-pushout`: read its full statement and compared it with Kerodon 03X4, including the $r>0$, union, and inverse-image hypotheses; verdict: mathematically correct and statement-only with definitions and source, but unnecessary here. The item only attaches embedded strict chains, for which direct gluing is elementary; removed this uncommitted node under C1/C2 and the brief's rule 3, rather than leaving another item for the maintainer.

I opened every cited definition statement; no citation uses a proof or an unstated general theorem. `citations.json` has a fresh verbatim quote for each final citation, including the simplicial-set morphism and colimit definitions used in elementary step 4. No other-unit non-leaf result is used as a tool.

Independent duplicate/Mathlib checks: whole-DAG searches for 01DN, 03X4, horn inverse images, and prism filtrations found the item and its parent but no replacement; the existing `lem-weil-pbc-simplicial-set-glue-simplex` assumes a full-boundary attachment under degree hypotheses, and `lem-coef-infinity-right-prism-boundary` is a different interval/right-horn filtration. Whole-blueprint searches in both snapshots for prism/initial-horn/horn-filtration/free-simplex vocabulary found no duplicate. Read-only searches of both Lean source trees for the item, 01DN, and prism/horn-filtration vocabulary found no declaration stating the item. My own differently phrased LeanFinder query “A subcomplex union the range of an embedded simplex is a pushout over their intersection” returned `SSet.Subcomplex.BicartSq.isPushout`; Loogle `"BicartSq"` and a scoped Mathlib grep confirmed `SubcomplexColimits.lean:84–100`, which I read. This concerns embedded-subset gluing, not the original general helper or the whole item. All searches ran through `msearch.py`; their actual logs remain in `searches.jsonl` and the item records the relevant results. No new leaf is required for an argument written directly in a few elementary lines.

Small cases: $m=0$ has empty first boundary and exactly the single attachment $\Lambda_0^n\hookrightarrow\Delta^n$ with the required edge; $m=1,n=2$ includes both outer and inner attachments; $p=0$ is treated without referring to an invalid index $-1$. The cases $m=0$, $m=1$, $n=2$, and the empty boundary are all allowed. No scheme, ring, field or coefficient hypotheses occur. A separate finite strict-chain enumeration also checks exhaustion and every face intersection, attachment dimension and endpoint in the tested cases; this is a mathematical sanity check, with no Lean compilation.

Changes and reasons: removed the unnecessary general helper; expanded the chain normalization, missing-face enlargement and $p=0$ arguments; wrote the embedded pushout gluing directly and marked that step elementary; added the exact definition citations and updated `citations.json`; corrected `proof_deps` and `split_report` to the resulting four-step proof. The imported item's statement and the first worker's report sections are preserved. No SGA source is used.


Finite enumeration results (strict chains / attachments): $(m,n)=(0,2)$: 7/1; $(0,3)$: 15/1; $(1,2)$: 31/4; $(1,3)$: 79/6; $(2,2)$: 103/9; $(2,3)$: 303/19; $(2,4)$: 831/33. Every check passed.

Validation: `python3 /home/ubuntu/weil-launcher-nt/deliver.py NP lem-cbc-initial-prism-horn-filtration --no-push` printed `OK (not pushed) deliver/NP/lem-cbc-initial-prism-horn-filtration at a80067b53a: preflight passed`. The installed tool accepts no trailing `.` argument, so I used its documented argument syntax. The final delivery command repeats preflight on the report carrying this result.
