# Worker report: lem-trf-etale-descent-through-source-cover

Group Q73; stage 1; 2026-10-18. Direct delivery with self-review, as authorized in the dispatcher brief. No other agent was started.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-descent-through-source-cover.json`: existing statement node, now split into four steps; no exact Mathlib match. The statement and statement dependencies are unchanged. Existing metadata, ancestry, and original Mathlib search records are retained; the six searches actually run in this sandbox are appended.
- `citations.json`: twelve entries, one for every step/node citation, with verbatim portions of the corresponding statement.
- `report.md`: this report. Search-command output is recorded by the search tool in `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file changed; this item is not a unit's key node.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint tag, etale descent, surjective etale morphisms and the relevant declarations. No declaration of the project states the item exactly. The existing proved `AlgebraicGeometry.Smooth.of_comp_of_flat_of_surjective` is only the smoothness input; it belongs to the already-existing `lem-sbc-smooth-flat-surjective-source-descent`, so no node or attachment is being invented for it. Upstream master was treated only as reference material.

## WANTED

None. Every source needed here is present in the Stacks source tree.

## Findings and corrections

The item is true with exactly its existing hypotheses, including arbitrary schemes. No statement dispute or statement correction was necessary. Its empty proof and dependencies are replaced by an actual argument; the input node's source citation to 036W is correct. I followed that tag through 02KM to the smoothness and dimension argument of 02K6. The smooth case of 05B5 supplies smoothness and hence the local finite presentation which 02K6 assumes separately. The final proof spells out why local finite presentation supplies local finite type before applying 02JS.

The original search records correctly distinguish opposite-arrow cancellation from this item. I ran LeanFinder with two different formulations, LeanSearch, Loogle, and two source-grep queries using the prescribed `msearch.py` command. The hits were read: Mathlib `Etale.of_comp` (Etale.lean:130--140) concludes that the first arrow is etale assuming the second is unramified; it cannot conclude etaleness of h here. The `DescendsAlong` instance (LocalFlatDescent.lean:47--48) descends through target base change. Composition, base-change stability and surjective ring-homomorphism results also do not state this source-cover assertion. None gives a one-line specialization. All six successful searches are recorded as no match; no unavailable service was misreported.

Whole-DAG searches by 036W, source-etale descent and permanence, together with blueprint_refs searches for `Etaleness descends surjective etale source cover`, `etale descent`, and `surjective etale`, found the reusable component nodes. No blueprint node states this exact assertion. The same_as field remains []. Historical ancestry through the old semistable branch is retained, as supplied by the item; the present auxiliary argument changes neither the contracting-correspondence unit nor its chapter route.

## Unfinished work

None in the one-level split. Existing dependency nodes remain their owners' work. Server checks and push are performed by the required delivery tool; no Lean file, compiler, Lake, build, or forbidden local checker is used.

## Not duplicates

No new nodes. Existing nodes are cited, including the general flat fibre-dimension equality; the weaker same-unit composite-dimension inequality is deliberately not used as if it were an equality.

## Review by Q73

I read descent.tex 036W (lemma-etale-etale-local-source), 02KM (lemma-syntomic-smooth-etale-permanence), and the smooth case of 05B5 (lemma-smooth-permanence), then morphisms.tex 02K6 (lemma-etale-permanence-two), its cited 02JS, the remark after 02GI and the source-locality statement 02GJ. I also read the existing nodes' full statements, rather than relying on their titles. There are no new-node sources to check.

Step 1 uses exactly the flatness and local-finite-presentation clauses of def-weil-etale-morphism, the smoothness clause of lem-weil-pbc-etale-smooth-zero-dimensional-fibres for h composed with p, and the general source-descent assertion of lem-sbc-smooth-flat-surjective-source-descent. Its q is our p: flat, surjective and locally finitely presented. Its smooth composite is our h composed with p. No quasi-compactness is assumed. The smooth definition explicitly supplies local finite presentation for h. Thus this use does not confuse target base change with source precomposition.

In Step 2 I checked the affine quantifiers of lem-weil-pbc-lfp-affine-opens-finite-presentation: it applies to every affine U mapping into an affine V. Affine opens form a basis by lem-weil-pbc-affine-opens-basis, so these U cover the inverse image of each V. The images of the displayed finite list of polynomial variables generate each quotient algebra. This proves precisely the local-finite-type definition cited by the step, in a few lines. It is an elementary step, not a new lemma disguised as a node. No finite subcover or Noetherian base is being assumed.

In Step 3 the surjectivity definition really supplies y over every chosen x. The etale-to-zero-dimension node gives the two specific dimensions, dim_y(Y_x) and dim_y(Y_t). The additive-dimension node assumes both maps locally finite type and its first map flat at the lifted point; Steps 1--2 provide exactly these assumptions. It states equality for dimension at a point of the scheme-theoretic fibres, so substituting the two zeros gives dim_x(X_t)=0 without identifying that dimension with the dimension of a local ring. The existing same-unit inequality would only give 0 <= dim_x(X_t), which is insufficient; I chose the existing equality node instead.

Step 4 applies the near-point criterion with global smoothness as the neighbourhood hypothesis and the dimension just proved. That node states the existence of an etale open neighbourhood, which is exactly what the step takes from it. The source-locality node states the iff for an arbitrary open covering, including the empty family when X is empty, so it globalizes these neighbourhoods. Neither citation requires separation, global finite type, or Noetherianity.

I checked the identity-cover case, empty X and Y, and the infinite disjoint union of copies of X as a surjective etale p: the proof never uses a finite subcover or global quasi-compactness. Removing surjectivity would make the assertion false: the empty etale map to X=Spec(k[e]/e^2), with T=Spec(k), has etale composite but h is not etale. Thus the proof genuinely uses the stated cover hypothesis. Positive-dimensional smooth h cannot slip through Step 3, because its fibre dimension would contradict the displayed equality.

Against delivery-errors B, the unchanged item is self-contained, its definitions are cited, TeX uses single logical backslashes, and source labels/tags are verified against tags/tags; I corrected the draft local-finite-presentation implication tag to 01TW before delivery. B1, B6 and B8 introduce no new-node or Mathlib-leaf obligations, and B9/B10 are covered by the blueprint and Lean searches above. Against C1--C4 I checked each non-elementary input against the quoted node statement; twelve exact quotes are in citations.json. C5 is satisfied by reuse of existing nodes; a dependency traversal found no cited component reaches the item (C6). Off-unit smoothness, fibre dimension and etale criteria are declared generic tools in split_report.tool_uses, not written as maintainer-owned tool_uses (C7--C8).

Against D1--D5 the four steps carry the proof, create no restated clauses, and do not copy a document citation as an argument; the short local-finite-type implication is expanded despite the source's omitted proof. Against E1--E7 I checked each hypothesis and each fibre's base point, used the equality rather than the inequality, and kept scheme-point dimension distinct from local-ring dimension. All four proof steps are shorter than 2000 characters, and none hides an additional comparison or lemma. No SGA source is used, no statement is silently weakened, and no unavailable source or failed service has been reported as evidence.
