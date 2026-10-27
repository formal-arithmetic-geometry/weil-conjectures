# Stage-1 delivery: lem-sfb-space-closed-pushforward-relative-flatness

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-closed-pushforward-relative-flatness.json`: existing statement split into five steps; no new nodes and no Mathlib leaves. Statement and statement dependencies retained.
- `citations.json`: eighteen entries, each quoting the cited node's statement verbatim.
- `searches.jsonl`: five new searches made by the prescribed msearch command; the item's earlier searches are retained.
- `report.md`: this report. `write_split.py` is sandbox-only preparation, not part of the delivery.

## Attachments

None. Searched WeilConjectures for the item id, relative flatness, and closed-pushforward flatness. `AlgebraicGeometry.Etale.flat_lowerStar_obj_of_isClosedImmersion` in `SixFunctors/Etale/Derived/Stability/FlatModelGeneration.lean:93` is sorry-free text, but it concerns fixed coefficient-ring sheaves on schemes, only the preservation direction, and flatness as an object of the coefficient-sheaf category. It does not state the relative O-module assertion over T or the algebraic-space clause. It is not an attachment. No Lean was written or compiled.

## WANTED

None. All mathematical sources used are present under literature/stacks-project.

## Problems found and changes

The imported statement is correct and unchanged. The proof was empty. The given geometric-stalk source is insufficient by itself to compare the ordinary Zariski stalks in the flatness definition; the argument now explicitly passes through scheme charts and Zariski/etale comparison. It also proves the converse on every chart of Z, using flat source descent, and checks arbitrary target etale charts for the final structure-sheaf assertion. No flatness of the closed immersion, finite presentation or Noetherian hypothesis has been introduced.

The source's Tag 0DK1 formula has the subscripts interchanged, as the imported item's source already records: i_*F is on X and has its stalk at bar x, while F is on Z and has its stalk at bar z. The proof uses the well-typed ordinary-stalk statement Tag 00AE instead. This does not require a statement correction to this item.

The inherited blueprint chain has from.node=null, as `tools/blueprint_refs.py ancestor` confirms; its from.place and via were retained. Read the latest blueprint unit and det-thm-sf-ctf-stability-direct-images, especially proof (3). This split is the Hilbert-is-Quot flatness input below the inherited alteration chain, not a replacement for the compactification/direct-image assembly. Searches `blueprint_refs.py search closed pushforward`, `search flat closed`, `search relative flatness`, and `search pushforward flatness` find no blueprint node stating this relative-flatness result. same_as remains [].

## Mathlib searches

Read both LeanFinder result sets, Loogle, LeanSearch, and grep results from searches.jsonl. Both semantic phrasings return flat scheme morphism criteria, restrictions and stability under base change, not this assertion for relative O-modules on algebraic spaces. Loogle `"Flat", "pushforward"` returns no hits. Grep returns `Ideal.comap_map_eq_self_of_faithfullyFlat` in Mathlib/RingTheory/Flat/FaithfullyFlat/Algebra.lean, read at lines 105ff; its pushforward is extension of ideals, not sheaf direct image. None is a match. No search was invented, and no service was unavailable.

## Not duplicates

No new node. DAG keyword and Tag 0DK1 searches found the existing geometric-stalk node and closed-immersion QCoh node; the former states geometric stalks, the latter supplies quasi-coherence but does not state relative flatness. Additional searches found the Zariski/etale equivalence, the unrestricted functor comparison square, etale direct-image restriction, closed ordinary abelian stalks, flat source-cover descent, and etale base-local-ring flatness. All are reused.

## Review by Q135

I read quot.tex Tag 0D00, lemma-hilb-is-quot, including both the omitted forward affine-flatness argument and the final reverse-flatness sentence. I checked spaces-morphisms.tex Tag 0DK1 and its proof and observed the already reported swapped point subscripts. The proof I supply is agent-written expansion of the omitted argument, using sheaves.tex Tag 00AE, spaces-properties.tex Tag 03LX, descent.tex Tags 03DX/03LC, morphisms.tex Tags 01U3/01U4 and 02JZ, and flat.tex Tag 05BA. There are no new statements whose sources require separate validation.

Step 1 uses the existing closed-immersion QCoh theorem exactly for quasi-coherence of i_*G, with no finite-type assumption; the representable closed-immersion convention makes V=Z x_X U a scheme. I opened the etale restriction node: it states the canonical direct-image comparison for arbitrary module sheaves, not merely flat base change. The scheme Zariski/etale equivalence states that restriction to opens is its inverse. I also opened the functor-square node, whose unrestricted first clause identifies the two pushforwards on Zariski opens, identically on sections. This is the clause used; I removed an unnecessary attempt to establish separatedness for applying its stronger QCoh direct-image clause. Quasi-coherence on charts is restriction of the local presentation predicate.

Step 2 uses the ordinary abelian-stalk node, which states zero on the complement and the canonical germ isomorphism on the closed subset. It is not the geometric-stalk theorem. I checked its germ formula: pulling a base function through V -> U -> X -> T gives exactly the function acting on H, so the isomorphism is linear over O_{T,t}. This supplies the scalar compatibility which an abelian-group isomorphism alone would not supply. The zero module's flatness is explicitly tensor-injectivity for 0 -> 0. The definition node's equivalent stalk criterion then gives the pointwise flatness equivalence on each pair of charts.

Step 3 only quantifies Step 2 over all U and the corresponding V, hence is elementary. The algebraic-space definition supplies the meaning of these charts. No additional pushforward theorem is hidden in the quantification.

Step 4 does not assume a chart of Z extends to X. The algebraic-space definition gives a surjective etale atlas of X. The fibre-products node says its base change covers Z and that both further chart fibre products are schemes; the two maps from E are etale, and E -> W is surjective. The etale definition includes flatness. The scheme comparison theorem explicitly respects tensor pullback, so the same Zariski module on E is the pullback from V and W. The source-cover theorem states both the pointwise flat-forward implication and the surjective-flat converse over the unchanged base T, with no quasi-compactness requirement. Those are precisely the two uses here. I checked all these actual statements, not their proofs.

Step 5 checks a sometimes missed distinction: the module-flatness convention fixes T, whereas the space-morphism chart definition tests every B -> T. O_Z is quasi-coherent by its free presentation. The scheme flatness definition identifies flatness of its local rings with flatness of W -> T. The etale-base-local-ring node says that an arbitrary O_{B,b}-module is flat over O_{T,t} iff over O_{B,b}. Applied to O_{W,w} this proves the arbitrary target chart test. No finite generation of the module is assumed in that node.

For delivery-errors B1-B10: no new unsplit node, no undocumented new notion, no duplicate or clause copied into a new node, no Mathlib leaf with a guessed declaration; the item retains its source and blueprint metadata and adds recorded real searches. For C1-C8 I matched all eighteen uses to exact statement quotes in citations.json, checked that no proof of a cited node is used, and declared the off-unit generic tools in split_report.tool_uses for maintainer review. For D1-D5 the five steps carry the proof, including the source's omitted argument; no content is moved to a new node. For E1-E7 I verified representability, chart surjectivity, flatness of the etale maps, QCoh hypotheses and base-ring actions at the applications. Each proof step has fewer than 2000 characters.

Small cases: Z empty gives i_*G=0 on all charts and both flatness conditions are vacuous/zero; i identity gives identical stalk tests. For a non-flat closed immersion Spec(Z/2) -> Spec(Z) over T=Spec(Z), the structure sheaf and its pushforward are both non-flat over Z; the argument does not mistake a closed immersion for a flat morphism. For a field base, both sides are flat even for nonreduced closed subschemes. Infinite-type closed ideals cause no change to the neighbourhood/stalk computation. Empty E or V causes no invalid point choice in the source-cover argument. All the used nodes are existing independently reusable lemmas rather than restatements of this item.

## Remaining work

No uncompleted part of this split. The reused unsplit dependencies remain their own items. Required server dry run and push follow this review.
