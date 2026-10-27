# Q65: lem-sfb-space-relative-flat-locus-base-change

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-flat-locus-base-change.json`: statement, now split into four proof steps; no Mathlib match.
- `citations.json`: twelve entries, one for every cited node in each numbered step, copying verbatim statement text.
- `report.md`: this report. The sandbox also contains the actual `searches.jsonl` and a scratch writing script.

New nodes: 0. New Mathlib leaves: 0. No Lean written or compiler/build invoked.

## Attachments

None. I searched the current project source by the exact item id and by relative-flat-locus terminology. The only relativeFlat name found is the open scalar restriction of a relatively flat sheaf; its type concerns modules on an open ringed site, not the locus of flat points of an algebraic-space map. Scheme flatness and ring-theoretic flat-locus declarations do not state this item.

## WANTED

None: the Stacks TeX sources needed here are present locally.

## Corrections and route

The mathematical statement and its statement dependencies are unchanged. The imported item had no proof. I expanded the reduction behind Stacks 05X3 through 05X2, rather than making a new module-flat-locus theorem that would merely generalize the item. The existing scheme theorem `lem-sfb-relative-flat-locus-base-change` supplies both its clauses. The source tags were checked against `literature/stacks-project/tags/tags`; the compatible triple construction is in 05WY, not the section tag 05WX (a draft citation was corrected before delivery).

The inherited blueprint.from.node is null; `tools/blueprint_refs.py ancestor` also reports None. I retained that inherited field and its explicit place/via history. The place traces this to `det-thm-sf-ctf-stability-direct-images`, proof (3), through the existing alteration/moduli chain. I read the current file under `literature/blueprint/latest/`; its proof (3) is the direct-image/compactification route, not a direct statement of this supporting flat-locus theorem. No unit or chapter route is changed by the present split. Searches of the whole imported blueprint for flat locus and flatness found no blueprint statement of this algebraic-space theorem. The existing scheme theorem is a useful proper special case and is cited rather than duplicated.

Three off-unit statements are declared as generic tools in split_report.tool_uses: the scheme-atlas/quotient-topology lemma, fibre products and base-changed covers, and etale-cover composition/permanence. They concern atlas infrastructure and do not replace a unit-level direct-image argument. All other proof citations belong to this item's unit, or are a definition.

## Not duplicates

No new node was created. In particular no algebraic-space module variant of 05X2, compatible-triple lemma, or chart-independence lemma was added: the scheme relative-flat-locus theorem and the existing atlas, strict-local-flatness and etale-permanence statements already give the required inputs.

## Review by Q65

I read the statement of Stacks 05X3 in `spaces-more-morphisms.tex` and the proof it invokes, 05X2. This proof explicitly reduces to schemes using compatible surjective etale charts and, after an arbitrary algebraic-space base change, an auxiliary scheme atlas of W times_Z Z-prime. I also read the construction of the triple in 05WY, the scheme 05VK statement in `more-morphisms.tex`, the presentation-lifting lemma 02X1 in `spaces.tex`, and the topology and pointwise-flatness passages 03BX and 04NG in `spaces-properties.tex` and `spaces-morphisms.tex`. No SGA route is used. There are no new nodes requiring additional source reviews.

For step 1 I opened all four cited statements. `lem-a1-space-affine-etale-cover` gives a surjective etale scheme atlas for each space and surjectivity on point sets. `lem-trf-space-fibre-products-etale-covers` constructs the intermediate algebraic spaces and preserves etale covers on base change. `lem-trf-space-chartwise-etale-permanence` supplies composition of etale maps and coverings. `def-sfb-space-morphism-properties` explicitly tests flatness, local finite presentation and local finite type on every compatible scheme-chart diagram. The chosen U and W are charts of X and Z, and V and W are charts of Y and Z, respectively. Thus U to W is flat and locally finitely presented, and V to W is locally finite type. I have not inferred flatness of U to V from flatness over W.

For step 2 I opened the full statement of `lem-sfb-relative-flat-locus-base-change`, whose hypotheses are exactly those established for the scheme triple in step 1 and whose first clause makes E open. I opened `lem-sfb-space-strict-local-flatness`: its last sentence defines flatness using a compatible chart and explicitly says it is independent of the choices. Consequently it identifies flatness at every individual u with the item's universal chart condition at a(u), not merely flatness of the entire morphism. This is the precise statement required to obtain E = a^{-1}(L). The atlas lemma explicitly says its point map is surjective and its quotient topology is independent of the chosen scheme atlas, so it proves openness of L from E. I did not cite only the definition of algebraic spaces for this topology claim.

For step 3 I rechecked the same three atlas/fibre-product/permanence statements. W times_Z Z-prime may be an algebraic space, so I choose a fresh scheme atlas W-prime of that space; I do not treat that fibre product as a scheme. U-prime and V-prime are fibre products of schemes over the scheme W. The factorization of a-prime uses two genuine base changes of covers: first W-prime to W times_Z Z-prime, then U to X. Their composition is etale and surjective. The coordinate identity a r = pi a-prime is the equality of the X-coordinates of the same fibre-product tuple. No separatedness, finite type of Z-prime, or flatness of the parameter change was introduced.

For step 4 the second clause of the existing scheme theorem explicitly gives E-prime = r^{-1}(E) for the arbitrary scheme map W-prime to W. The strict-local-flatness lemma again identifies E-prime with the inverse image of L-prime on the new compatible chart. These two exact equalities, together with the coordinate identity and the point surjectivity already proved, give L-prime = pi^{-1}(L). I wrote the membership argument instead of asserting that the equality transports. This avoids the false general assertion that point spaces preserve fibre products.

I checked all seven unchanged statement-dependency statements: they define schemes, universes, algebraic spaces, morphism chart properties, stalkwise flatness and point topology, and construct the required fibre products. Every proof use has a verbatim quotation in citations.json, and proof_deps is exactly their union. No step exceeds 2000 characters; each is a single construction or application followed by subset equalities, with all non-elementary inputs cited. The numerical step lengths in the draft were 606, 504, 938 and 669 characters.

The edge cases require no extra assumptions: if X is empty then U and all its base changes can be empty and L is empty; if a parameter base change is empty the asserted equality is equality of empty subsets. For f the identity the scheme and chart tests give the full source as its flat locus. With a non-flat f the proof only invokes the relative hypotheses on p and q and the scheme flat-locus theorem, not global flatness of f. All arbitrary parameter changes are handled by the auxiliary W-prime construction, including non-schematic bases and non-flat maps.

The Mathlib searches were actually run with the prescribed msearch command and read. LeanSearch and two LeanFinder phrasings returned permanence of scheme flatness and universally open flat morphisms; Loogle for AlgebraicGeometry and flatLocus and grep for flatLocus/flat_locus/AlgebraicSpace gave no matches. These do not identify an algebraic-space relative flat locus. I preserved the inherited searches and added the exact query text and actual log results from this worker; no unrun query is recorded.

## Unfinished work

None. The split is complete. Server review_split passed, with the three generic off-unit tool uses declared and the pre-existing unit realization still unfilled. The required deliver.py --no-push exited successfully with OK (not pushed), commit 184f609a8b1; preflight passed. No check script was run locally. The ensuing push command rechecks the delivery before publishing it.
