# Worker report: lem-kun-dimension-extension

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-dimension-extension.json`: item, statement; split into nine steps with twenty existing proof dependencies. Mathlib searches found no exact match for the two-clause statement.
- `citations.json`: twenty-six verbatim statement quotations, one for each step/node citation.
- No new DAG nodes and no new Mathlib leaves. `write_split.py` is sandbox scratch material only, not part of the delivery.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the blueprint id, dimension/extension/dense-open terminology, and the dimension names, and searched `dag/lean_names_upstream.json`. The project file `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:140` proves equal dimension of nonempty opens only for integral schemes. It does not state the arbitrary reducible dense-open clause or field-extension clause. The item has Lean audit state `none`. Upstream master was not used as finished-proof evidence.

## WANTED

None. The shared read-only tree omits the untracked literature payload. I read the obtained copies at `/home/ubuntu/weil-launcher-nt/literature/`, without modifying them or downloading anything. Logical source references retain their repository-relative `literature/` names.

## Source error

The item statement is correct and has not changed. The imported blueprint proof incorrectly calls the projection `X_L -> X` finite type for every field extension. Set `X = Spec K` and `L = K(t)`: this projection is not finite type, since a field finitely generated as a K-algebra is algebraic over K. The proof's unqualified claim that the upstairs residue fields are obtained from the downstairs ones by base change also needs care: a tensor product of fields can be a product or have nilpotents, so it is not in general a residue field. I replaced this passage by the existing affine-cover result and Stacks 00P3. This is a change below the unit level: the unit record has no proof steps, and its Kunneth statement is unchanged.

The original proof invokes the dimension formula but does not supply its Noether-normalization and component arguments. The revised proof reuses the existing 00P3 and irreducible-closed-subset/transcendence-degree nodes, rather than creating copies of them or moving the item's two clauses into new nodes. The component proof is written out rather than inferring preservation of dimension from density alone.

## Existing-node and blueprint searches

Read `dag/units/sk-prop-sf-kunneth-ordinary.json`, `dag/chapters/sec-smooth-purity.json`, the three-level route rule of SETUP, the standing brief, stage 1, GOAL, dag-sync, the worker role, and delivery-errors B through E. The item is not the key statement of the unit, so no unit fields are delivered.

Searched the whole DAG for dimension under field extension, dense opens, irreducible components, open-cover bounds, Noetherian schemes, sobriety, open restrictions, and the tags 00P3, 0A21, 04MU. Ran `tools/blueprint_refs.py search` for `dimension`, `dense open`, `00P3`, and `extension`, and `ancestor lem-kun-dimension-extension`. The ancestor is the item. There is no other blueprint node stating the entire two-clause item, hence `same_as: []`. `lem-pc-dim-base-change` overlaps only the affine field-extension clause and adds a curve application; it does not state the dense-open clause. `base-change-dimension` assumes algebraically closed fields and curves. Neither is an exact duplicate of this item.

Opened the statements of all twenty cited nodes, and also examined the existing proofs of the affine-cover and irreducible-closed-subset nodes. The selected dependencies do not lead back to this item. Definitions, Mathlib leaves, and the Lean-closed open-cover bound are generic tools. Off-unit theorem tools are explicitly declared in `split_report.tool_uses`: affine charts, affine field-extension dimension, the open-cover bound, finite-type Noetherianity, finite component cover, quasi-compact open immersions of finite type, locally finite type composition, and the dimension/trdeg theorem for irreducible closed subsets. None replaces a step prescribed by the unit.

## Mathlib audit

The item has state `none`, so I searched it with the required `msearch.py Q44 lem-kun-dimension-extension` command. All six tool/query pairs in its `mathlib_searches` are copied from actual calls in `searches.jsonl`. The first semantic phrasing asked for both scheme invariances. The second asked for the more general affine-algebra field-extension result. Loogle returned only the definition, homeomorphism invariance, subspace monotonicity, the spectrum/ring dimension comparison, and the Artinian dimension-zero criterion. The first grep found a polynomial-fibre rewrite at `Mathlib/RingTheory/KrullDimension/Polynomial.lean:39`; the second, restricted to `AlgebraicGeometry`, found Artinian and stalk/coheight results. I read these source regions and the topological Krull-dimension declarations: they do not state either requested invariance. LeanSearch returned HTTP Internal Server Error and is recorded as `unavailable`, never as a negative result. LeanFinder and Loogle succeeded. No new node needs a separate search record.

## Review by Q44

I read the item's actual blueprint source, including its entire proof paragraph, and Stacks Algebra 00P3 (`algebra.tex`, lemma-dimension-preserved-field-extension), together with Varieties 0A21 (`varieties.tex`, lemma-dimension-locally-algebraic), especially (6), (8) and their proofs. The first has exactly a finite type algebra over a field and an arbitrary field extension; it imposes neither algebraicity nor finite generation of the extension. The second explains why component dimensions are determined by generic-point residue transcendence degree. These support precisely the two unchanged assertions of the item. I also read the supporting source passages: Schemes 01JQ/01JR on affine fibre products and open fibre products; Schemes 01IS on unique generic points; Properties 01OV/01OW/01OZ and 0BA8 on Noetherianity, opens and finite components; Morphisms 01T3/01T5/01T6; and Topology 0055 and 0B7I. There are no new-node statements to check.

Step 1 uses only the definitions of base change, open immersion and chain dimension. An object with a map to the empty scheme has no points; the empty space has no irreducible chains. This handles the empty case before invoking the nonempty hypothesis of the affine-cover node.

Step 2 uses exactly the statement of `lem-pc-dim-base-change-affine-covers`, not its construction: matching covers, finite type coordinate algebras, and nonemptiness of the extension. `def-weil-finite-type-morphism` supplies locally finite type. There is no separatedness assumption, so none was added.

Step 3 applies the statement of `lem-weil-pbc-dimension-preserved-field-extension` with S = A_i, ground field K and extension field L, all supplied in step 2. I checked its tensor ordering: it states L tensor A_i, whereas the chart node gives A_i tensor L. The explicit swap and its inverse remove that difference, and `lem-weil-pbc-homeomorphism-krull-dimension` transfers dimensions through it and the two chart identifications. The cited node already states topological spectrum dimension, so no unquoted local-ring/topological comparison is being used.

Step 4 uses the exact open-subspace monotonicity statement with the larger open equal to the whole scheme, and the exact open-cover bound in the converse direction. `lem-weil-pbc-scheme-sober` states uniqueness and existence of generic points for every irreducible closed subset. This gives the quasi-sober and T0 hypotheses of that bound: singleton closures are irreducible, so two points with the same closure would be two generic points of one irreducible closed set. Thus the affine equalities really give both global inequalities.

Step 5 first checks that Spec K is Noetherian directly: a field has only two ideals and its spectrum is one point; `pqf-def-locnoeth` is used only as the definition. `lem-weil-pbc-finite-type-over-noetherian` then gives Noetherian X. I deliberately used `lem-sc-noetherian-closed-subset-finite-components`, which says that the closed subset is a finite union of its components, rather than a statement merely saying there are finitely many of them. Applied to E = X, it supplies the required finite closed cover. The open-subscheme Noetherian node explicitly supplies quasi-compactness of U and every U intersect W; it is not being cited merely for a definition of Noetherianity.

Step 6 checks quasi-compactness of j on every affine W, using that U intersect W is quasi-compact. Only then is the quasi-compact-open-immersion node applied. In the permanence node I use only clause (e), which explicitly states composition of locally finite type morphisms, not a purported finite-type clause. Together with quasi-compact U over the one-point base and the definition of finite type, this supplies all hypotheses for the dimension/trdeg node in U at step 8.

Step 7 uses generic-point existence from the sober node and component maximality from the component definition. I checked the point often hidden behind 'dense': remove all OTHER components, a finite closed union, to obtain an open O_i containing eta_i and contained in C_i. Density gives a point of U intersect O_i, and the generic-point closure identity forces eta_i into this nonempty open of C_i. The proof does not assume that density by itself meets an arbitrary closed subset. Its remaining closure-in-a-subspace identity is elementary.

Step 8 uses the full statement of `lem-sc-closed-irreducible-dimension-trdeg` twice. In X, C_i is nonempty irreducible closed with generic point eta_i; in U, C_i intersect U is nonempty irreducible closed with the SAME generic point. X was finite type initially and U was proved finite type in step 6. I wrote the cofinal-neighbourhood argument for the equality of their local rings, and then quotient by the maximal ideal using `def-weil-residue-field`. This is an isomorphism over K, since constant germs agree; it preserves algebraic independence by testing polynomials and its inverse, exactly the definition in `def-kun-transcendence-degree`. No geometric irreducibility, reducedness or separability is assumed.

Step 9 takes dimension directly from strict chains. The largest member of a chain lies in one component because a finite union of proper closed subsets cannot cover an irreducible space. Conversely chains of a closed component remain closed chains upstairs. The same reasoning places each chain of C_i intersect U in U. This gives the lower bound; the cited open-subspace monotonicity node supplies the upper bound. These are short elementary chain arguments, not new lemma nodes or an appeal to the proof of a cited node.

Small cases checked: empty X (dimension bottom on both sides); Spec K with any L/K (dimension zero); nonreduced Spec K[epsilon]/(epsilon^2) (the unique generic residue field is K); A^1_K and its punctured affine line (dimension one); a disjoint union of A^2_K and Spec K (a dense open must retain the isolated component and still has maximum dimension two); and two crossing affine lines (the other-component complement used in step 7 is nonempty on each component). An inseparable extension may introduce nilpotents upstairs, but the 00P3 node allows nonreduced algebras. The counterexample L = K(t) above tests the removed finite-type assertion. No small case required a change to the statement.

Against B-E: no new-node duplication or statement-only obligations arise; no new clause-restating node was made; every non-elementary input has a verbatim citation; all proof dependencies are their union; all elementary steps contain their arguments; and no cited statement requires missing properness, reducedness, algebraic-closedness, or a finite extension. The source route change is recorded openly above. I corrected the imported finite-type-projection error and expanded the generic-point and stalk identifications. No mathematical work remains unfinished; the independent second reader is to review and deliver the accepted sandbox.

## Validation

Ran `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q44 lem-kun-dimension-extension --no-push`. It printed `OK (not pushed) deliver/Q44/lem-kun-dimension-extension at 2e1ece8709: preflight passed`. The accepted check covers the DAG overlay, split review, route/tool-use declarations and citation quotations. A final dry run is repeated after recording this result. No branch was pushed and no Lean compiler or build tool was run.

## Second reading by Q44

- Step 1 checked against the base-change, open-immersion, and Krull-dimension definitions and the empty scheme: PASS; the empty case gives dimension $-\infty$ on both sides.
- Step 2 checked against the statements of `def-weil-finite-type-morphism` and `lem-pc-dim-base-change-affine-covers`: PASS; it uses only local finite type and the matching affine covers, with no finite-type assertion about $X_L\to X$.
- Step 3 checked against `lem-weil-pbc-dimension-preserved-field-extension` and `lem-weil-pbc-homeomorphism-krull-dimension`: PASS; the tensor-order swap is an explicit inverse ring isomorphism and hence a spectrum homeomorphism.
- Step 4 checked against the open-subspace monotonicity, open-cover bound, and scheme-sobriety statements: PASS; unique generic points give both sobriety and $T_0$, and the two inequalities give equality of the cover supremum, including empty members.
- Step 5 checked against the Noetherianity, finite-component, and open-subscheme statements: PASS after repair; the maximal-finite-union argument now explicitly supplies quasi-compactness of every open $U\cap W$.
- Step 6 checked against the quasi-compact-open-immersion and locally-finite-type composition statements: PASS; quasi-compactness is established before applying the finite-type criterion, and the final quasi-compactness check is explicit.
- Step 7 checked against scheme sobriety and the irreducible-component definition, including the finite-component density argument: PASS; each component generic point is shown to lie in the dense open.
- Step 8 checked against the irreducible-dimension/transcendence statement, open-immersion sheaves, residue fields, and transcendence degree: PASS after repair; cofinal neighbourhoods explicitly identify the two stalks and the induced $K$-field residue isomorphism.
- Step 9 checked directly against the chain definition of dimension and open-subspace monotonicity: PASS; finite irreducible-component covering gives the maximum component dimension and both global inequalities.
- No new nodes were created, so there are no new-node statements or Mathlib leaves to audit; all citations are existing nodes and were checked verbatim in `citations.json`.

Changes made: strengthened Step 5 with the missing quasi-compact-open argument, strengthened Step 8 with the cofinal-stalk argument, and added this per-step second-reading record. The imported source error concerning finite type of arbitrary field-extension projections remains documented above; the item's two clauses are unchanged.

The earlier review sentence that the open-subscheme node explicitly supplies quasi-compactness of every $U\cap W$ should be read as relying on the Noetherian-open argument now written in Step 5; that node directly supplies Noetherianity of $U$, and the second reading made the open-subset implication explicit.
