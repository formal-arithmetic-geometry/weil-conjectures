# Worker report: lem-sfb-etale-derived-tensor-stalk

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-derived-tensor-stalk.json`: statement, split; no Mathlib match. Five proof steps, thirteen distinct existing dependencies. The statement and its statement dependencies are unchanged.
- `citations.json`: a verbatim statement quotation for every dependency of every proof step.
- No new nodes; zero Mathlib leaves created. `searches.jsonl` contains the actual search-tool results. The inherited searches were retained and the searches run in this session were appended to the item with their exact query texts.

## Attachments

None for the item. I searched the project `WeilConjectures/` by blueprint id and by stalk/tensor/K-flat concepts. `AlgebraicGeometry.Etale.sheafFiberTensorIso` in `SixFunctors/Etale/UpperLowerStar/StalkMonoidal.lean:63` is an ordinary sheaf tensor comparison, not this derived statement. Derived upper-star monoidality is not itself a declaration of the comparison with ordinary module stalks. No attachment is claimed.

## WANTED

None. All literature used is present.

## Findings and changes

The imported item is true as written. It had no proof. Its source, Stacks Tag 0DEN, clause (1), really concerns unbounded K-flat complexes on a ringed site; the existing `lem-pc-kflat-stalk-criterion` concerns ringed *spaces* and cannot be applied directly to the small etale site. I did not create a duplicate general K-flat stalk theorem. For the constant ring in this item, the conclusion follows in a few lines by testing against termwise constant acyclic complexes, after the ordinary total-tensor comparison is established. That argument remains an elementary step of this item, not a new node. Since this differs from the general-ringed-site proof of 0DEN, `proof_origin.by` is `agent`.

The unit's first step and the ancestor `det-ctf-finite-proper-tor` need exactly this stalkwise tensor calculation. I read the current main-20261015 chapter and unit, and the ancestor file `sk-prop-ctf-finite-proper-tor.md`. No unit or chapter route is changed. The stronger arbitrary-ring statement of the item is the generic tool needed for that constant finite-coefficient application. Blueprint searches for K-flat, stalk tensor, K-flat stalk, check-K-flat-stalks, 0DEN and stalks commute found no equivalent blueprint statement; `same_as` stays empty. Definitions, ordinary tensor monoidality and the geometric-stalk colimit lemma are reused. Off-unit statement tools are declared in `split_report.tool_uses` with their individual purposes.

## Not duplicates

No new nodes. In particular, no second copy of `lem-pod-etale-stalk-tensor-scalar`, `lem-kun-stalks-commute-colimits`, or the ringed-space K-flat stalk criterion was introduced.

## Review by Q58

I read Stacks `sites-cohomology.tex`, Tag 0DEN (`lemma-check-K-flat-stalks`) including both its statement and proof, Tags 06YS (`lemma-K-flat-resolution`), 06YT (`lemma-derived-tor-quasi-isomorphism-other-side`), and the construction preceding 06YU (`definition-derived-tor`). I also read 07A4 (`lemma-pullback-tensor-product`), `sites-modules.tex` 03EI (`lemma-sheafification-exact`), 04EQ (`lemma-stalk-exact-modules`) and its tensor-pullback statement, and `etale-cohomology.tex` 03PT (`lemma-stalk-exact`). These sources allow arbitrary complexes and arbitrary commutative coefficient rings. No SGA source is used. There is no new-node source to audit.

For step 1 I opened the statements of `prop-weil-pbc-geometric-stalks-exact`, `def-kun-constant-sheaf`, `lem-weil-pbc-sheafification-geometric-stalk`, and `lem-weil-pbc-site-r-module-presheaf-sheafification-exact`. The exactness node explicitly concerns abelian geometric stalks; the proof explains the extension to constant-ring modules by the induced scalar actions on kernels, images and cokernels. Sheafification invariance is applied to the underlying abelian constant presheaf, and the resulting map is linear because the constant-germ maps commute with scalars. Every pointed neighbourhood maps to the identity neighbourhood, so the colimit of the constant diagram is its value. Exactness of constant complexes is not assumed from a definition: clause (1) of the presheaf node gives sectionwise homology and clause (2) gives exact sheafification. Applying these to an acyclic module complex proves the assertion needed later.

For step 2 I opened `lem-kun-stalks-commute-colimits`, `lem-pod-etale-stalk-tensor-scalar`, and `def-pc-tensor-complex-sheaves`. The ordinary tensor lemma allows every commutative ring and arbitrary etale module sheaves; no finite or locally constant hypothesis is present. Its clause (1) gives the actual natural germ comparison. The colimit lemma supplies arbitrary sums, and scalar actions on the colimit are described explicitly. The total-complex definition supplies the direct sum and sign convention. Naturality on the two differential maps proves the chain equation with the unchanged sign, so this is not an unexplained identification of complexes. The index is the countable set of pairs of integers summing to n.

Step 3 is elementary relative to the preceding two steps and the two opened K-flat definitions: for *every* acyclic A-module complex E, its constant sheaf complex is acyclic; its tensor with P is acyclic; the exact stalk identifies that tensor with SP tensor E. That is precisely ordinary module K-flatness. This avoids an unjustified inference from mere termwise flatness or exact monoidality to preservation of arbitrary K-flat complexes. No new lemma is hidden here, and the statement needs only constant coefficients.

For step 4 I checked that `lem-kun-flat-resolution-existence` supplies unbounded K-flat resolutions on exactly the small etale site, and that `def-kun-derived-tensor` allows any representing complexes and one K-flat replacement. I use K-flat representatives in both variables, with the identity as the first resolution; their stalks are K-flat representatives by steps 1 and 3. Thus both sides are computed by the two ordinary total tensors identified in step 2. The localization is the one explicitly specified by `def-weil-abstract-derived-category`.

For step 5 I checked that the *statement* of `lem-kun-derived-tensor-well-defined` gives canonical independence of the K-flat model as well as the quasi-isomorphism comparison. The chain comparison is natural before localization; its squares therefore commute after inverting quasi-isomorphisms. I corrected the initial draft to use K-flat representatives in both variables. This ensures that on the ordinary-module side the other fixed factor is K-flat when changing either model, so the quasi-isomorphism criterion explicitly stated by `def-pc-module-kflat-complex` applies. No extra theorem about tensoring an arbitrary complex with a quasi-isomorphism between K-flat complexes is smuggled into that argument. Naturality under inverses and composites accounts for derived morphisms and the canonical resolution identifications.

For B--E I verified that this creates no statement-only wrappers or new definitions, cites no node's internal proof, and leaves no uncited non-elementary site theorem. The one elementary K-flat test has its full argument in step 3. All cited statements were opened, and their verbatim text is in `citations.json`. There is no statement dispute or added hypothesis. Small cases checked: the zero ring, zero complexes, a geometric point over the spectrum of an algebraically closed field (the identity comparison), and complexes unbounded in both directions (the degreewise sums remain countable). If T is empty there is no geometric point, so the universally quantified assertion is vacuous. The argument tests every acyclic module complex, not just modules in degree zero. Every step is shorter than 2000 characters; none hides a separate comparison lemma or an invocation of a source's omitted argument.

## Unfinished work

None in this stage-1 split. No Lean source was written and no compiler or Lake command was run. Mechanical validation and delivery are recorded by the required delivery tool.
