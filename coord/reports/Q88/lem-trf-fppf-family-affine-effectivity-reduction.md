# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fppf-family-affine-effectivity-reduction.json`: item, same statement, four assembly steps.
- `dag/nodes/sec-trace-formula/lem-trf-fppf-family-coproduct-descent-encoding.json`: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle and targeted grep.
- `dag/nodes/sec-trace-formula/lem-trf-fppf-affine-refinement-pullback-model.json`: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle and targeted grep.
- `citations.json`: a verbatim statement quotation for every citation in each assembly step.

## Attachments

None. Read the project declarations by blueprint tag and by family/coproduct/refinement concepts. The exact item theorem `AlgebraicGeometry.fppf_family_isEffective_of_affine_singletons` in `lean/Sheaf/AlgebraicGeometry/FppfFamilyAffineEffectivityReduction.lean` ends with `sorry`. No exact completed declaration occurs under `lean/WeilConjectures/`. The nearby fpqc property-descent theorems concern a given morphism, or singleton covers with stronger affine hypotheses; they are not this family effectivity statement.

## WANTED

None: the sources used are available locally.

## Return repaired

The returned live node has seven steps totaling 5403 characters. The supplied sandbox contained only dispatcher marker files, no node, report or search log. I copied the live node as the baseline and retained its statement, citations/search records and all historical/maintainer metadata. There was no prior sandbox split/report on which to run a preliminary dry run. This is an actual re-split, with two new unsplit statement-only nodes, rather than an unchanged re-push.

The coproduct-encoding node transfers old steps 1 and 2, together with the recovery of family isomorphisms from old step 7. The affine-refinement-pullback node transfers old steps 3 and 4 and the canonical-pullback construction from old step 5. These are comparable independent construction tasks: disjoint-open descent and fpqc coverage on one side, affine-local refinement with Cartesian pullback identifications on the other. Neither mentions the property's affine-effectivity hypothesis or concludes that arbitrary data are effective. Thus neither restates the item.

The uses of (i), (ii), isomorphism invariance and (iii) from old steps 3 and 5 are explicit in new assembly step 2. Old step 6 remains assembly step 3. The open-local inference in old step 7 remains assembly step 4. Every argument of the returned proof is therefore assigned either to a new statement-only work item or to a remaining assembly step. The complete previous proof is reproduced below so a subsequent worker retains all its arguments; no proof sketch is put inside either new statement.

## Search and blueprint reading

I searched all `dag/nodes/` for 023X, 021P and 02W3 and family/singleton, coproduct/fpqc and affine-refinement/datum concepts; then parsed statements and source places of the candidates. I also read the source statements of all old proof dependencies. `tools/blueprint_refs.py ancestor` gives `lem-trf-local-term-locality`. Whole-blueprint searches were made for `descent family`, `fppf affine`, `023X`, `coproduct`, `02W3`, `021P`, `descent datum`, `descent`, `refinement`, `family`, and `affine`. No imported node states either new lemma. The new blueprint records prepend this item to the inherited via chain and specify the geometric quotient-presentation support via 0265 and 02W8. The chapter and curve-zero unit route are retained; no SGA source is used.

All new Mathlib queries were run with the required msearch.py command, read, and recorded verbatim from `searches.jsonl`. LeanSearch was rate-limited and is recorded as unavailable. LeanFinder and Loogle were available. For the first node, the pseudofunctor `exists_equivalence_of_sieve_eq` candidate in `Mathlib/CategoryTheory/Sites/Descent/DescentData.lean:401` was read: it needs equality of the generated sieves. A family and its coproduct do not generally have that equality (even the identity of a disconnected coproduct need not factor through one summand), so it does not give the claimed equivalence in one line. Scheme gluing hits supply the component gluing tools only. For the second node, `OpenCover.affineRefinement` in `Mathlib/AlgebraicGeometry/Cover/Open.lean:156` concerns a Zariski open cover, with no finite fppf subcover or descent datum component model. AffineTransitionLimit hits concern cofiltered diagrams, absent here. `Scheme.fppfPrecoverage_le_fpqcPrecoverage` and `Hom.singleton_mem_fppfPrecoverage` in `Mathlib/AlgebraicGeometry/Sites/Fpqc.lean:66,101` supply cover facts only, not the two construction packages. Neither new node is a Mathlib leaf.

## Review by Q88

I read Stacks `descent.tex`, Tag 02W3 (`lemma-descending-types-morphisms`), statement and all proof paragraphs; Tag 023X (`lemma-family-is-one`), including double/triple product identifications; Tag 023Y (`lemma-pullback`), including the actual transport composite; and Tag 02W0 (`lemma-refine-coverings-fully-faithful`). I read `topologies.tex` Tags 021P (`lemma-fppf-affine`), 021Q (`definition-standard-fppf`), and the fpqc convention 022B. The item is precisely the fppf specialization of 02W3, including finite presentation on the singleton hypothesis; no hypothesis has been silently strengthened.

For the coproduct-encoding node I checked that 023X gives a datum and recovers the original transitions, while double/triple component gluing supplies the cocycle. The realization clause is an assertion for the same specified W, so it carries both directions of the old component-restriction argument, not an assumption of effectivity. The additional fpqc claim is exactly old step 2: restrict over an affine U, apply 021P, regard its finitely many W_j as open affine subschemes of the disjoint union, and check flatness on the component local rings. This uses no finite index assumption and asserts no property P of an infinite coproduct.

For the affine-refinement-pullback node I checked the two base changes are distinguished: A_U is over U and Z_U is its pullback over A. The identity in degree two is (A_U times_U A_U) = (A times_T A) times_T U, and the degree-three identity gives the restricted cocycle and transport compatibility with D. A point of C lies in a W_j, whose map to A_U lands in the chosen T_i component; the fibre product there is Q_j = V_i times_{T_i} W_j. Thus the displayed component identification is over C, which is exactly what the P hypothesis needs. Finite affine coproduct gives affineness of C; flatness is checked on components, surjectivity by the finite refinement, lfp by the finite-coproduct lfp fact, and qcqs because C and U are affine. In particular this node adds the finite-presentation and datum-identification assertions missing from the existing mere affine-refinement node. Canonical E has the actual Cartesian projection and intertwining transports from 023Y; these are conclusions of its statement, not details the parent borrows from its proof.

Assembly step 1 uses the new encoding statement for its coproduct datum, fpqc cover and realization equivalence. Assembly step 2 uses the new refinement statement for D_U, p, h, E and the Q_j identification. It then applies exactly (i) to the Q_j base changes, (ii) only to finitely many such maps and (iii) only to the verified affine flat surjective finitely presented p. The empty finite coproduct is explicitly covered by (ii). Assembly step 3 uses `lem-galois-fpqc-covering-base-change` with U -> T; its statement really gives an fpqc covering after this change. `lem-galois-fpqc-refinement-reflects-effectivity` explicitly requires two singleton fpqc covers, a Cartesian projection and transport compatibility; step 2 supplies all of these and the effective E. Assembly step 4 uses `lem-galois-fpqc-effectivity-open-local`, whose statement expressly assumes compatible restricted effective data on every affine open, exactly established in steps 2-3. Its output is effectiveness of D. The encoding lemma's same-W clause then gives the original family realization. Verbatim quotations of each of these statements are in citations.json.

I tested I empty: joint coverage forces T empty, so A and Z are empty and W/T is necessarily empty. If U is empty, m=0 is permitted and all finite-presentation, fpqc and component pullback conclusions hold; assumption (ii) includes this case. Repeated indices i(j) cause distinct summands in C, not identified opens. For infinite I only the topology uses finite subfamilies over each affine U; no P of Z/A is inferred. Intersections of affine opens are never assumed affine and no quasi-separatedness of T is used. All source and new statements use the fixed universe convention for set-indexed coproducts. The pre-existing stage-2 review warns that a particular Lean universe implementation may need a small-subcover argument; no Lean is changed in this stage-1 repair and no enlargement invariance of P is assumed here.

I checked B1-B7: the new nodes have no proof, are self-contained, explicitly cite the notions they use, use singly escaped TeX, and cite Stacks tags with labels. For C1/C4 I matched the actual assembly uses to the opened statements as described above, retaining the full Cartesian/transport clauses rather than citing definitions for them. For D1/D2 both new nodes construct data without P and do not conclude general effectiveness, leaving the actual effectivity deduction in the parent. For E I checked affineness, finite presentation, empty families and the precise base maps above. The repair changes the allocation of work; it does not change the item's statement or omit an old argument. No assembly step exceeds 2000 characters. The generic cross-unit tools still used by the item are declared in split_report.tool_uses.

## Not duplicates
- lem-trf-fppf-family-coproduct-descent-encoding vs def-weil-pbc-fpqc-covering: the existing node is the definition of an fpqc covering, not construction of an fpqc coproduct from an fppf family.
- lem-trf-fppf-family-coproduct-descent-encoding vs lem-a1-universe-enlarged-proetale-cover: the existing statement transports an already fpqc family through universe enlargement; it constructs no coproduct datum or affine refinement.
- lem-trf-fppf-family-coproduct-descent-encoding vs lem-pc-field-extension-fpqc-cover: the existing statement is only the Spec of one field extension; there is no arbitrary covering family or scheme descent datum.
- lem-trf-fppf-family-coproduct-descent-encoding vs lem-pc-fppf-affine-refinement: the existing statement only gives finitely many open affine refining schemes; it gives neither a singleton scheme datum nor its Cartesian component pullback model or realization compatibility.
- lem-trf-fppf-family-coproduct-descent-encoding vs lem-pc-fpqc-descent: the existing node is descent of quasi-coherent modules and invertible modules, not a construction of scheme descent data from coproduct components.
- lem-trf-fppf-family-coproduct-descent-encoding vs lem-weil-pbc-fpqc-affine-standard-refinement: the existing statement gives a faithfully flat product ring for an fpqc cover of an affine scheme, with no singleton datum, family realization equivalence or finite-presentation pullback model.
- lem-trf-fppf-family-coproduct-descent-encoding vs lem-weil-pbc-fpqc-local-on-base-criterion: the existing statement descends a property of a pre-existing morphism, not construction of a family/coproduct scheme descent datum.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-galois-descent-pullback-construction: the existing statement constructs the singleton pullback functor for a fixed refinement; the new statement also constructs the finite fppf affine refinement and its explicit component model.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-galois-fpqc-affine-descent-effective: the existing statement proves effectivity for affine morphisms V -> X; the new refinement allows arbitrary V_i and constructs models without proving effectiveness.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-galois-fpqc-affine-model-transition-cartesian: the existing statement verifies a transition square between already specified effective affine models; the new statement constructs a finite cover and datum pullback.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-galois-fpqc-affine-model-transition-reconstruction: the existing statement is an invariance equation for given effective affine models; it supplies neither the finite fppf cover nor the local coproduct pullback.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-galois-fpqc-affine-model-transitions: the existing statement constructs transitions between already effective affine models; the new refinement model assumes no effectivity.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-galois-fpqc-affine-models-glue: the existing statement glues already effective singleton data to a global scheme; the new statement constructs affine-refinement data without assuming they are effective.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-galois-fpqc-canonical-pullback-datum: the existing statement gives a datum after a fixed singleton refinement only; it neither constructs the finite fppf affine refinement nor proves the component identification and finite presentation.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-galois-fpqc-descending-types-morphisms: the existing statement concludes singleton fpqc effectivity with a stronger flat affine hypothesis and P on its underlying map; the new construction has no P or effectivity conclusion.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-galois-fpqc-effectivity-affine-base-gluing: the existing statement assumes effectivity over every affine singleton fpqc base for a property and glues; the new statement constructs a finite fppf affine source and datum without any effectiveness assumption.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-galois-fpqc-effectivity-open-local: the existing statement glues already effective singleton data; the new model constructs the refinement datum before applying the affine-effectivity hypothesis.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-galois-fpqc-pullback-canonical-iso: the existing statement compares pullback functors for two chosen refinements; the new statement constructs a finite flat finitely presented affine refinement and identifies its scheme as a component coproduct.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-galois-fpqc-refinement-reflects-effectivity: the existing statement reflects an assumed effective datum along a specified singleton refinement; the new model constructs that refinement and its component scheme, with no effectivity hypothesis.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-pc-fppf-affine-refinement: the existing statement only gives finitely many open affine refining schemes; it gives neither a singleton scheme datum nor its Cartesian component pullback model or realization compatibility.
- lem-trf-fppf-affine-refinement-pullback-model vs lem-trf-fppf-family-affine-effectivity-reduction: the parent concludes effectivity from hypotheses on P; this new node only constructs cover/datum models and does not assume or prove that conclusion.

## Retained argument and allocation for future workers

### Returned step 1

Allocation: Encoding node: disjoint-open decomposition, assembled transport, inverses and triple cocycle.

Put $A=\coprod_iT_i$ and $Z=\coprod_iV_i$. We first express the family datum as a singleton datum $D$ on $Z\to A$ over $T$. For any $H\to A$, the inverse images $H_i$ of the disjoint open components $T_i$ are disjoint opens covering $H$. They represent $H\times_AT_i$: a morphism to $H$ whose composite lands in $T_i$ factors uniquely through that open subscheme. Thus $H\cong\coprod_iH_i$, by gluing the inverse component maps. Applying this to the relevant projections gives $A\times_TA=\coprod_{i,j}(T_i\times_TT_j)$ and the corresponding decompositions for $Z\times_TA$, $A\times_TZ$, and triple products. On component $(i,j)$ define the transport of $D$ to be $\phi_{ij}$; the component inverses glue too. The cocycle follows component by component from the given family cocycle, and equality on the open cover implies equality globally. Conversely, restricting $D$ to those components recovers exactly the original datum. This is the explicit construction of Tag 023X, rather than an invocation of an uncited equivalence.

Original cited nodes: lem-weil-pbc-scheme-coproduct-family, def-weil-open-immersion, def-pc-fibre-product, lem-weil-pbc-scheme-morphism-gluing, def-pd-descent-datum

### Returned step 2

Allocation: Encoding node: fpqc singleton from finite affine refinements on each affine base open.

The singleton $f:A\to T$ is fpqc. At a point in the component $T_i$, its local ring map is that of $T_i\to T$, so it is flat. For every affine open $U\subset T$, the family $\{T_i\times_TU\to U\}$ is fppf by the cited base-change lemma. The affine-refinement lemma supplies finitely many affine opens $W_j\subset T_{i(j)}\times_TU$ whose images cover $U$. Each $T_i\times_TU$ is the open inverse image of $U$ in $T_i$, by the same factorization through open subschemes as in step 1; hence each $W_j$ is an affine open of $A$. Their images under $f$ have union exactly $U$. Together with flatness this is precisely the definition of an fpqc singleton covering. This argument applies to any fppf family, without assuming its index set finite.

Original cited nodes: def-weil-flat-morphism, lem-trf-fppf-covering-base-change, lem-pc-fppf-affine-refinement, def-weil-pbc-fpqc-covering, lem-weil-pbc-scheme-coproduct-family, def-weil-open-immersion

### Returned step 3

Allocation: Refinement-pullback model node: restriction identities, compatibility with D and component fibre product identification; P application stays in assembly step 2.

Fix an affine open $U\subset T$. Write $A_U=A\times_TU$ and $Z_U=Z\times_AA_U$. Restrict $D$ to a datum $D_U$ over $A_U/U$: the identity $A_U\times_UA_U\cong(A\times_TA)\times_TU$ follows by the two fibre-product universal properties, and the analogous identity in degree three shows that the restricted transport satisfies the cocycle. The projection $Z_U\to Z$ intertwines these transports. Choose the finite refinement $W_j\subset T_{i(j)}\times_TU$ of step 2, and let $C=\coprod_{j=1}^mW_j$. The refinement maps give $h:C\to A_U$ over $U$. By the coproduct and fibre-product descriptions of step 1, $Z_U\times_{A_U}C\cong\coprod_jQ_j$, where $Q_j=V_{i(j)}\times_{T_{i(j)}}W_j$. Each $Q_j\to W_j$ has $\mathcal P$ by hypothesis (i). Notice that no property of the infinite coproduct $Z\to A$ is asserted.

Original cited nodes: lem-trf-fppf-covering-base-change, lem-pc-fppf-affine-refinement, def-pc-fibre-product, def-pd-descent-datum, lem-weil-pbc-scheme-coproduct-family

### Returned step 4

Allocation: Refinement-pullback model node: affine C, flatness, surjectivity, lfp, qcqs, finite presentation, fpqc and empty case.

The morphism $p:C\to U$ is flat, surjective, and of finite presentation between affine schemes. Indeed, $C$ is affine by the finite-coproduct clause of the affine-permanence lemma. Flatness follows at every point from the local ring map on its open component $W_j$, and surjectivity follows from the chosen joint coverage. Every $W_j\to U$ is locally of finite presentation by the refinement lemma, so $p$ is locally of finite presentation by the finite-coproduct lemma. A morphism between affine schemes is affine, hence quasi-compact and separated, in particular quasi-separated, by affine permanence. These properties give finite presentation with exactly the convention in the statement. Also $\{p\}$ is an fpqc covering: for every affine open $B\subset U$, its preimage is affine because $p$ is affine, and this one affine open has image $B$ by surjectivity. If $m=0$, the refinement covers only $U=\varnothing$ and the same conclusions hold vacuously.

Original cited nodes: lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-morphism-affine-schemes-affine, lem-weil-pbc-finite-coproduct-lfp-qcqs, lem-pc-fppf-affine-refinement, def-weil-flat-morphism, def-sbc-locally-finite-presentation, def-weil-pbc-fpqc-covering

### Returned step 5

Allocation: Refinement-pullback model node: canonical Cartesian datum E. Assembly step 2 retains finite-coproduct P and affine effectiveness applications.

Pull $D_U$ back along $h:C\to A_U$ using the canonical-pullback-datum lemma. Its underlying scheme is $Z_U\times_{A_U}C=\coprod_jQ_j$ as in step 3, and its projection to $Z_U$ is cartesian over $h$ and intertwines transports. Hypothesis (ii) gives $\mathcal P(\coprod_jQ_j\to C)$; invariance under isomorphism gives the property for the chosen pullback. For $m=0$ this uses precisely the explicitly assumed empty coproduct case. Step 4 verifies every hypothesis on $p$ required by (iii), so (iii) makes this pulled-back datum effective over $U$.

Original cited nodes: lem-galois-fpqc-canonical-pullback-datum, def-pc-fibre-product, lem-weil-pbc-scheme-coproduct-family

### Returned step 6

Allocation: Assembly step 3: base-changed fpqc cover and reflection across the refinement.

The singleton $A_U\to U$ is fpqc, being the base change of $f:A\to T$ from step 2. The singleton $C\to U$ is fpqc by step 4 and factors through it by $h$. The datum of step 5 is the cartesian pullback of $D_U$ with transport compatibility, exactly the additional hypotheses of the cited refinement-reflects-effectivity lemma. Applying that lemma to its effective pullback shows that $D_U$ itself is effective. Thus for every affine open $U\subset T$ we have effective data $D_U$ on $Z_U\to A_U$, with the transport compatibility to $D$ proved in step 3.

Original cited nodes: lem-galois-fpqc-covering-base-change, lem-galois-fpqc-refinement-reflects-effectivity

### Returned step 7

Allocation: Assembly step 4: open-local gluing. Encoding node: recovery of each family isomorphism and overlap compatibility.

Apply the cited effectivity-open-local lemma to $f:A\to T$ and $D$. Step 2 provides its singleton fpqc hypothesis; steps 3 and 6 provide effective restricted data on every affine open and the required projection/transport compatibility. It yields a $T$-scheme $V_0$ and an isomorphism $V_0\times_TA\cong Z$ identifying its canonical datum with $D$. Restrict this isomorphism to the open component $T_i\subset A$. The fibre-product universal property identifies its left side with $V_0\times_TT_i$ and its right side with $V_i$, as in step 1. Compatibility with $D$ on the component $T_i\times_TT_j$ is exactly compatibility with $\phi_{ij}$. These are the required compatible isomorphisms for the original family. No claim that $V_0\to T$ has $\mathcal P$ is needed or made.

Original cited nodes: lem-galois-fpqc-effectivity-open-local, def-pc-fibre-product, lem-weil-pbc-scheme-coproduct-family, def-pd-descent-datum

## Outstanding work

The two new statement-only nodes are deliberately unsplit for independent workers. The item assembly is complete at stage 1. No Lean file, compiler or build tool was written/run. The required server dry run exited successfully: `OK (not pushed)` at `f3d3e232b71`, preflight passed. The subsequent delivery push runs the checks again.
