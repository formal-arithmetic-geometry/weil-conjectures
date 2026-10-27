## Worker report

Q06, stage 1, 2026-10-23. Item: lem-sfb-ringed-site-conservative-flatness.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-conservative-flatness.json: unchanged statement, four proof steps, exact proof dependencies, source provenance, search records and split report. Mathlib verdict: no exact match for the arbitrary ring-sheaf criterion.
- citations.json: one verbatim statement quotation for every cited node in every proof step.
- report.md: this report. searches.jsonl is the unmodified log produced by msearch.py.

## New nodes

None. There are zero new nodes and zero new Mathlib leaves. The needed ordinary-module result was found as Module.Flat.rTensor_exact and Module.Flat.lTensor_exact and is already represented by lem-weil-pbc-flat-tensor-exact. It is cited, not duplicated.

### Attachments

None. I searched lean/WeilConjectures both for the blueprint tag and for flatness/stalk terminology. The exact item was not found. Scheme stalk-map flatness, fixed-coefficient etale flatness and flatness at a single point do not supply every clause under this item's hypotheses. No Lean was written or compiled.

### WANTED

None. The relevant Stacks source is available locally.

### Problems found and changes

The item was statement-only, with no proof. Its statement agrees with Stacks 05VC (sites-modules-lemma-check-flat-stalks), for an arbitrary commutative ring sheaf and conservative topos points. I did not correct or weaken it. The existing normalized point interface supplies exactly the finite-product transport of ring and module operations required in the item.

I retained the existing source, statement dependencies and all inherited blueprint provenance. The ancestor command reports blueprint.from.node = None for this created item. Its inherited from.place already specifies the exact supporting-input chain ending in 05VC. I retained that null ancestor instead of inventing an imported blueprint identity. I read the current latest blueprint at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, particularly proof (3), and the current chapter and unit records. The present supporting lemma is below the fixed unit route, not a replacement for it.

The total-tensor node promises an isomorphism of complexes, not explicitly a natural isomorphism of module tensor functors. Rather than take unstated naturality from it, step 2 applies it to the entire three-term complex K and M[0]. Exactness transfers across this isomorphism of complexes. This accounts for the actual differentials without strengthening the citation.

### Unfinished work

None in this one-level split. No new statement-only obligations were needed.

## Searches and reuse

I searched the whole DAG by 05VC/05VB, stalk/point flatness, tensor-stalk comparisons, conservative exactness, and ordinary flat tensor exactness, then opened the matching statements. Blueprint searches for ringed site conservative flatness, conservative, 03EL and 05VC produced no exact duplicate of the item. The conservative hits are special geometric situations or different functors; the existing ringed-site-point-flat node is the forward implication only, and etale-flat-geometric-fibers has constant coefficients on a scheme site.

All Mathlib queries in the new search entries were run through the prescribed msearch.py command, and the actual returned hits were read. The two ordinary-module phrasings found rTensor_exact/lTensor_exact and their iff variants; I read Mathlib/RingTheory/Flat/Basic.lean lines 323-345 and the existing Mathlib leaf. The separate item queries through LeanFinder, LeanSearch, Loogle and grep found scheme stalk-map flatness/localization or no hits, not the item. The two semantic phrasings are the direct flat-sheaf criterion and the ordinary exact-tensor formulation. All services answered; none is recorded as unavailable. Earlier search entries in the copied item are retained as provenance.

## Not duplicates

No new nodes. In particular no new node was created for ordinary flat-tensor exactness, flatness at a point, or conservative reflection of exactness. The latter is three lines of kernel-quotient reasoning from exactness and the given conservativity and is written as a step.

## Review by Q06

I read Stacks sites-modules.tex, lemma-check-flat-stalks (05VC) and its complete proof, the preceding lemma-stalk-flat (05VB), lemma-pullback-flat (05VD), and lemma-check-exactness-stalks (05V3). The proof follows 05VC: the forward implication is flatness at a point; the reverse implication uses the tensor comparison and detection of exactness. I read the fixed chapter/unit route, the latest direct-images proof and SETUP's three levels; the split adds no alternative route above this lemma. I used no SGA source: the cited source is Stacks and its written proof, not its bibliographic reference.

Step 1: I opened def-sfb-ringed-site-point and lem-sfb-ringed-site-point-flat. The former explicitly says normalized presentations exist for every point, gives the underlying-set natural identification, and fixes ring and module operations by inverse finite-product comparisons. Thus its module is the item's module, not an unrelated scalar action. The latter explicitly states that the image of any flat R-module sheaf is flat over the point ring. Its category need only be essentially small; our small site satisfies this. No locality, finiteness, quasi-coherence, constant-ring or Noetherian condition is introduced.

Step 2: I opened def-pc-cochain-complex-modules, lem-sfb-ringed-site-point-exact, lem-weil-pbc-flat-tensor-exact, def-pc-tensor-complex-sheaves and lem-sfb-ringed-site-point-tensor. The cochain definition allows the zero extension of a three-term complex. The exactness node explicitly asserts exactness of the normalized module functor. The ordinary tensor node explicitly preserves exactness at the middle of a three-term sequence, for an arbitrary flat module over an arbitrary commutative ring; this is applied to R_i and S_i(M), not to a constant global coefficient ring. The signed-total definition makes the degree-zero second factor eliminate every other summand and its differential. The point-tensor node gives an isomorphism of these total complexes, which suffices for exactness. I did not extract an unstated map formula or naturality clause from that node. Every cited node's relevant complete statement is in citations.json.

Step 3: I reopened the abelian module-category statement, exactness statement and normalized point definition. Exactness preserves kernels and cokernels and hence their composite image construction; therefore it preserves the displayed quotient ker(b)/im(a). There is no additional geometric lemma hidden here: the quotient vanishes at every point, so its map to the zero sheaf is a bijection after every inverse image; the hypothesis of this item makes that very map an isomorphism. A singleton underlying module has its unique zero module structure. This elementary argument proves the reflection claim in the step, rather than citing a definition as if it implied conservative exactness. It also handles an empty conservative family: the hypothesis then already makes every set-sheaf morphism an isomorphism, and the same argument works.

Step 4: I opened the signed-total definition, sheaf-tensor definition and flat-sheaf definition again. The reduction to the three tensor terms follows from their displayed formulas, including the differential. Additivity is proved on pure tensors and descends through the stated sheafification construction. Step 2 plus the reflection argument in step 3 proves preservation of every exact triple, in particular triples containing zero, hence every short exact sequence. This is exactness of the additive tensor functor, precisely the flat-sheaf definition. No uncited assertion that an arbitrary tensor functor is exact is used.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against these node statements and sources. With no new nodes there is no statement-only-node, duplicate-node or false-new-lemma issue. The existing generic point nodes are explicitly declared as tool uses in split_report (not a new top-level tool_uses approval); no node in this item's unit gives their arbitrary-ring-sheaf statements. The ordinary algebra node is already a Mathlib leaf. A transitive statement/proof dependency traversal found no path back to the item from any of the point inputs. Every proof step is under 2000 characters, and the assembly is under 3000 characters. The elementary steps spell out their kernel-quotient and degree-zero arguments.

Edge cases checked: the one-object point site reduces to ordinary flatness; M=0 gives exact zero tensor functors and flat zero stalks; zero stalk rings cause no problem because their modules are zero; an empty family is addressed above; a nonconstant ring on a ringed topological space uses its actual stalk rings, with no comparison to a fixed coefficient ring. Infinite families and arbitrary modules cause no infinite tensor total in the application: the test complexes have only three terms and the second factor has one term. The universe convention is unchanged and the site is small in the chosen coefficient universe. I found no statement dispute, added hypothesis, weakened conclusion or source error.
