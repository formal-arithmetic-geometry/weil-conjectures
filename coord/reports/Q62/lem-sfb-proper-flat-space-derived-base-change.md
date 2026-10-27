## Worker report

Files written (all under `dag/nodes/sec-six-functors-basics/`):

- `lem-sfb-proper-flat-space-derived-base-change.json`: split, statement unchanged; six proof steps.
- `lem-sfb-proper-support-tensor-perfect.json`: statement, unsplit; no Mathlib match. General perfect tensor direct image with relatively flat, finitely presented, bounded second factor and proper term supports, for algebraic spaces.
- `lem-sfb-space-flat-complex-base-change.json`: statement, unsplit; no Mathlib match. General qcqs algebraic-space base change for a bounded-above relatively flat complex, with the actual ordinary-pullback target and canonical map.
- `lem-sfb-derived-etale-zariski-equivalence.json`: statement, unsplit; no Mathlib match. Unbounded quasi-coherent derived equivalence, its canonical unit/counit, exact faithful pullback, and geometric functor comparisons.
- `lem-sfb-etale-detects-perfect.json`: statement, unsplit; no Mathlib match. Detection of Zariski perfectness after small-etale pullback, for an arbitrary complex.

`citations.json` quotes the statement of every cited node at every step. `searches.jsonl` is the unmodified output log of the prescribed search command; `search_results.json` and `search_*.txt` retain the full results read for the new prerequisites. Four new nodes, zero Mathlib leaves. No Lean written or compiled.

Attachments: none. I searched the item tag and the proper/flat/perfect/direct-image concepts in `lean/WeilConjectures/`. The proper-perfect theorem in `ProperPerfectDirectImagePerfect.lean` concerns schemes over a Noetherian base; the relatively flat base-change complex theorem also concerns schemes. Neither gives this algebraic-space statement or its etale-Zariski clauses.

WANTED: none.

The imported item has no proof and its blueprint ancestor chain currently terminates in null. `tools/blueprint_refs.py ancestor` reports `None`. I retained that existing null anchor, the full inherited via chain and exact source-route explanation, and prefixed the item to the via chain of each new node. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, particularly (3), together with the unit and chapter records. This is the coherent-cohomology prerequisite already selected below its alteration/curve-moduli branch, not a change to a unit or chapter route. No unit realization is claimed: this item is not the key unit theorem.

The source's 0CTM(2) says flat over S although its map has target Y; our application has S=Y=T, so this distinction causes no hypothesis problem. We use the precisely formulated 0A1P/0A1K statements directly. In particular relative flatness of a sheaf does not imply intrinsic flatness over O_X; the proof never substitutes such a claim. No unresolved statement dispute or unfinished part of this split remains.

## Searches and existing results

Before creating nodes I searched the entire DAG by the source tags 0CTM, 0A1P, 0A1K, 071Q, 08H8, 08HG and 08GH; by perfect direct-image, tensor, quasi-coherent equivalence, etale-Zariski and mate-pasting concepts; and searched the whole imported blueprint with `tools/blueprint_refs.py search` for these tags and the corresponding phrases. I opened the candidate nodes rather than using their titles. The existing `lem-pc-proper-support-perfect-direct-image`, `lem-pc-rf-base-change-complex`, `lem-pc-rf-perfect-base-change`, `lem-pc-proper-flat-single-derived-direct-image-perfect`, and `lem-sc-proper-flat-derived-direct-image-perfect-universes` are all statements for schemes. They cannot be applied to a nonrepresentable X. The existing `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence` and functor-square nodes concern ordinary modules, not unbounded derived equivalences. I reuse the latter square as a statement dependency specifying the actual ringed-site morphism. I reuse `lem-weil-pbc-mate-pasting` for the category-theoretic theorem rather than creating a coherence lemma.

For each new node I ran two distinct LeanFinder phrasings plus LeanSearch, Loogle and source grep, and read every returned hit. All services answered in these searches. The image searches return flat-module exactness, ordinary direct-image adjunctions and stability of scheme morphism properties; the base-change searches return flatness and ordinary tensor base-change facts. These do not assert the derived pushforward theorems. The derived-equivalence searches return generic derived localization functors, `Equivalence.sheafCongr`, and equivalence between affine-etale and full-etale presentations. I read `Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean` at the equivalence instances and `Mathlib/CategoryTheory/Sites/Equivalence.lean`: their sites are equivalent/dense presentations, not Zariski versus etale quasi-coherent derived categories. The perfectness-detection searches return etale morphism stability and Zariski-local morphism properties, not a perfect-complex predicate. Exact queries and actual outputs are in the node records.

## Review by Q62

I read `spaces-perfect.tex`, labels `lemma-flat-proper-perfect-direct-image-general` (0CTM), `lemma-base-change-tensor-perfect` (0A1P), `lemma-base-change-tensor` (0A1K), `lemma-epsilon-flat` (08H8), `lemma-derived-quasi-coherent-small-etale-site` (071Q, including its proof that the derived restriction is a quasi-inverse and the actual counit is invertible), `lemma-descend-perfect` (08HG), `remark-match-total-direct-images` (08GH), and `lemma-pseudo-coherent` (08JL). I read the site-perfect definition in `sites-cohomology.tex` (08G5), and the base-change construction and horizontal pasting remark there (07A7, 0E47). These sources match the new nodes' hypotheses: 0A1P needs finite presentation of f, bounded finite-presentation relatively flat terms and proper support, but neither Noetherianness nor flatness of f. The 0A1K theorem needs qcqs f and a bounded-above relatively flat complex, not properness or intrinsic flatness of that complex. 071Q and 08HG apply to arbitrary schemes. The finite strict-perfect chart description is the site notion, not the constant-coefficient etale-perfect notion.

In Step 1 the supported tensor theorem is applied with E the rank-one structure complex and G the given sheaf in degree zero. Its statement supplies both perfectness and quasi-coherent cohomology. I checked the closed support argument using properness, and that the tensor unit calculation introduces no extra flatness. During review I corrected the initial draft to put quasi-coherent cohomology explicitly in the cited general theorem rather than relying on a longer uncited kernel argument in the item's step.

In Step 2 the equivalence node explicitly supplies the quasi-inverse R-epsilon, its canonical counit and exactness. The detection node explicitly compares the two perfectness predicates. Thus the proof takes no theorem from a definition node and no claim from the proof of a cited node.

In Step 3 the base-change node has exactly the ordinary pullback G on its target, and explicitly specifies the counit-defined exchange followed by the coefficient comparison. Proper f is qcqs by its separated, finite-type definition. The derived-equivalence node has the arbitrary-scheme-morphism pullback comparison on D_QCoh, so the identification with epsilon applied to Lh*K supplies quasi-coherence of the new etale direct image. This avoids silently assuming preservation theorems for a sheaf after base change.

In Step 4 the same equivalence node supplies full faithfulness and both canonical comparisons. I checked every endpoint of the displayed conjugation: it begins at epsilon_(T')*Lh*K and ends at epsilon_(T')*R-epsilon_(T')*A'. The arrow in the middle is the actual map of Step 3. Conjugation therefore constructs the Zariski canonical map and checks its equality with the etale one; no arbitrary isomorphism is substituted.

In Step 5 I opened `lem-weil-pbc-mate-pasting`: clause (1) is exactly the pasting formula for the two exchange squares, and clause (4) gives the identity case. I checked the coefficient comparisons on scalar tensors and the identity/composition comparisons explicitly present in the site-equivalence statement. The mate node is already a Mathlib leaf and hence is a permitted tool across units; no new off-route tool declaration is required.

In Step 6 I opened `def-weil-pbc-adjunction-mate`: its transpose formula is precisely the formula used. The base-change node specifies the derived adjunction counit and its actual exchange, so this step is the elementary triangle-identity calculation, not an uncited derived adjunction existence claim. The transpose of the pulled scalar unit followed by exchange is the identity; the unit for f' has the same transpose. The equivalence node explicitly normalizes scalar insertion and the unit/counit, giving the Zariski unit equality.

I tested the new statements with zero G, empty X, identity f, a field base, an arbitrary nonreduced/non-Noetherian base, an unbounded first tensor factor in 0A1K, and a non-quasi-compact scheme T for the comparison statements. The zero and empty cases give the zero perfect complex; identity gives the usual scalar-extension maps. Over an arbitrary base the statements are local, so perfect need not mean globally bounded, and none asserts such boundedness. The ordinary tensor target is retained even if G is not intrinsically flat. The detection theorem quantifies over arbitrary A as the source does. All new nodes are statement-only with empty proofs and proof dependencies. Every proof step is shorter than 2000 characters; there is no long hidden comparison proof. I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the files and sources. In particular the general tensor theorems are independent general tools, not copies of the item's clauses; the item carries the specialization and the comparison/coherence argument.

## Not duplicates

lem-sfb-derived-etale-zariski-equivalence vs lem-trf-zariski-etale-functor-comparison-square: the existing statement specifies ordinary module-functor comparisons and degree-zero flat base change; the new statement is the unbounded D_QCoh equivalence with derived restriction and derived pullback.

lem-sfb-derived-etale-zariski-equivalence vs lem-trf-scheme-zariski-etale-quasi-coherent-equivalence: the existing equivalence is of ordinary quasi-coherent module categories and their ordinary functors, not the unbounded derived subcategories and canonical derived counit.

lem-sfb-derived-etale-zariski-equivalence vs lem-trf-etale-extension-free-presentations-hom: the existing statement gives ordinary free presentations, full faithfulness and module sections, not derived essential surjectivity or derived restriction.

lem-sfb-derived-etale-zariski-equivalence vs lem-trf-zariski-etale-tensor-sections: the existing statement constructs the ordinary tensor-sections pullback; it does not state the derived equivalence or its derived unit/counit.

lem-sfb-derived-etale-zariski-equivalence vs def-trf-space-module-scheme-restriction: the existing definition is ordinary restriction of a space module to a scheme chart, not a derived equivalence theorem.

lem-sfb-derived-etale-zariski-equivalence vs lem-sfb-affine-etale-derived-module-realization: the existing equivalence has source D(A) and target the small-etale D_QCoh of an affine spectrum only; the new statement compares Zariski and etale D_QCoh for every scheme, with the geometric pullback comparison. Affine realization alone does not give that general scheme statement or its functor comparisons.

lem-sfb-derived-etale-zariski-equivalence vs lem-sfb-proper-flat-space-derived-base-change: the item is the specialization to one relatively flat finite-presentation sheaf under proper flat f, with Zariski direct-image and scalar coherence clauses; the new node is an independent site comparison or perfectness-detection theorem for arbitrary schemes and complexes.

lem-sfb-derived-etale-zariski-equivalence vs lem-sc-etale-tensor-sections-right-exact: the existing statement gives cokernel preservation of an ordinary lifted tensor-sections functor, not exactness on all modules together with the D_QCoh equivalence.

lem-sfb-etale-detects-perfect vs lem-sc-affine-pseudo-coherent-rhom-qcoherent: the existing theorem compares affine derived internal Hom with algebraic RHom; the new theorem concerns perfectness or perfect pushforward, not internal Hom.

lem-sfb-etale-detects-perfect vs def-pur-pseudo-coherent-complex: the existing node defines pseudo-coherent complexes; it proves neither detection of perfectness across sites nor perfectness of algebraic-space pushforwards.

lem-sfb-etale-detects-perfect vs lem-sfb-proper-flat-space-derived-base-change: the item is the specialization to one relatively flat finite-presentation sheaf under proper flat f, with Zariski direct-image and scalar coherence clauses; the new node is an independent site comparison or perfectness-detection theorem for arbitrary schemes and complexes.

lem-sfb-proper-support-tensor-perfect vs lem-sc-affine-pseudo-coherent-rhom-qcoherent: the existing theorem compares affine derived internal Hom with algebraic RHom; the new theorem concerns perfectness or perfect pushforward, not internal Hom.

lem-sfb-proper-support-tensor-perfect vs def-pur-pseudo-coherent-complex: the existing node defines pseudo-coherent complexes; it proves neither detection of perfectness across sites nor perfectness of algebraic-space pushforwards.

The scheme-only tensor theorems with different tags were also compared: `lem-sfb-proper-support-tensor-perfect` vs `lem-pc-proper-support-perfect-direct-image`: the former permits algebraic spaces X,Y; the latter is scheme-only. `lem-sfb-space-flat-complex-base-change` vs `lem-pc-rf-base-change-complex`: the former permits algebraic spaces and their small-etale derived categories; the latter is scheme/Zariski-only. No existing node supplies their algebraic-space generality.
