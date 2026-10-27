# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-zariski-etale-pseudocoherent-rhom.json`: statement item, now split; no Mathlib match. Seven steps follow the local finite-free computation of Stacks 08JP(1), including the canonical-arrow verification.
- `citations.json`: one entry per step/node citation, quoting the full existing statement verbatim so that all clauses used can be checked together.
- `searches.jsonl`: the search command's unchanged log; five searches run for this item, including two semantic phrasings. The item's earlier searches were retained.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searches under `lean/WeilConjectures/` for the blueprint id, Zariski/internal-Hom combinations and pseudo-coherent terminology found no declaration giving this item. The existing abstract monoidal Hom comparisons and coefficient-site comparisons concern other objects and do not give this structure-sheaf comparison.

## WANTED

None. The source and all supporting Stacks passages are available locally.

## Corrections and findings

The sandbox was empty on resumption (only dispatcher marker files). No delivery or search process for this item was still running. I copied the live unsplit item and retained its complete statement, source, original searches, creation record and blueprint ancestry. No statement correction was needed. In particular the conclusion concerns ordinary module-sheaf derived categories and does not require quasi-coherence of the second argument.

The finite products in the proof are finite because the source complex is bounded above and the target complex is bounded below. Exact pullback is never asserted to preserve arbitrary products or K-injective complexes. Instead the proof uses a new K-injective replacement on the etale site. The existing ringed-site augmentation lemma explicitly permits that replacement to be unbounded, which is essential for matching the fixed comparison in the item's statement.

The current blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md` were read together with the chapter and unit records. This item is a supporting ringed-site tool deep below the recorded direct-image route. No unit or chapter route was changed. The pre-existing `blueprint.from.node = null` was retained: `tools/blueprint_refs.py ancestor` reports that same value. The detailed existing place already locates the affine Hom comparison. `split_report.blueprint` explains which argument is realized.

## Not duplicates

No new nodes were created. Whole-DAG searches for 08JP, 08JI, the source labels, bounded-above finite-free models and derived internal Hom found the existing ringed-site Hom model and arbitrary K-injective augmentation nodes; these are cited rather than recreated. Whole-blueprint searches for 08JP and 08JI returned no imported nodes. A broader RHom search was also read. The ring flat-base-change node `lem-trf-pseudocoherent-rhom-flat-base-change` concerns module derived categories over rings, not arbitrary structure-module sheaves; it was not substituted for this item. The finite-free ring-extension comparison `lem-sf-ringed-finite-free-hom-base-change` assumes that the extension ring is finite free on the same site, and does not apply to epsilon.

## Mathlib search reading

The Q86 log contains exactly the searches added to the node. LeanFinder's first phrasing returned scheme module pullback/adjunction and etale categorical pullback declarations. Its second phrasing returned flat scheme morphism and site-continuity lemmas. Loogle returned categorical pullback congruences and related Hom names. LeanSearch returned ordinary sheaf/module pullback, its composition and preservation of finite limits. The grep returned zero hits for derived/internal Hom combined with etale or Zariski. I read `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` at lines 183–199 and `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` at lines 45–68: these define ordinary pullback and its adjunction, not this derived comparison. None is an exact match or one-line specialization. No service was unavailable and no search was invented.

## Review by Q86

I read `spaces-perfect.tex`, Tag 08JP, label `lemma-descend-RHom`, statement and proof of case (1), and Tag 08H8, `lemma-epsilon-flat`. The source assumes a scheme, pseudo-coherent first argument and cohomologically bounded-below second argument; these are exactly the item's assumptions. I also read `sites-cohomology.tex`, Tag 08JI, `lemma-Rhom-complex-of-direct-summands-finite-free`, Tag 08JF, `remark-prepare-fancy-base-change`, Tag 0A95, `lemma-RHom-well-defined`, and Tag 08JB, `lemma-restriction-RHom-to-U`. The ringed-space version 08I5 in `cohomology.tex` and 08EE in `perfect.tex` were checked; the proof actually uses the existing general ringed-site 08JI node and the local finite-free definition, so it needs no new affine-lifting lemma. There are no new-node statements to review.

Step 1 uses the exactness on **all** modules explicitly stated by `lem-sfb-derived-etale-zariski-equivalence`, not merely its quasi-coherent equivalence. The Hom differential and componentwise functoriality are precisely those of `def-pur-hom-complex`. `def-pur-derived-internal-hom` states functorial K-injective replacement, independence of representatives and inversion of quasi-isomorphisms; `def-weil-abstract-derived-category` states the localization used to descend the transformation. The displayed differential calculation verifies the chain-map condition. It proves naturality for arbitrary chain maps and hence for their localizations, rather than choosing bases to assert naturality.

Step 2 uses the explicit arbitrary-object restriction clause of `lem-weil-pbc-ringed-internal-hom-exact-restriction`. The comparison square node says pullback commutes with scheme pullback for **every** Zariski module without quasi-coherence; applying it to an open immersion gives the required restriction comparison. `lem-pur-kinjective-restrict-localized` states K-injectivity after restriction, so the construction really restricts. The representative-independence clause of the internal-Hom definition then allows local fixed replacements. Detecting an isomorphism of sheaves on a cover is the elementary sheaf gluing argument, not an extra cohomological comparison theorem.

Step 3 takes its bounded-above finite-free representative locally directly from the statement of `def-pur-pseudo-coherent-complex`. No global free resolution on an arbitrary scheme is assumed. I wrote the good lower truncation, including its degree-a cokernel and its quasi-isomorphism test, explicitly. Exact pullback preserves the bound and the quasi-isomorphism; scalar extension sends the structure module to the structure module. There is no coherence hypothesis on this truncated target. The arbitrary-module pullback formula is in the comparison square node, cited here.

Step 4 applies `lem-weil-pbc-ringed-site-bounded-free-rhom-model` to both sites. That statement has precisely a bounded-above source with terms retracts of finite free modules and a bounded-below target; a free term is its own retract. It supplies the derived object identification, the finite interval a-n <= p <= b and the signed differential. Thus I did not cite a ringed-space-only result on the etale site.

Step 5 is elementary from the sheaf-Hom definition and exact additive module pullback: basis evaluation identifies the Hom sheaf with a finite sum, and the pullback comparison is the identity on its coordinates. The degreewise calculation is finite and its signs agree with the Hom-complex differential. This is a step, not a new node duplicating a finite-free fact.

Step 6 uses the statement of `lem-weil-pbc-ringed-site-bounded-free-rhom-quasi-iso`, not an argument hidden in its proof. Its target I is explicitly allowed to be unbounded; this covers both the fixed Zariski replacement and the fixed etale replacement of the pullback of that replacement. Exactness of epsilon makes j composed with Ti a quasi-isomorphism. I wrote all four arrows of the commuting square and checked commutativity by composition on every component. The upper map is the finite-free isomorphism; both vertical maps are the canonical replacement identifications, so the lower map is exactly the map specified in the item and is invertible. This repairs the common gap of producing an abstract isomorphism without proving invertibility of the specified canonical arrow.

Step 7 only glues the local cohomology-sheaf isomorphisms and uses localization at quasi-isomorphisms. It adds no hypothesis. The non-elementary tools from other units are explicitly declared in `split_report.tool_uses`; they are generic ringed-site tools, not replacements of the constructibility route.

I checked B1–B10 against the files: no new nodes, no hidden proof inside a new statement, no invented leaf, no source or maintainer-field edits, and original search records retained. For C1–C8, every substantive computation, restriction and replacement is the statement of an existing cited node; every such statement was opened, and citations.json quotes it verbatim. I checked that none of the cited nodes has a transitive statement/proof dependency back to the item. For D1–D5 the seven steps carry the argument itself and no new node restates a clause. For E1–E7 I checked both bounds, ringed site rather than just space, arbitrary target modules, no Noetherian assumption, and the exact four arrows defining the canonical map. Small cases checked were an empty scheme, K or L zero, a rank-zero free term, an empty interval a-n > b, a rank-one free source in a single degree (the comparison is the identity on the shifted pulled-back target), a complex with infinitely many negative source degrees (each fixed total degree is still finite), and a non-quasi-coherent target sheaf. No case forces a missing assumption. All step texts are below 2000 characters.

## Unfinished work

None in this stage-1 split. Existing unsplit dependency nodes remain the existing work queue; this delivery does not claim Lean proofs or compiles.
