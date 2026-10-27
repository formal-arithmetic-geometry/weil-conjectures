# Stage-1 delivery: lem-sfb-stable-relative-picard-kummer

Files written, all under this sandbox's `dag/nodes/sec-six-functors-basics/`:

- `lem-sfb-stable-relative-picard-kummer.json`: item, statement, split into ten steps; statement retained; no Mathlib match.
- `lem-sfb-picard-space-curves-smooth.json`: statement-only input, unsplit; no Mathlib match.
- `lem-sfb-nodal-multidegree-zero-locus.json`: statement-only input, unsplit; no Mathlib match.
- `lem-sfb-nodal-normalization-picard-sequence.json`: statement-only input, unsplit; no Mathlib match.
- `lem-sfb-smooth-group-invertible-multiplication.json`: statement-only input, unsplit; no Mathlib match.
- `lem-sfb-connected-proper-fibres-proper.json`: statement-only input, unsplit; no Mathlib match.
- `lem-sfb-stable-picard-theta-ampleness.json`: statement-only input, unsplit; no Mathlib match.

Also written: this report, `citations.json` (one entry per step/cited node, copying its statement verbatim), the search logs and local preparation scripts. Six new nodes, zero Mathlib leaves. No Lean files, library builds, repository writes or repository git commands.

Attachments: none. Searching the item blueprint tag and relative-Picard, multidegree and semiabelian terminology in the project Lean source found no complete declaration for this claim. Smooth-curve Picard/Jacobian declarations over a field do not supply this relative, singular-fibre statement.

WANTED: `literature/deligne-le-lemme-de-gabber_Asterisque-127-1985.pdf`, Sections 1.1, 2, 3.3--3.5 and 4.1--4.3 (printed pp.131--142), for the item and the multidegree-locus, proper-fibres and theta-ampleness inputs. The local PDF is absent; I read the primary Numdam PDF at https://numdam.org/item/AST_1985__127__131_0.pdf online without downloading it. The item's proof is accordingly marked agent-written, with the Stacks inputs and the missing local source identified. The report does not claim that EGA III-1 Section 5.5 was read directly: Deligne 1.1 explicitly invokes it.

The seeded item was unsplit, not a statement error. Its source pointer to Sections 3.3--3.5 explains why Picard torsion is used for levels but does not itself construct the relative Picard space; the multidegree construction is in Section 2, printed p.135. I retained the statement and added the actual construction, scheme representability and the specified Kummer map. In particular the proof does not assume a universal line bundle on the whole relative Picard space. Nor does it claim finite etale torsion over the singular locus. I corrected a local TeX newline conversion that had changed normalization symbols, and replaced imprecise chart language for properness with the diagonal/universal-closedness definitions: properness is not etale local on the source.

Unfinished work: the six new inputs are intentionally unsplit, as required by a one-level split. Their proofs are future work, not hidden proofs of this item. No other mathematical clause of the item is deferred except through those explicitly named inputs. Delivery validation is recorded below.

## Blueprint and searches

I read the chapter and `sk-thm-sf-ctf-stability` unit. This is the relative Picard prerequisite for the prime-to-characteristic level comparison in the stable pointed-curve extension route under `det-thm-sf-ctf-stability-direct-images`, proof (3). It does not replace alteration by a different route. The live seeded chain has `blueprint.from.node = null`, and the ancestor command returns `None`; I preserved that inherited anchor, its precise proof-(3) place, and the complete `via` chain. Each new node prepends the item to that chain and states its particular role in `from.place`. There is no unit-realization edit: this item is not the unit's key theorem.

Whole-DAG statement/source searches and whole-blueprint searches covered relative Picard, Picard functor, Kummer sequence, multidegree, semiabelian, normalization Picard, normalization of a curve, proper connected fibres, theta bundle, Picard space and invertible multiplication. Smooth-curve field Picard nodes are reused; they do not provide families over possibly nonreduced bases or nodal gluing. No equivalent blueprint statement was found, so `same_as` is empty. The source-tag overlaps are distinguished below.

For each of the six new nodes I ran leanfinder and leansearch with different plain-language phrasings, a Loogle name pattern and a Mathlib grep, using the mandatory `msearch.py` command. The four results for each are copied exactly into its `mathlib_searches`; queries and results are also in `search-results.json` and `searches.jsonl`. All four services ran. The hits are smooth-morphism instances, ordinary scheme normalization, abstract categorical objects or Weierstrass-coordinate Jacobians, not these relative Picard/group-space statements. The item's additional four searches, recorded separately in `item-search-results.json` and in the item, return arithmetic roots of unity, Selmer groups and Weierstrass coordinates. They do not state the relative sheaf comparison. Existing seeded item search records are retained. I inspected the hit types rather than inferring absence from an empty service response.

## Not duplicates

lem-sfb-nodal-normalization-picard-sequence vs lem-pc-nonzero-section-integral-cartier: the latter constructs the effective Cartier zero scheme of a nonzero section on an integral scheme; it has no nodal normalization or Picard gluing exact sequence.

lem-sfb-nodal-normalization-picard-sequence vs lem-sc-hilb-to-pic-morphism: the latter constructs the degree-d Hilbert-to-Picard morphism for a smooth projective curve; it does not identify the kernel of pullback through a singular curve's normalization.

lem-sfb-nodal-normalization-picard-sequence vs lem-sc-hilb-to-pic-surjective: the latter proves surjectivity of that smooth-curve divisor morphism in high degree; it does not concern normalization, node gluing or the fppf kernel sequence.

lem-sfb-nodal-normalization-picard-sequence vs lem-sc-picg-geometrically-integral: the latter concerns geometric integrality of degree-g Picard for a smooth geometrically integral curve; it has no reducible nodal curve or graph torus.

lem-sfb-nodal-normalization-picard-sequence vs sk-thm-picard-main: the latter gives Picard varieties and degree components for a smooth proper connected curve over a field. It supplies the normalization components' Jacobians, but no exact sequence of relative fppf Picard sheaves for the singular curve.

lem-sfb-nodal-normalization-picard-sequence vs thm-sc-theorem-of-the-base: the latter gives the degree decomposition and proper degree-zero Picard scheme of a smooth projective geometrically integral curve. The new node concerns node gluing, including all test schemes and reducible nodal curves.

lem-sfb-smooth-group-invertible-multiplication vs lem-sc-mult-n-etale-kernel: the latter assumes an abelian variety over a field and concludes a finite kernel of a specified order. The new node allows arbitrary bases and smooth commutative group algebraic spaces, including tori and nonproper groups; it concludes etaleness without finiteness. An abelian-variety specialization cannot supply that general assertion.

## Review by N9

I checked delivery-errors B through E against the source texts and the completed node files. This is my direct-delivery self-review; no second reader or sub-agent was used.

For the source of each new input, I read Stacks `quot.tex` Tags 0D2C and 0D2D and `moduli.tex` Tags 0DNI and 0DPK for relative Picard representability, its diagonal and smoothness. Their hypotheses are proper, flat, finitely presented with universal structure-sheaf pushforward; the curve smoothness result requires fibre dimension at most one, not a smooth family. Deligne Section 2 provides the open, bounded, separated multidegree-zero subspace; the new locus node deliberately does not simply assert all the item's identity-component, connectedness and semiabelian conclusions. I read the units sequence and both component cases in Stacks `curves.tex` Tag 0C1M, together with `pic.tex` Tag 0BA0 for the normalization Jacobians. Tag 0C1M itself is an exact sequence of ordinary Picard groups: the new node explicitly formulates the stronger fppf-functor gluing statement as agent work, not as a quotation of that tag. Its future proof glues invertible modules along the two branches, trivializes their branch fibres fppf locally on the test scheme, and quotients the gluing parameters by the component units; thus it must hold for all test schemes, including nonreduced ones. The step in this item only computes that already-stated cokernel by a spanning tree.

For invertible multiplication, I checked Stacks Tags 0BF5 and 0BFH. The latter has proper abelian-variety hypotheses; the new smooth-group-space formulation is an agent generalization, not a claim that the tag already states it. Its infinitesimal argument is that two lifts differ by a Lie-algebra section tensored with the square-zero ideal, multiplication by n acts as the unit n there, and there is a unique correction to any smooth lift. This gives formal etaleness and then etaleness using local finite presentation, and the kernel is its pullback. Deligne 1.1 supplies the separate properness criterion; I included nonempty fibres, so an open immersion omitting a fibre cannot pass its hypotheses. Deligne 4.1--4.3 supplies the normalized relatively ample line module and scheme representability. The ample module is extra geometric data, rather than an auxiliary node merely restating “the smooth restriction is an abelian scheme.” No forbidden SGA source is used.

I opened every statement cited by the item's steps, and `citations.json` records its actual wording. Here is the hypothesis and citation audit:

1. The stable-curve definition gives projective-bundle, flat, finitely presented and nonempty geometrically reduced connected fibres. `lem-trf-projective-bundle-proper` gives properness in exactly that convention. `lem-sc-proper-flat-global-sections` then applies after arbitrary base change, not just over a reduced base. Taking units of an isomorphism of rings is elementary.
2. The first new node gives P; `sk-def-picard-pic` specifies its quotient/sheafification functor. The locus node supplies openness, quasi-compactness and separation, rather than inferring them from a definition of Picard. Open restriction preserves smoothness and local finite presentation; quasi-compact plus quasi-separated upgrades this to finite presentation. This step has not assumed connected fibres.
3. The normalization input explicitly gives a smooth surjective open Q-torsor onto the product abelian variety. The connected dual graph has a spanning tree, including in the single-vertex/loop case. Setting tree-edge parameters to 1 computes the cokernel functor, with one parameter for each remaining edge. A torus torsor has connected geometric fibres; openness and connectedness of B justify the clopen-partition argument. Cosets of the open subgroup then identify it with the neutral component. These arguments remain in the item instead of creating nodes for elementary graph bookkeeping.
4. `lem-pd-picard-base-change` states relative Picard base change for an arbitrary morphism, not just extension of fields. The locus node defines its subfunctor by all geometric test fibres; that condition restricts literally to the same test objects after base change. The same line-module pullback gives family-isomorphism naturality. No representability-by-a-universal-line-bundle assumption occurs.
5. `sk-thm-picard-main` applies to the smooth proper connected geometric fibres on V and gives proper connected abelian varieties. The theta input first makes the relative group a scheme. Only then does the flat separated finite-presentation proper-fibre criterion prove properness over V. This prevents conflating an abelian algebraic space with the requested abelian scheme.
6. The multiplication input needs only smoothness, commutativity and invertibility of n, all already available. Its kernel is etale over S but is used as an etale scheme only over V, where scheme representability was proved.
7. `lem-amb-kummer-any-base` gives Kummer exactness on every total space X_U. The cohomology long-exact-ladder node applies on arbitrary schemes, so no H2-vanishing or affine-curve hypothesis is smuggled in. `thm-sc-hilbert-90` gives the Picard identification by its explicit torsor formula. Integer degrees of an n-torsion line module vanish on each component. The multidegree criterion factors into N[n]; `sbc-lem-higher-direct-image-presheaf` gives precisely the sheafification needed to construct kappa, not only an abstract isomorphism of stalks.
8. The existing `cor-weil-pbc-geometric-fiber-finite` explicitly supplies degree-q stalk base change for finite module sheaves; mu_n is a finite Z/n-module sheaf since n is invertible. `lem-galois-stalk-representable` requires an etale scheme and is applied only to N_V[n]. Global units on the geometric curve come from the universal structure-sheaf theorem, and nth powers are surjective in the algebraically closed field. The same Kummer and Hilbert-90 statements give Pic[n]; the geometric Picard degree decomposition gives Pic0[n]. The enough-geometric-stalks node then detects the isomorphism. No per-degree theorem is silently substituted for a derived theorem.
9. The cohomology-pullback node explicitly gives naturality in coefficients and composition. The Hilbert-90 torsor formula identifies that pullback with the line-module pullback used by relative Picard base change. The higher-direct-image presheaf statement permits sheafification of this equality. For arbitrary base change, `thm-weil-pbc-bounded-below` supplies derived exchange, `sk-thm-iff` already states its cohomology-sheaf consequence, and `lem-kun-bc-map-on-cohomology` identifies the map with the usual injective-resolution base-change map. These extra existing citations correct the initial temptation to use the derived theorem directly as a degree-one comparison. They establish the specified map, not a freely chosen isomorphism.
10. The empty base is handled separately. If S is nonempty, the map from k into a residue field shows that n is prime to its characteristic. `lem-sc-primitive-root` then supplies the primitive root over k. Its distinct powers have unit pairwise differences on every k-scheme; the displayed polynomial factorization and Chinese remainder argument give the constant-sheaf trivialization with the stated formula, hence pullback compatibility.

Small-case tests: for a smooth fibre the graph has one vertex and no edges, so the torus is trivial and the construction recovers the Jacobian. For a compact-type reducible fibre the graph is a tree, again giving no torus. A loop contributes one multiplicative parameter, and rational normalization components contribute trivial Jacobians. In a nodal degeneration the torus rank can increase and n-torsion rank can drop, explaining why no finite-etale conclusion across the boundary was added. At n=1 both Kummer torsion and the cyclic sheaf are trivial. For empty S, invertibility is vacuous, so the final step treats its unique sheaves directly instead of inferring the existence of a primitive root in k. Empty V makes only the smooth-locus assertions vacuous. Nonreduced bases are covered by the universal pushforward and test-scheme formulations, not discarded.

All ten proof steps are below 2000 characters; none conceals an additional comparison or standard non-elementary lemma inside a long step. The six inputs are genuine general geometry/gluing results after DAG and Mathlib searches, not newly named repetitions of the complete item or elementary line-module manipulations. I checked JSON/TeX, dependency unions, the statement-only status of the new inputs and the literal citation quotes. The preliminary remote `review_split` passed. The full delivery dry run also passed at fe2177305d7; the final empty-base clarification is checked again before pushing.

## Repair of returned delivery

The prior landing was rejected because the side completion was not promoted into the live DAG. I rebased the retained split against the current live DAG by comparing every sandbox node with its live counterpart. The item remains unsplit in the live DAG, while the six statement-only dependencies remain new delivery nodes; no live dependency node superseded any of them. I re-read the live statements of every existing node cited by the ten proof steps (including the stable-curve definition, projective properness, universal structure-sheaf pushforward, Picard base change and theorem, Kummer, cohomology, stalk, proper-base-change, and primitive-root nodes). Their hypotheses and quoted sentences are unchanged and still match `citations.json`; no proof step or dependency quote required adjustment. The retained split, searches, citations, and source review are therefore rebased onto the current origin and are being dry-run again before push.

## Current-DAG repair audit (returned head 094f94753d8)

The current return entry in `coord/returns/N9.md` identifies branch head `094f94753d8` (2026-10-22 12:09 UTC). I continued the retained delivered sandbox rather than regenerating its proof or searches. The first required dry run exited successfully at `95afcd247cc`. The delivery tool fetches `origin/sheaf-dag`, constructs a new commit on that current base and overlays only stage-1-owned fields of existing nodes; this is the integration repair requested by L. In the current read clone the item remains `unsplit`, its statement and inherited blueprint fields agree with the retained item, and all six new ids remain absent. No released stage-1 repair note exists for the item.

I re-read the current statements used by all ten steps. All 34 recorded citation quotes remain literal substrings, and the set of (step, node) entries is exactly the set of proof citations. In particular the proper-base-change inputs still provide the finite-coefficient geometric-stalk formula and the identification of the degree-one exchange map; the relative Picard base-change input still permits arbitrary base morphisms. The current stable-family definition still supplies the proper-flat, reduced-connected nodal hypotheses through projective-bundle properness. No citation or mathematical step needs replacing. The split report now explicitly records this returned-head repair.

I also reopened Stacks `quot.tex` 0D2C/0D2D, `moduli.tex` 0DNI/0DPK, `curves.tex` 0C1M, `groupoids.tex` 0BF5/0BFH and `pic.tex` 0BA0. I re-read Deligne 1.1, Section 2 and 4.1--4.3 in the [primary Numdam PDF](https://numdam.org/item/AST_1985__127__131_0.pdf). Their uses remain exactly those described in Review by N9 above; the normalization functor and group-space multiplication assertions remain explicitly agent generalizations, not claims that those tags state more than they do. I read the retained search results and their logged queries; their questions and statements have not changed, so I reused them. The project Lean search still finds no declaration covering the relative singular-family assertion.

The current live proof-dependency statements are fingerprinted below (SHA-256 of the UTF-8 statement). This records exactly which dependency versions were checked for this repair.

- `cor-weil-pbc-geometric-fiber-finite`: `0797ae104b6c05f9a97d0536da7939f083101e4f163fa4bf93b322155396f09a`

- `def-sfb-stable-pointed-curve`: `ecbee07e45d27763d21f45794a0fd5b84b4baf526cf5607c7d5faf6709366f4b`

- `lem-amb-kummer-any-base`: `06e44d3d69baf8bf23b16b9159b9bbbcec6963a6799ad560c9b16a076f731fc1`

- `lem-galois-stalk-representable`: `1b786a6d20526bdb57033a1321bd266d5be74b27415bd78c5982fe20981fc8d6`

- `lem-kun-bc-map-on-cohomology`: `2c7801da1015dece091edc85ed969a5fefa389a53fac88ae250a2c2305de9206`

- `lem-pd-picard-base-change`: `2e85bb3db64eefc1c3355fe6801eb4e6cd686dbb1af9ec51e7ba3074e5fcfee6`

- `lem-sc-primitive-root`: `edfa54d25f326215764017b6552e6fed1c8b0a688f0fdbc21a453ab044fa5fdc`

- `lem-sc-proper-flat-global-sections`: `55f0e58d78b641e4c3fbeb979eb4fc8bec95cc54bc0e6fb24458f2ddc05ea398`

- `lem-trf-projective-bundle-proper`: `235e2bad6f311ba5520b638504585e13268e81095d65099260801a6dc8c6af22`

- `lem-weil-pbc-cohomology-pullback-functorial`: `36651bd074d35f99b5cdbad85cdbfcc85cac3dc264a43e7c2f33048e9a1d54b0`

- `lem-weil-pbc-pullback-cohomology-long-exact-ladder`: `75e2473502313dedf18c061c0291da5211d2936cf2dbb19b6405145bf117a39c`

- `lem-weil-pbc-sets-etale-iso-on-geometric-stalks`: `b074d9e3d9dbebff46044d0e590e08fe2ab7d14b347167063c1856be59c68c5f`

- `sbc-lem-higher-direct-image-presheaf`: `bd92c481b55a841ea3e8c6edd33a357991777167a6ef037d5e884b37e847ee11`

- `sk-def-picard-pic`: `3beae01f6a06fa5079da798496dc77ad75f19d253f469b54ebda3bc7e905904e`

- `sk-thm-iff`: `7525963b8335bf558fd15af0912b7e55bb2e137e4ced0da8fd75a1c79217eb65`

- `sk-thm-picard-main`: `68871c41481e1190bbcefe8e0da11b3c088fe50d40a6417ccc0fbb2e04037cae`

- `thm-sc-hilbert-90`: `e82c4f1abb187ce1bbc1608518001161ab8ee0ccf6c0b7e511143fdc72a0e147`

- `thm-weil-pbc-bounded-below`: `3be20fd1b5ba03b88aa15695aa7caeac7d6fddca74ad5944859655eaa6b1a1ec`


The final dry run and push are performed after this audit; only the sandbox node and report were changed in this repair. Existing citations and search logs are retained.


## Repair audit for returned head 6a0bf15ff4a (2026-10-23)

This continues the retained delivery returned on 2026-10-22 at 16:18 UTC, not the older return discussed above. L approved its mathematics but refused landing because the side completion had not been promoted to the live DAG. The required first dry run has now passed on the freshly fetched delivery base at `ac34eaa016f`. The delivery command performs the rebase onto the current server DAG; I have not run git in the shared read clone. I updated the item's split report and this repair record for this actual return. The proof, source references, six inputs, citations and logged searches are retained.

I compared every sandbox node with the current read clone. The item remains unsplit; its statement, source and inherited blueprint fields agree with the sandbox. The only differing fields are the intended stage-1 split fields: proof, proof dependencies, statement dependencies, proof origin, searches, status and split report. All six auxiliary ids are still absent, and no repair note reopens or supersedes the item. All 18 existing proof-dependency statements have exactly the fingerprints recorded in the preceding audit: there is no changed cited statement requiring a replacement step. I nevertheless read their full current statements again. The 34 literal quotes remain valid and form exactly the set of step/node citations; the dependency union is exact. Each of the ten steps remains below 2000 characters.

For steps 1--4, the current statements still give universal structure-sheaf pushforward, relative Picard representability and its actual sheafification functor, the multidegree locus, normalization torsor and arbitrary Picard base change. For steps 5--6, the retained ample-line-module input supplies scheme representability before the proper-fibre criterion is applied, and invertible multiplication needs only the smooth commutative group hypotheses already established. For steps 7--9, I rechecked Kummer exactness on every test total space, the precise Hilbert-90 torsor identification, the sheafified higher-direct-image presheaf, finite-coefficient stalk base change and the specified cohomology exchange map. Step 10 still separates the empty base before using invertibility to choose a primitive root. Thus no hypothesis was silently strengthened during the rebase.

I reopened the cited Stacks statements and Deligne's primary Numdam PDF, Sections 1.1, 2 and 4.1--4.3. The two agent generalizations remain marked as such. I reread the retained Mathlib result records and their query log rather than rerunning unchanged search questions. The current project Lean search has no relative singular-family Picard declaration: the nearby ConstantKummerNaturality and AffineKummerDegreeOneBaseChange declarations concern smooth curves over fields and do not attach this item. Whole-blueprint searches for relative Picard, multidegree and invertible multiplication found no replacement for a new input. The previously checked smooth, tree, loop, n=1, empty-base and nonreduced-base cases remain unchanged. The final dry run and push below use this updated repair record.
