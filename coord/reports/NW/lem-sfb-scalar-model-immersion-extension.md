# Stage-1 delivery: lem-sfb-scalar-model-immersion-extension

Group NW, 2026-10-21. Direct-delivery worker; no other agents used.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-scalar-model-immersion-extension.json`: statement, now split into six proof steps. Not a Mathlib leaf. The statement, original source, created metadata and inherited Mathlib searches are retained. Added the actual argument, its fifteen existing dependencies, proof origin, precise blueprint place, search results and split report.
- `citations.json`: nineteen entries, one for every step/node citation; each quote was checked as a literal substring of the live node statement.
- `searches.jsonl`: produced by the required msearch command; five item searches and one auxiliary geometry grep, all actually run. The geometry grep is auxiliary evidence only, not a claim to have created a Mathlib leaf.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit file is needed: this item is a child of the blueprint node det-lem-integral-models-operations, not the unit's key node. No Lean files were written; no compiler or build command was run.

## Attachments

None. Searched the project Lean by the exact blueprint id and by scalar-model/constructibility/immersion-extension terminology. Read `WeilConjectures/SixFunctors/ProEtale/ModuleObject/LowerShriek/Constructible.lean`, especially the theorem `AlgebraicGeometry.ProEtale.CondensedRing.isConstructibleModuleObject_openImmersionLowerShriek_obj` at line 145, and read the predicates in `ConstructibleSheaf/ProEtaleModule/Def.lean` and `CategoryTheory/ModuleObjects/Free.lean`. That theorem uses arbitrary local finite presentation over the ring object, not the specified finite constant scalar presentations. It is also only the open assertion. It is therefore not an attachment for this item. No project declaration found states every clause of this item under its hypotheses.

## WANTED

None. All source passages used are available locally.

## Corrections and scope

The item was an unsplit statement with no proof. Its statement is true and unchanged. The six-step proof realizes the constructibility assertion in paragraph (3) of `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-integral-models/sk-lem-integral-models-operations.proof.md` by the finite constant local model definition in `sec-proetale-coefficients/sk-def-sfb-constructible/_section.md`. The source paragraph treats constructibility on reductions; the proof here explicitly supplies the scalar-model argument for the module statement that the parent actually cites. Proof origin is marked agent rather than pretending the full general scalar assertion is verbatim in Stacks.

The proof does not identify finite scalar-model constructibility with arbitrary local finite presentation, and does not assume derived completeness. It requires no torsion, invertibility of a prime, reducedness, finite presentation of i, or restriction to finite-type schemes over a field. The Noetherian hypothesis supplies exactly the needed source qcqs properties, constructibility of locally closed subsets, and quasi-compactness of j. The comparison between internal modules and ordinary ringed-site modules is cited as a theorem rather than inferred just from terminology.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs requiring distinction. Searched the whole DAG by the relevant notions and Stacks tags and the whole blueprint with `blueprint_refs.py search` for extension by zero, composition of immersions, 02V0, constant scalar and finite constant local model. The blueprint finite constant local model definition is reused; no other imported node states this entire precise assertion. The nearby existing lem-weil-pbc-condensed-constructible-open-closed-images and the upstream Lean theorem use the weaker arbitrary internal finite-presentation predicate, so they cannot certify retention of chosen constant scalar models. Existing lem-weil-pbc-proetale-ringed-open-closed supplies the needed identities, and the immersion-composition clause already exists in the Mathlib leaf lem-weil-pbc-proper-fp-permanence. In particular no new geometry or recollement node was introduced.

## Mathlib searches

The current searches were run with the prescribed launcher msearch command and read. LeanFinder was tried twice: first the exact finite scalar-model formulation, then preservation of constructible sheaves by locally closed extension. Results were scheme/space constructible images and preimages, Noetherian affine covers, and unrelated structure-sheaf facts; none states this coefficient-module claim. Loogle `CategoryTheory.Sheaf, "constructible"` returned no hits. LeanSearch returned functions extended by zero and unrelated linear maps, not sheaf constructibility. The grep `constructible.*(extension|pushforward)|extensionByZero` returned no hits. These exact tool/query pairs are appended to the item's inherited records; no unavailable service was counted as a negative result. An auxiliary grep found Mathlib's immersion-composition instance; the existing DAG leaf was then located and reused, not recreated.

## Review by NW

I read coord/delivery-errors.md B–E in both occurrences, the three blueprint levels in SETUP.md, GOAL.md, the worker brief, chapter sec-six-functors-basics and unit sk-lem-integral-models, and the exact current blueprint proof and constructibility definition named above. I read the statement of each of the fifteen proof dependencies. For the site identities I also read `literature/stacks-project/proetale.tex`: Tag 09AA (lemma-closed-immersion), 09BM (lemma-closed-immersion-complement-retrocompact-exact), 09BN (lemma-open-immersion), 09AG (lemma-jshriek-zero), and the statement of 09AH (lemma-ses-associated-to-open). I read properties.tex Tag 01OZ (lemma-Noetherian-topology) and schemes.tex Tag 02V0 (lemma-composition-immersion), including the open-lifting argument. There are no new-node sources to audit.

In step 1 the open-subscheme node explicitly says U is Noetherian. Clause (a) of closed-immersion-proper explicitly includes finite type, which meets the finite-type-over-Noetherian node's hypothesis with base T; this gives Noetherian Z without assuming i is of finite presentation. The locally-Noetherian-quasi-separated node applies to both resulting schemes. Together with their quasi-compactness, these are precisely the hypotheses of the qcqs clause in sk-def-sfb-constructible. This step chooses finite adapted stratifications and all scalar witnesses, without adding a finiteness hypothesis on the index of a trivializing cover.

In step 2 the minimal-closed-subset statement implies the descending-chain definition of Noetherian topology by the argument written in the step, so the compact-subsets leaf applies. The open-immersion definition supplies the homeomorphism onto the image; this proves the required quasi-compactness over each affine open, not just quasi-compactness of U as a scheme. Clause (e) of proper-fp-permanence explicitly contains composition of immersions with no properness hypothesis in that clause. It applies to each actual composite s_a;j or t_b;i. Their images, plus the complementary immersion, are disjoint and exhaustive. The definition of stratification and the Noetherian clause of constructible-subset give exactly the finite constructible locally closed stratifications needed. I did not use a false factorization-through-a-subscheme inference from containment of images.

In step 3 the ringed-open-closed statement supplies all four displayed identities and both exactness assertions. Its only additional geometric hypothesis is the quasi-compact complementary open, verified in step 2. Cartesian-coefficients gives ring identifications for these untwisted admissible coefficients without a prime-invertibility condition. Internal-module-operations-transport explicitly compares inverse/direct image, open shriek and their adjunctions under additive exact equivalences, so the ringed identities and exactness apply to the item's specified module operations. A comparison of module categories is thus a cited result, not an implicit identification. These two off-route statements are declared generic tool uses in split_report; module-pullback composition is also declared as a generic tool.

In step 4 the composition clause in module-pushforward-pullback supplies exactly the isomorphism for the composite stratum immersion. The open unit identity from step 3 then identifies the restriction with the original F on the same stratum. Pulling back this isomorphism along each original cover map retains the chosen P and its given isomorphism; there is no claim that an extension functor sends a finite free presentation to another finite free presentation. This is a few-line application of cited identities and the scalar-model definition, marked elementary.

In step 5 the complementary restriction is the zero module by step 3. The identity cover with scalar module zero has its explicit rank-zero finite presentation, and tensor with zero is zero; the matrix formulation of the local-model definition also directly gives this zero object. The new stratification therefore satisfies the constructibility definition. This is elementary and does not deserve a separate zero-model node.

In step 6 the closed counit identity from step 3 and the same cited composition statement retain every closed-side model. Its additional open restriction is zero, with the same explicit rank-zero model. Reading sk-def-sfb-constructible verifies that these witnesses prove precisely the stated constructibility, and exactness was already obtained in step 3. Thus no new node merely relabels an item clause, and the last steps do not hide an extra stability theorem.

I tested T empty, U empty, Z empty, the identity open or closed immersion, empty source strata and the zero sheaf. Empty strata can be retained or discarded without affecting the finite partition or witnesses. The zero ring and zero scalar module use rank zero throughout; no nontriviality assumption is needed. For a nonreduced closed subscheme the same closed counit applies; the proof uses the given immersion rather than replacing its scheme structure with a reduced one. The argument also permits infinite pro-etale trivializing covers and does not assume their members are Noetherian. Each proof step is under 1000 characters; no long step exceeds the 2000-character review threshold.

B: there are no new unsplit nodes, duplicate clauses, unsupported source tags or claimed leaves. C: all nineteen step citations have verbatim quotes, every external substantive assertion has a cited statement, and a read-only dependency traversal found no return path from the ringed-identity, operation-transport, composition or Cartesian-coefficient nodes to this item. D: the steps perform the actual witness construction rather than delegating preservation to a restatement. E: all uses have the hypotheses checked above, including the qcqs sources and quasi-compact open required in the pro-etale argument. No statement dispute or unresolved mathematical gap remains.

## Unfinished work

None within the one-level stage-1 split. Its existing dependencies retain their live statuses; this delivery does not claim to prove their Lean implementations.
