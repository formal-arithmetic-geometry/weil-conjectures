# Stage-1 worker report: sk-def-sfb-constructible

## Files written

- `dag/nodes/sec-proetale-coefficients/sk-def-sfb-constructible.json`: existing definition split, statement preserved verbatim; no new nodes and no new Mathlib leaves.
- `citations.json`: ten verbatim statement excerpts, one for every step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's actual log; `repair_split.py` is the sandbox-local editing script, not a delivery file.

## Attachments

None. I searched the entire slopmaster2 `WeilConjectures/` tree for the item tag and the three advertised declaration names, and read `WeilConjectures/SixFunctors/ProEtale/ConstructibleSheaf.lean:59–75` and `:189–195`. `AlgebraicGeometry.ProEtale.IsConstructible` uses sheaves valued in modules over an ordinary ring and local models of finite underlying cardinality. Here the coefficients are arbitrary condensed ring objects and the models are finitely presented scalar modules. Even for a discrete scalar ring, finite underlying cardinality and finite presentation differ (over Z, Z itself is finitely presented and infinite). The declaration also omits the derived-category and Tor-amplitude clauses. The later comparison theorem has a literal `sorry` and supplies no attachment.

For comparison only, upstream master `CategoryTheory/ModuleObjects/Free.lean:48` defines the abstract finite-presentation predicate, and `ConstructibleSheaf/ProEtaleModule/Def.lean:69,87` defines the weaker local-finite-presentation/constructibility predicates. These are reference material, not evidence that this item is finished.

## WANTED

None. The item is itself the blueprint's definition, so its primary source is the current main-20261015 blueprint. No unavailable external proof is asserted.

## What was wrong and what changed

I read the chapter `_section.md`, the item's `_section.md`, its two proof paragraphs, the local-model statement and proof, and the Tor-amplitude detail statement. This newly imported item has no `chapter`/`unit` binding and no corresponding chapter/unit JSON record in the shared tree. I used the available chapter and key-node blueprint documents without manufacturing or modifying metadata.

The imported proof identifies the displayed notion with `def-sfb-constructible-module`, which imposes local finite presentation rather than finite constant local models. Its own detail node explicitly says the converse from local finite presentation fails in general. Thus that identification does not follow. The revised split keeps the item's definition exactly, including scalar matrices and constructible stratum images, and cites the existing local-model equivalence. It does not change any target or coefficient category. No statement correction is needed.

The earlier sandbox attempt added `sk-def-sfb-bounded-constructible` as a statement dependency and cited `det-def-sfb-constructible-tor-amplitude` in the proof. Both introduce a cycle: the first depends on this item, and the second depends on the first. The bounded/Tor subcategories are now defined directly by their displayed predicates using the existing ambient derived-category and relative derived-tensor constructions. The statement's parenthetical comparisons remain comparisons, not dependency edges. This does not assert their triangulatedness, thickness or any other theorem stated in those other nodes.

The earlier report and citations also attributed an abelianness sentence to `sk-def-sfb-derived-categories` that is absent from its current statement. The source's actual abelianness lemma is `lem-sfb-modobj-abelian`; it was located and read. The revised definition does not need a separate general abelianness argument: its matrix equivalence is supplied by the already existing `det-def-sfb-constructible-local-model`, while the derived ambient category is supplied by its actual definition node. All old citation quotes were regenerated from the statements actually used.

The stale `sk-def-sfb-finite-pushforward-pullback` reference is replaced in this item's argument by the current `sk-def-sfb-module-pushforward-pullback`. I added the coefficient-isomorphism lemma so that well-typed restriction is not inferred from the coefficient definition alone.

## Mathlib and duplicate searches

All Mathlib searches were run with the required `msearch.py NY sk-def-sfb-constructible` command and are recorded with their actual query strings in the item. I reran LeanFinder, Loogle, grep and LeanSearch, then tried a second semantic phrasing and a targeted sheaf-of-modules grep. The inherited search log also contains the earlier four queries; their entries are retained as actual searches, including Loogle's unknown-identifier response rather than claiming a successful type match.

I read the candidates in `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:263–275` and `Mathlib/Condensed/Module.lean:37–45`. `SheafOfModules.IsFinitePresentation` allows arbitrary coefficient-sheaf local presentations; it neither requires scalar matrices nor supplies constructible stratifications or the derived subcategories. `CondensedMod` concerns a fixed ordinary scalar ring and the coherent site of compact Hausdorff spaces, rather than this item's category of module objects over a pulled-back condensed ring on a scheme. Neither is a one-line specialization of the entire item. The second LeanFinder phrasing returned those predicates and locally-constant module functors, without the complete definition.

Whole-DAG keyword searches and `tools/blueprint_refs.py search` were run for finite constant local models, Tor amplitude, constructible subsets and the item's title. The local-model node is reused; the Tor-amplitude detail is recognized but cannot be a dependency of its own defining ancestor. No other blueprint node states the entire item, so `blueprint.same_as` is empty. No new nodes were created, hence there are no new/existing duplicate pairs to distinguish.

## Review by NY

I checked the actual main-20261015 definition and both proof paragraphs, rather than accepting the imported dependencies. The four revised steps account for every clause: restriction, scalar local models and matrices, constructible strata, and the three full subcategories with Tor amplitude. Here is what each citation supplies.

Step 1 uses `sk-def-sfb-pulled-back-coefficients` for the formula Λ_X = p_X*Λ; `lem-sfb-alpha-iso` for the coefficient comparison being an isomorphism for **any** condensed ring and **any** scheme morphism; `sk-def-sfb-module-pushforward-pullback` for the actual module pullback and its codomain; and `sk-def-sfb-transport` for mapMod along the underlying monoidal inverse image. Each of those statements was opened. In particular I did not apply a theorem confined to the listed admissible adic rings, and did not confuse the inverse image on abelian sheaves with extension of scalars on module objects. No immersion, finiteness or Noetherian hypothesis is required here.

Step 2 uses `def-sfb-finitely-presented-module` only for the finite-cokernel presentation, specialized to ordinary scalar modules in Ab, and `det-def-sfb-constructible-local-model` for its explicitly stated scalar map, relative tensor notation and equivalence (1)–(2). I read the detail's proof: it takes a scalar presentation, passes to constant sheaves and extends scalars; conversely it takes the cokernel of the same scalar matrix. The fixed scalar entries are essential. The cited node states the equivalence for exactly the cover in question, so the step does not extract an unrecorded construction from its proof. The abstract locally-finitely-presented definition and generic constructible-module predicate are not substituted for this stronger local-model definition.

Step 3 reads `def-constructible-stratification` as a finite disjoint locally closed partition with immersion data. That node alone does not require constructible images, so I separately use `def-weil-constructible-subset` and retain the item's extra condition. I checked `literature/stacks-project/topology.tex`, Tag 005G (`definition-constructible`), Tag 005H (`lemma-constructible`) and Tag 005L (`lemma-constructible-Noetherian-space`). The last is exactly the Noetherian finite-union characterization stated by the cited node and used for the single-stratum remark. For general qcqs schemes I did not assume every locally closed subset constructible. The affine-local prescription for arbitrary schemes is the definition written by the source, not an unproved gluing or locality theorem.

Step 4 uses the actual layer-B row of `sk-def-sfb-derived-categories` for D(Mod_{Λ_X}) and the actual layer-B clause of `sk-def-sfb-derived-tensor-hom` for the relative derived tensor. I opened both statements and quoted those portions. It then selects objects by the displayed predicates, retaining ambient morphisms, which is an elementary construction of a full subcategory. The test objects for Tor amplitude are **all sheaves of Λ_X-modules**, concentrated in degree zero; they are not restricted to constant, flat or constructible test sheaves. Boundedness means one finite interval for each complex. No completeness or Noetherian hypothesis is inserted, and no thick/triangulated subcategory theorem is claimed.

I checked the empty scheme (empty partition and vacuous local data), the zero module (zero scalar finite presentation), scalar free modules of arbitrary finite rank (identity cover), and the zero complex (Tor amplitude in every nonempty interval). The possibility of unbounded scalar-module projective dimension explains why finite Tor amplitude remains an additional condition for a general condensed ring. The finite-cardinality Z example above also prevents a false attachment. There are no new statements requiring further small-case tests.

Against B–E: there are no new-node placeholders or duplicates; the only edited node's statement is verbatim from the source. Every non-elementary fact in these steps is a stated clause of a cited existing node; step 4's predicate selection is elementary. The ten quotes are exact statement substrings, not proof excerpts. I checked the dependency paths and removed both backward references responsible for the earlier cycle. All original import and blueprint metadata is preserved. No SGA source, Lean edit, compiler or build was used.

## What could not be finished

Nothing remains in the proposed one-level split. The required dry run is run after this report; a fresh second reader must review and deliver it. No delivery is pushed by this worker.

## Second reading by NY

- Item statement: checked against `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-constructible/_section.md` (node order 744), clause by clause; the restriction convention, finite constant local models, constructible stratification, `Cons`, `Dbc`, Tor-amplitude, and `Dctf` clauses agree. The cited Stacks constructibility background was checked at Tags 005G, 005H, and 005L; no Stacks statement is being substituted for the blueprint definition.
- Step 1: opened all four cited statements (`sk-def-sfb-pulled-back-coefficients`, `lem-sfb-alpha-iso`, `sk-def-sfb-module-pushforward-pullback`, and `sk-def-sfb-transport`); each supplies the coefficient identification, module pullback codomain, or transport operation used. No extra morphism hypothesis is used.
- Step 2: opened `def-sfb-finitely-presented-module` and `det-def-sfb-constructible-local-model`; their statements give the finite presentation and the exact scalar-matrix equivalence. The step does not use the proof of either node or replace finite constant models by local finite presentation.
- Step 3: opened `def-constructible-stratification` and `def-weil-constructible-subset`; they supply the finite locally closed partition and the separate constructibility requirement. The Noetherian remark is the stated Tag 005L consequence, and no false locality claim is added.
- Step 4: opened the layer-B statements of `sk-def-sfb-derived-categories` and `sk-def-sfb-derived-tensor-hom`; they supply the ambient derived category and relative derived tensor. Selecting full subcategories by the displayed predicates is elementary, and the test module is arbitrary in `Mod_{Λ_X}`.
- New nodes: none; there are therefore no new-node statements, sources, Mathlib leaves, or duplicate nodes to audit. The only edited node remains the existing blueprint definition.
- Edge cases: checked the empty scheme (empty stratification), zero module and zero complex (vacuous local model/Tor conditions), arbitrary finite-rank free scalar modules, and the infinite finitely presented module `\mathbf Z` over itself; these expose why finite presentation must not be replaced by finite underlying cardinality.
- Changes made during this reading: none to the mathematical statement or proof. I verified the ten citation excerpts are verbatim statement excerpts, confirmed the forward-cycle repairs and the current module-pullback dependency, and retained the worker's exact blueprint provenance and search log. The dry run is being executed with `deliver.py` from the shared launcher; no Lean compiler or build was run.
