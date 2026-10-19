## Worker report

Files written:

- `dag/nodes/sec-trace-formula/def-trf-oriented-nearby-cycles.json`: definition marked `split`; its existing statement dependencies and exact clauses are retained, with refreshed Q19 Mathlib-search records and blueprint/split metadata.
- `citations.json`: empty list, because a definition has no proof steps.
- `searches.jsonl`: four searches actually run for this item (LeanFinder, Loogle, grep, LeanSearch).

New nodes: none. Mathlib leaves: none. The definition is not present as a declaration in either read-only `WeilConjectures/` source tree, and no declaration tagged `(blueprint: def-trf-oriented-nearby-cycles)` was found. No Lean file was written and no compiler, Lake, or build command was run.

Attachments: none.

WANTED: Illusie, *Around the Thom--Sebastiani theorem*, §§1.4--1.5, for the Psi-good pair and ordinary-comparison terminology (the item's source explicitly marks the local PDF WANTED). The oriented-product construction itself is available in the archived ILO PDF cited by the item.

What was incomplete: the imported node was statement-only and still `unsplit`. Its definition uses the existing statement node `lem-trf-oriented-product-universal` for the site construction and universal property, plus the seven existing definition nodes listed in `stmt_deps`; no additional node is needed for a definition. I changed only the split status, blueprint `from.place` wording, Mathlib-search records, and `split_report`; the statement, hypotheses, dependencies, source, and provenance remain unchanged. No statement dispute was found.

What I could not finish: nothing within stage 1. A second reader must independently inspect this split and perform the no-push delivery.

## Sources, route and searches

I read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, the complete item node, and the complete statement of every dependency in `stmt_deps`: `def-weil-pbc-etale-site`, `def-weil-pbc-ringed-topos-morphism`, `def-weil-sheaf-of-modules-category`, `def-weil-abstract-derived-category`, `def-pur-kinjective-complex`, `def-pc-kflat-complex`, `def-pur-sheaf-tensor-product`, and `lem-trf-oriented-product-universal`. The last node states the site of triples, its three covering types, projections, oriented 2-morphism, and universal property needed by the definition; the other nodes supply exactly the small etale-site, ringed-topos, module-category, derived-category, K-injective, K-flat, and sheaf-tensor notions named in the statement. Since the item is a definition, there are no proof steps and therefore no step citations; `citations.json` is correctly empty.

I read ILO, Exposé XI §§1.1--1.7 in the local PDF (`pdftotext` pages 171--174 of the exposition). Its construction gives the category of triples, covering families (a)--(c), sheaf topos, projections, the 2-arrow `g p₂ ⇒ f p₁`, Theorem 1.4's universal property, and Definition 1.7's independence of site choices. Specializing `g=id_B` gives the item's `V_f` and `ψ_f=(1_T,f,1_f)`. The remaining clauses are definitions of derived direct image, ordinary base-change mate, Psi-goodness, lax tensor map, and the two oriented Kunneth products; they agree with the item source's stated terminology. The local Around Thom--Sebastiani PDF is absent, so its requested citation is recorded as WANTED rather than silently treated as read.

The four logged searches are exactly those in `searches.jsonl`: LeanFinder for the oriented nearby-cycle definition, Loogle for `nearbyCycles, OrientedProduct, GeometricMorphism`, grep for `nearbyCycles|orientedProduct|vanishingTopos|Psi.good` under Mathlib/AlgebraicGeometry, and LeanSearch for the vanishing-topos/derived-nearby-cycle description. I read the returned signatures; they concern ordinary etale sites, ideal sheaves, Mayer--Vietoris or generic category constructions and do not state this project-specific definition. Thus `mathlib_match` remains null.

## Not duplicates

No new nodes were created. The existing `lem-trf-oriented-product-universal` is a strictly smaller universal-property statement used by this definition, not a duplicate: it constructs the general oriented product, while this item specializes it to etale topoi and adds nearby-cycle, base-change, Psi-goodness, tensor, and Kunneth definitions.

## Review by Q19

I checked the item against ILO Exposé XI §§1.1--1.7 and the cited project nodes clause by clause. The item first fixes schemes and their small etale topoi, then specializes the left oriented product to `f:T_Et→B_Et` and `id:B_Et→B_Et`; the site of triples and the universal property are exactly what `lem-trf-oriented-product-universal` states. Its projections and orientation have the correct direction `p₂ ⇒ f p₁`, matching ILO's `g p₂ ⇒ f p₁` when `g=id`. The map `ψ_f` corresponds to `(1_T,f,1_f)` as in the universal property.

The dependency statements say exactly what each later clause takes: `def-weil-pbc-etale-site` supplies the small etale sites; `def-weil-pbc-ringed-topos-morphism` supplies geometric/ringed-topos morphisms; `def-weil-sheaf-of-modules-category` supplies module sheaves; `def-weil-abstract-derived-category` supplies the abstract derived categories; `def-pur-kinjective-complex` supplies K-injective computation of right derived direct image; `def-pc-kflat-complex` supplies K-flat resolutions; and `def-pur-sheaf-tensor-product` supplies the sheaf tensor product. The universal-product node supplies every site-construction clause and its uniqueness. No dependency is cited for a fact absent from its statement.

I verified the ordinary comparison as the adjunction mate of the inverse-image square, Psi-goodness as the requirement that this comparison be invertible for every Cartesian base change, and the lax tensor map as the mate of the tensor of the two counits. For the final product clauses I checked that `T=T₁×_B T₂`, the maps `q_i` and `v_i`, and both tensor products have the displayed coefficient ring and derived notation. These are definitional clauses, so no hidden theorem is being claimed. The item includes the bounded-cohomology convention and all coefficient/topos hypotheses from its source.

I checked delivery-errors B--E: there are no new nodes, no restatement node, no cyclic proof dependencies, and no uncited proof steps. The item is not a Mathlib notion, as all four searches and the source-tree grep confirm. Small edge cases are well-typed: for `T=∅`, the oriented product and derived direct image remain defined; for `f=id_B`, the universal product specializes to the diagonal-oriented construction; for a zero coefficient ring, the module and derived categories still exist; and for `T₁` or `T₂` empty, the product clauses remain formal definitions. No hypothesis is added, dropped, or silently identified across coefficient categories.

The item has no proof step longer than 2000 characters because it is a definition. No source error or statement correction was needed. The requested no-push dry run is run after this report is written.

## Dry run

`python3 /home/ubuntu/weil-launcher-nt/deliver.py Q19 def-trf-oriented-nearby-cycles --no-push .` passed: `OK (not pushed) deliver/Q19/def-trf-oriented-nearby-cycles at 83678c3114: preflight passed`.


## Second reading by Q19

This is an independent stage-1 reading. The Q20-only maintenance recovery does not apply: the group/item are Q19/def-trf-oriented-nearby-cycles, the stage-1 item JSON exists, and no corresponding retained stage-2 packet exists. The repository and both source trees were read only. No Lean, compiler, Lake, global build, live-project write, git command in the shared repository, or sub-agent was used.

I read delivery-errors B--E, AGENTS.md, SETUP.md, GOAL.md, coord/STATE.md, coord/dag-sync.md, roles/worker.md, stages/1-dag.md and tools/README.md, the chapter and unit records, and the current ancestor's main-20261015 blueprint_update. The current ancestor's contracting-correspondence argument explicitly uses normal-cone specialization; this definition supplies its oriented nearby-cycle language without changing that route.

Clause-by-clause verdicts (there are no proof steps):

- Site and vanishing-topos clause: checked against ILO Exposé XI 1.1--1.7 and 4.1 and lem-trf-oriented-product-universal; PASS after distinguishing the presenting small sites from their sheaf topoi and spelling out the direct-image convention for a 2-arrow. The orientation is p2 => f p1, not its reverse.
- Canonical psi_f clause: checked against ILO XI 4.3 and the universal-property node; PASS, from (id_T,f,id_f).
- Module and derived-category clause: checked against the two category-definition nodes and Stacks sites-cohomology.tex section-unbounded; PASS after citing actual K-injective existence and right derivation, rather than treating the definition of K-injectivity as an existence theorem. The original unbounded scope is retained; ILO's D+ construction is its restriction, and no boundedness of its output is asserted.
- Tensor and inverse-image clause: checked against Stacks 06YS, 06YU, 06YY and 07A4 and the existing site-tensor and ringed-topos pullback statements; PASS after adding the missing dependencies. Constant coefficients identify inverse-image coefficient rings, so the inverse image is exact and its derived functor is termwise inverse image. On modules, kernels are created on underlying abelian sheaves and cokernels are sheafified cokernels; the geometric inverse image preserves the finite limits and colimits defining them. This is why no flatness assumption on Lambda is necessary.
- Induced-map clause: checked against ILO XI 1.9 and the universal-property node; PASS after writing the projections (h p1',g p2') and the arrow g p2' => g f' p1'=f h p1'. Applying this to psi_f' yields the square isomorphism with psi_f h. There is no theorem that the resulting square of topoi is Cartesian.
- Ordinary-comparison clause: checked against Illusie 1.4, especially (1.4.2)--(1.4.3); PASS after writing its exact transpose psi_f'^* v^* Rpsi_f* L = h^* psi_f^* Rpsi_f* L -> h^* L under psi_f'^* |- Rpsi_f'*. This uses only commutativity of the scheme square.
- Psi-goodness clause: checked against Illusie Definition 1.5; PASS unchanged. Invertibility is required for every Cartesian base-change square and every scheme map g, with no implicit finite-type, torsion, noetherian or constructibility hypothesis.
- Lax-tensor clause: checked against the ringed-topos tensor-pullback isomorphism, module adjunction and derived adjunction; PASS after displaying the tensor of the two counits and giving both inputs. No invertibility is claimed.
- External products and oriented Kunneth clause: checked against Illusie 2.1, (2.1.1)--(2.1.4), specializing Y1=Y2=B over B; PASS after introducing L_i and P_i and writing both comparisons beta_(q_i,id_B) and then mu_f. Their endpoints are respectively on V_f and T1 x_B T2 and all coefficient rings are Lambda. No Kunneth isomorphism theorem or finite-Tor preservation is imported here.

Dependency verdicts (each statement was opened):

- def-weil-pbc-etale-site: PASS, provides the presenting etale sites, covering families and finite limits needed by the oriented-product lemma.
- def-weil-pbc-ringed-topos-morphism: PASS, provides the geometric inverse/direct-image adjunction and the coefficient-linear direct image.
- def-weil-sheaf-of-modules-category: PASS, provides Mod(Lambda) and its abelian structure.
- def-weil-abstract-derived-category: PASS, provides the unbounded localization and cohomology used in the bounded subcategory convention.
- def-pur-kinjective-complex: PASS for the resolution notion only; the missing existence assertion is now supplied separately.
- def-pc-kflat-complex: PASS for the K-flat resolution notion only; it is not cited as a derivability theorem.
- def-pur-sheaf-tensor-product: PASS, provides the sheafified sectionwise tensor.
- lem-trf-oriented-product-universal: PASS, its three covering types, projections, orientation and universal property agree with ILO XI 1.1--1.7. Its statement, not details hidden in its proof, supplies the construction used here.
- def-weil-pbc-constant-sheaf: PASS, applies on any site, including the oriented-product site; added for the previously uncited constant coefficients.
- prop-pur-kinjective-resolutions-exist: PASS, applies to all the chosen small ringed-site presentations; added for actual unbounded K-injective resolutions.
- def-sfb-right-derived-functor: PASS, applies to additive direct image between the stated module categories once K-injectives exist; added for the total-derived construction and its canonical comparison, as supported by its dependency lem-weil-pbc-kinjective-total-derived (Stacks derived.tex 070K).
- lem-weil-pbc-site-derived-tensor-descent: PASS, its full statement supplies unbounded derived tensor and resolution-independent descent on any small commutative ringed site; added because the former K-flat definition alone did not supply them.
- lem-weil-pbc-ringed-topoi-module-adjunction: PASS, applies to these constant-ring geometric morphisms and supplies the module adjunction (Stacks sites-modules.tex 03D7).
- lem-pc-derived-adjoint-functors: PASS, applies because both derived functors are everywhere defined by the existing K-injective and K-flat constructions; added for the derived adjunction (Stacks derived.tex 09T5, lemma-derived-adjoint-functors).
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback: PASS, its statement is for arbitrary small ringed topoi, not just schemes/pro-etale sites; added for derived pullback and the tensor comparison (Stacks sites-cohomology.tex 07A4).

No new nodes exist. Hence there is no new-node statement, duplicate, restatement, Mathlib leaf or new-node proof to audit. The four original searches were read. I independently ran LeanFinder with the different vocabulary “Lax pullback of Grothendieck topoi classifying specialization arrows between geometric morphisms”, a full-Mathlib grep for nearby-cycle/vanishing-topos/oriented-product/lax-pullback names, and Loogle's quoted "nearby" search. Returned signatures describe ordinary sheaf inverse images or Units.ofNearby, not oriented nearby cycles. The actual queries/results are retained in searches.jsonl and in the item search records. Source-tree searches in both named read-only WeilConjectures trees find no oriented nearby-cycle declaration to attach.

Edge checks: T empty gives the degenerate sheaf topos and zero coefficient categories; the displayed functors and counits still exist. Lambda the zero ring or L=0 makes the comparisons maps between zero objects. For an identity square, beta transposes the counit and hence is the identity by the adjunction triangle identity. f=id_B still defines the arrow/oriented product; I do not identify it with B_Et for a general B. If B=Spec(k) for separably closed k, its etale topos is punctual and the displayed orientations specialize consistently. Empty T_i cause no tensor-domain problem. The finite-torsion application includes n=1 without a hidden invertibility hypothesis in this definition.

Changes and reasons:

1. Added seven existing statement dependencies, all strictly supporting constructions already used; no new nodes. The first worker's claim that the old dependencies alone supplied derived functors and tensors was incomplete.
2. Distinguished sites from topoi, clarified the 2-arrow convention and introduced the complexes' domains; these are explicit readings of the existing clauses, not changes of mathematical scope.
3. Wrote the ordinary mate, the lax tensor mate and the Kunneth composite so their coefficient categories, directions and endpoints can be reviewed directly.
4. Resolved the WANTED source locally: downloaded the author's PDF to this sandbox, read 1.1--1.5 and 2.1, and updated the source references. This supersedes the first worker's WANTED note without erasing it. Source: https://www.imo.universite-paris-saclay.fr/~luc.illusie/Illusie-nearby-cycles28.pdf (accessed 2026-10-17). ILO and Stacks remain the route; no prohibited SGA source was used.
5. Preserved the worker report, including its Review by Q19 section, and preserved backups before changing existing packet files. No mathematical counterexample or scope-changing statement dispute was found; the repair concerns dependency completeness and explicit construction data.

The seven added dependencies have no path back to this item in the current statement/proof DAG (checked by a read-only traversal), so none introduces a cycle through it. Proof and proof_deps remain empty because this is a definition; citations.json remains [] because it records proof-step citations only. The old dry-run result above predates these repairs. The final required server dry run and delivery follow this completed second-reading report.
