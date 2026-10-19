# pur713-def-module-category — Q49 stage-1 report

## Files written

- `dag/nodes/sec-smooth-purity/pur713-def-module-category.json`: existing definition, Mathlib leaf. `DerivedCategory`, `DerivedCategory.Plus`, and `DerivedCategory.Bounded` specialize to the actual internal-module category, one declaration per category. Zero new nodes.
- `citations.json`: `[]`, since this definition/Mathlib leaf has no proof steps.
- `report.md`: this report. Searches are logged by the authorized `msearch.py` command in `searches.jsonl`.

## Attachments

None. Searches for the blueprint tag and for the notion in the project's `WeilConjectures/` source found no declaration giving all three coefficient cases and both bounded variants. In particular `AlgebraicGeometry.ProEtale.AdicSheaf` (`SixFunctors/ProEtale/Adic/Module.lean:54`) is an underived category for Qbar coefficients, in sheaves of WeilCoefficients-modules over the source's adicConstantSheaf. It neither states this whole definition nor identifies those coefficients with the present pulled-back ring object. It is not an attachment. Upstream master is reference only.

## WANTED

None.

## Corrections and dependency audit

The original definition agrees mathematically with the current blueprint. It had two dangling prose references: `pur713-input-module-abelian` and `pur456-pbc-finite-category` are absent from the DAG and do not occur as declarations of nodes in the current blueprint (only as references from other nodes). `sk-def-sf-setting`, its seeded dependency, does not supply that module-abelian input: its current statement describes older completion/rationalization coefficient conventions. The replacement references resolve the intended ordinary category without changing its meaning. This is a cross-reference repair, not a statement dispute.

The statement now introduces X, ell, E and T explicitly and names:

- `pur713-def-coefficient-rings`: precisely R_(X,T), a commutative ring object in abelian sheaves. Its own dependency nodes supply the continuous and Qbar coefficient rings.
- `pur713-def-modules`: precisely the unital associative internal action and its equivariant morphisms, with the notation Mod(X_proet,T).
- `sk-def-sfb-sheaf-tensor`: the sheafified tensor over Z, with Ab as an explicit example of the coefficient category, rather than a cartesian tensor.
- `lem-weil-pbc-sheaf-tensor-closed`: clauses (1)–(3) give abelianness of abelian sheaves, additivity of tensor, and preservation of colimits. These are stronger than the hypotheses needed by the next node.
- `lem-sfb-modobj-abelian`: an abelian monoidal category with additive tensor and R tensor - preserving finite colimits has an abelian category of R-module objects. The preceding node provides the hypotheses for the actual pro-etale sheaf category; the coefficient-ring node provides R as a monoid object. No claim about modules on a ringed site is substituted for this internal-module statement.
- `def-weil-abstract-derived-category`: localization of all Z-indexed cochain complexes at quasi-isomorphisms and the cohomology functors on the resulting category.
- `def-weil-pbc-bounded-derived-subcategories`: both required cohomological support conditions for an arbitrary abelian category.
- `def-weil-pbc-proetale-site` and `def-weil-size-convention`: the site is replaced by a small skeleton in a sufficiently large universe. Thus the sheaf-tensor theorem's essential-smallness hypothesis is met and the ordinary localization can be chosen in a sufficiently large universe.

The generic derived category and bounded-subcategory nodes already exist, so no new nodes duplicate them. Blueprint/DAG searches for “derived category”, “bounded below”, “module objects”, “module-category”, and “Non-finite-coefficient” were read. `sk-def-sfb-derived-categories` contains the same construction for O_E and E in its layer-B table, but also contains many derived-functor assertions and is not the full definition for these three coefficient cases with both bounded variants. It is not used as an omnibus input. No units or chapters were changed: this item is not the key node of the coefficient-towers unit, whose record has no proof steps.

## Mathlib verdict

The authorized searches ran LeanFinder twice, Loogle, LeanSearch, and three source grep queries. All services answered; no outage is reported as absence. Every query recorded in the JSON is the exact query in the search log. Candidate source text was read directly, without opening Lean through a server or running any compiler.

With C equal to the actual abelian category Mod_(R_(X,T))(Sh(X_proet,Ab)), `DerivedCategory C` is a literal specialization; there is no equivalence-of-definitions theorem to prove. `HasDerivedCategory.standard` supplies a localization in a sufficiently large universe. Read `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean:74–98`: DerivedCategory at 87, Q at 95, its localization instance at 98. Read `HomologySequence.lean:34–41` for homologyFunctor and its factorization from complexes. Read `TStructure.lean:84–120` and `200–218`: isGE_iff at 90 and isLE_iff at 107 identify the standard t-structure with cohomology vanishing; Plus at 204 and Bounded at 207 are its full subcategories. These definitions impose none of the extra coefficient constructions explicitly excluded by the blueprint. The item is therefore one Mathlib leaf; no new Mathlib leaves were created.

## Review by Q49

I read the complete current blueprint file `main-20261015/blueprint/sec-smooth-purity/sk-def-sp-coefficient-towers/pur713-def-module-category.md`, its unit and chapter records, and the coefficient-ring and module-object statements. I also read the current source statement of `lem-sfb-modobj-abelian`, the source statement of `lem-weil-pbc-sheaf-tensor-closed`, and Stacks `derived.tex`, Definition `definition-unbounded-derived-category` (Tag 05RU), including the three displayed boundedness conditions. The ordinary unbounded localization and the meanings of + and b agree verbatim in substance with those sources. The only definition-specific source is the current blueprint; Stacks supplies the general derived-category conventions.

There are no proof steps to audit under C1/C4: this is a definition, recognized by a direct Mathlib specialization, and its proof and proof_deps remain empty. I checked every statement dependency by reading its statement, as detailed above. In particular the module-abelian node really states abelianness of internal module objects; the sheaf-tensor theorem really supplies its finite-colimit-preservation and additive-tensor hypotheses, and the site/size nodes make the index category essentially small. The abstract-derived node supplies the cohomology used by the bounded-subcategory node. The replacement avoids using an underived module definition as a theorem of abelianness or using the finite etale site as if it were the pro-etale site.

For the B–E self-check, no new node can hide a proof sketch, restate a clause, introduce a duplicate, or omit a search. The definition is self-contained after replacing its dangling references, TeX is written once, and each Mathlib clause records the declarations and exact source lines read. Small cases give the expected answers: the zero object belongs to both bounded subcategories (take any finite interval), a module in one cohomological degree belongs to both, and the definition allows arbitrary unbounded complexes in the ambient category. There is no derived-completeness hypothesis even at T = O_E; T = E and T = Qbar do not use a rationalization or a colimit. An empty scheme causes no exception: its sheaf/module categories and their ordinary derived categories are still defined. I did not assume constructibility, finite type, noetherianity, or invertibility of ell on X to define this category. No SGA source, route change, Lean writing, or compiler/build command was used.

The corrected dependencies and precise Mathlib references are the substantive changes. Nothing remains unfinished for this one-level definition split.

## Earlier second reading (a previous round; superseded)

I reopened delivery-errors.md §§B–E, the imported node, every statement named in its `stmt_deps`, the current blueprint node `pur713-def-module-category` (main-20261015, order 2479), and Stacks `derived.tex`, Definition 05RU (`definition-unbounded-derived-category`). The source has no proof steps and no new nodes are present. The item statement agrees with the blueprint clause by clause after making the ambient scheme, coefficient choices, pro-étale site, internal module category, ordinary localization, and the `+`/`b` support conditions explicit. The added clauses exclude constructions that the source explicitly says are separate comparisons; they do not add hypotheses to the category.

- Item statement: checked `T=\mathcal O_E,E,\overline{\mathbf Q}_\ell`, the internal module category, ordinary unbounded derived localization, and both cohomological support conditions against the blueprint and 05RU; PASS, including `X=\varnothing`, the zero object, and a one-degree module.
- Proof steps: none (the node is a definition/Mathlib leaf); PASS.
- New nodes: none; the existing coefficient, module-object, site/size, sheaf-tensor, abelian-module, abstract-derived, and bounded-subcategory nodes were opened and each supplies exactly the cited notion; PASS.
- Mathlib leaf: checked `DerivedCategory`/`Q`/localization in `Basic.lean:81,87,95,98`, homology in `HomologySequence.lean:34,39`, and `Plus`/`Bounded` plus the `isGE_iff`/`isLE_iff` characterizations in `TStructure.lean:90,107,204,207`; PASS as a one-line specialization to the internal-module category.
- Search audit: reran the whole-blueprint and DAG duplicate searches and read the six recorded Mathlib search results; no equivalent specialized definition or usable declaration was found. All services returned normally and all seven records are present in `searches.jsonl`; PASS.
- Edge cases: the empty scheme, either coefficient specialization, the zero object, and complexes concentrated in one degree satisfy the stated definitions; arbitrary unbounded complexes remain in the ambient category; PASS.

Changes made during this second reading: no mathematical or node-file correction was required. I clarified the second-reading audit here and confirmed that the worker's replacement of dangling `pur713-input-module-abelian`/`pur456-pbc-finite-category` references with the precise existing interfaces is required for a self-contained statement. No Lean, compiler, Lake, or build command was run.

## Dry run

Validation command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q49 pur713-def-module-category --no-push`. The command performs the maintainer preflight in its own temporary worktree; its terminal output records acceptance. The sandbox is reserved for the second reader, and this reader makes no delivery push. A read-only dependency walk found no cycle involving the item; it exposed an inherited missing `def-weil-pbc-etale-morphism` below existing dependencies, which was not edited.


## Earlier second reading (a previous round; superseded)

This is the current independent second reading, on 2026-10-17. I opened the sandbox node, its imported original, the current blueprint `pur713-def-module-category.md` (order 2479), Stacks `derived.tex`, Definition `definition-unbounded-derived-category` (Tag 05RU, lines 3689–3723), and all nine statement dependencies. The older sections remain as history; the required delivery commands are run by this reader.

- Item statement: against the current blueprint and 05RU, checked all three coefficient choices, the actual internal-module category over the pulled-back ring, ordinary unbounded localization, and both cohomology support conditions; PASS. Explicitly introducing a scheme X, a prime ell, and a finite extension E only binds the source's parameters. No finite-type, constructibility, characteristic, or completeness condition was added.
- Proof steps: none, as verified in the node and the source definition; PASS. `proof`, `proof_deps`, and `citations.json` are empty, so there is no uncited proof step, circular application, or clause moved into a new lemma.
- New nodes: none, verified by comparing the sandbox file list with the shared DAG; PASS for B1–B7 and D1–D2 without exceptions.
- Dependency `pur713-def-coefficient-rings`: opened its statement and source; PASS, it supplies exactly the commutative ring object R_(X,T) in abelian sheaves, without asserting sectionwise continuous functions.
- Dependency `pur713-def-modules`: opened its statement and source; PASS, it defines the associative unital internal action and equivariant maps and the displayed notation, for all three coefficient choices.
- Dependencies `def-weil-pbc-proetale-site` and `def-weil-size-convention`: opened both statements; PASS, they provide a bounded essentially small site and the larger universe needed for the sheaf and localization constructions. No constant-ring module category from the second paragraph of the site node is substituted for the present ring object.
- Dependency `sk-def-sfb-sheaf-tensor`: opened its statement; PASS, Ab uses tensor over Z and sheafification, with Ab explicitly among the permitted closed symmetric monoidal Grothendieck coefficient categories.
- Dependency `lem-weil-pbc-sheaf-tensor-closed`: opened clauses (1)–(3); PASS, at that site with A=Ab they give abelianness, additive tensor, and preservation of all colimits, hence finite colimits for R tensor -.
- Dependency `lem-sfb-modobj-abelian`: opened its statement and current blueprint source; PASS, its abelian ambient category, additive tensor, monoid object R, and finite-colimit hypothesis are precisely supplied above, so its conclusion applies to the actual module objects.
- Dependency `def-weil-abstract-derived-category`: opened its statement and 05RU; PASS, it gives Z-indexed cochain complexes, quasi-isomorphism localization, and the cohomology functors used here.
- Dependency `def-weil-pbc-bounded-derived-subcategories`: opened its statement and 05RU; PASS, its plus and bounded vanishing conditions agree with the item's clauses for arbitrary abelian categories.
- Mathlib leaf: read `Basic.lean:74–98`, `HomologySequence.lean:28–41`, and `TStructure.lean:84–120,200–218` directly in the read-only source; PASS. `DerivedCategory C`, `DerivedCategory.Plus C`, and `DerivedCategory.Bounded C` apply to C equal to the cited internal-module category, with no theorem identifying two different module categories needed. `HasDerivedCategory.standard` supplies the localization choice; `isGE_iff` and `isLE_iff` give the exact cohomology conditions.
- Duplicate/source audit: reran whole-blueprint searches for “derived category” and “module objects”, and independently searched `DerivedCategory.Bounded` with Loogle and `HasDerivedCategory.standard|abbrev Plus|abbrev Bounded` with the authorized source grep; PASS. Both new queries returned normally and are recorded verbatim in `searches.jsonl` and the node. The generic definitions already have nodes; no duplicate is created. The source's `AdicSheaf` uses a different ambient coefficient category and does not attach this three-coefficient definition.
- Edge cases: PASS for the empty scheme, X a field spectrum, E=Q_ell, each of the three T choices, the zero complex, a module in degree 0 or 1, and complexes with arbitrarily unbounded cohomology. Zero lies in both full subcategories; a one-degree object lies in both; unrestricted unbounded complexes remain in the ambient category. There is no n parameter to restrict.

Changes: appended this required current second-reading section, and added the two independently executed Mathlib searches to the node. The mathematical statement, all dependencies, Mathlib declaration references, and empty proof/citation arrays required no correction. The original worker's `## Review by Q49` is preserved. No Lean source, live repository, launcher, compiler, Lake, or build was changed or run.

Second-reader validation: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q49 pur713-def-module-category --no-push` printed `OK (not pushed) deliver/Q49/pur713-def-module-category at d15b8e131f: preflight passed`. The tool's supported syntax omits the trailing `.` in the brief. The final push uses the same command without `--no-push`.


## Repair after landing return (2026-10-17)

The landing return said that `pur713-def-coefficient-rings` had changed since review. I reread the current repository node in full and compared the clause used by this item: it still defines the commutative ring object `\mathcal R_{X,T}=p_X^*\underline T` on the small pro-étale site for `T\in{\mathcal O_E,E,\overline{\mathbf Q}_\ell}`, with the transported multiplication and unit and with no identification of sections with continuous maps. This is exactly the input required by the item statement and by `pur713-def-modules`; no hypothesis, coefficient category, or construction in the item needs adjustment.

I updated the item’s `split_report` summary/date to record this revalidation. I then reran `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q49 pur713-def-module-category --no-push`; it printed `OK (not pushed) ... preflight passed` at `1a0a675d6d`.

## Second reading by Q49

- Item statement: checked against blueprint `pur713-def-module-category` (main-20261015, order 2479) and Stacks `derived.tex`, Definition `definition-unbounded-derived-category`, Tag 05RU, lines 3689–3724. The three coefficient choices, explicit scheme and finite extension parameters, internal module category, ordinary unbounded localization, and cohomological definitions of `+` and `b` agree clause by clause; no finite-type, constructibility, completeness, rationalization, or colimit hypothesis was added. PASS.
- Proof steps: the item is a definition/Mathlib leaf and has no proof steps, `proof_deps`, or citations. PASS; there is no hidden argument or uncited non-elementary fact.
- Statement dependencies: reread `def-weil-pbc-proetale-site`, `def-weil-size-convention`, `pur713-def-coefficient-rings`, `pur713-def-modules`, `sk-def-sfb-sheaf-tensor`, `lem-weil-pbc-sheaf-tensor-closed`, `lem-sfb-modobj-abelian`, `def-weil-abstract-derived-category`, and `def-weil-pbc-bounded-derived-subcategories`. Each supplies exactly the site, universe, coefficient ring object, internal actions, sheafified tensor, abelian module-object structure, derived localization, or boundedness notion used by the item. PASS.
- Mathlib leaf: checked `HasDerivedCategory.standard`, `DerivedCategory`, `DerivedCategory.Q`, and localization in `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean:74–98`; homology factorization in `HomologySequence.lean:34–41`; and `isGE_iff`, `isLE_iff`, `Plus`, and `Bounded` in `TStructure.lean:84–120,200–218`. These are the generic constructions specialized to the cited internal-module category, so the leaf is exact. PASS.
- New nodes and duplicate audit: no new nodes are present. Whole-blueprint and DAG searches for the specialized derived module category and its component notions found no duplicate full definition; the generic derived and bounded-category nodes are cited instead. PASS for B1–B7 and D1–D2.
- Edge cases: checked the empty scheme, a field spectrum, all three `T` choices, the zero object, a module concentrated in one degree, and arbitrary unbounded complexes. The zero and one-degree objects satisfy both bounded subcategories, while unbounded complexes remain in the ambient category. PASS; no statement dispute found.
- Searches and route: the recorded LeanSearch, Loogle, LeanFinder, and Mathlib grep queries all returned normally and support the generic leaf; no SGA source is cited. PASS.
- Changes made: added this required independent second-reading section only. The node statement, dependencies, Mathlib match, proof arrays, and citations required no mathematical repair. No Lean, compiler, Lake, or build command was run.
