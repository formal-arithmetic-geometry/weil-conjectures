## Worker report

Files written: dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-presentation-stalk-germ-lifting.json (item, statement, split; no Mathlib match), citations.json, and this report.md. The msearch command recorded searches.jsonl.

Attachments: none. Searching WeilConjectures for the exact blueprint tag and finite-presentation/germ/stalk/lift variants found local presentations, overlap-map lifting, and finite-presentation stalk models, but no declaration with every clause of this global existence assertion. The existing ModuleFinitePresentationExtension theorem is the extension tool, not an attachment of this item.

WANTED: none.

The imported item had no proof. Its statement agrees with the prescribed surjectivity argument of Stacks 01PJ, properties.tex, lemma-directed-colimit-diagram-finite-presentation, lines 3173-3188. I kept the statement, its hypotheses, and statement dependencies unchanged. Nothing remains unfinished in this one-level split; the existing dependency nodes retain their own work states.

## New nodes

None. The non-elementary map-extension fact already has node lem-weil-pbc-module-finite-presentation-extension. Multiplication by a local section, the rank-one presentation, and taking the inverse image of the unit section are elementary steps, not additional nodes.

## Searches and blueprint

Read the chapter sec-proper-base-change and unit sk-thm-p1, together with the three levels in SETUP.md and GOAL.md. This is the existing auxiliary quasi-coherent-module route under the finite-pushforward argument; no chapter or unit route changes. The ancestor is lemma-weil-pbc-h1-constructible-representation, whose main-20261015 blueprint_update invokes the finite-pushforward lemma in step 2. The item's existing blueprint.from identifies the auxiliary 01PJ germ-lifting passage; split_report.blueprint relates it to the current ancestor.

Before deciding against new nodes I searched the entire DAG for 01PI, lemma-extend-finite-presentation, and finite-presentation/germ/stalk concepts, and the blueprint index for extend finite presentation, germ, 01PI, and 01PJ. The six blueprint germ hits concern function fields, rational sections, Frobenius conjugacy, strict-local exchange, Serre A, and zero-dimensional etale cohomology; none states this item. The index has no 01PI or 01PJ match. Existing definitions and the affine-basis, affine-qcqs and extension nodes were opened and their statements read.

The inherited Q45 Mathlib searches and their reported results are retained. Q125 ran LeanFinder twice with different phrasings, Loogle, LeanSearch and a source grep, exactly as logged in searches.jsonl and appended to mathlib_searches. LeanSearch and LeanFinder returned local QuasicoherentData and IsFinitePresentation facts; I read the defining class in Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:267 onward. The ring-valued exists_lift_of_germInjective hits are not module-sheaf global extension. The grep's five AffineTransitionLimit hits concern finite-presentation scheme morphisms; I read the general declaration at line 1232. None states the item or gives a one-line specialization. All services answered successfully for the Q125 searches; the older unavailable result remains correctly marked unavailable.

## Not duplicates

No new-node/existing-node pairs arise. I reused the existing 01PI node rather than introducing a second map-extension lemma, and used the existing affine-basis and affine-qcqs nodes. The item remains distinct from extension of an arbitrary finitely presented local source: its proof constructs a rank-one local source from the given germ and then produces the required germ upstairs.

## Review by Q125

I read Stacks properties.tex at lemma-directed-colimit-diagram-finite-presentation (01PJ), especially its final surjectivity paragraph, and lemma-extend-finite-presentation (01PI), both statement and proof. I checked the finite-presentation definition in modules.tex, definition-finite-presentation (01BN), and the affine-basis statement in schemes.tex, lemma-basis-affine-opens (01IT). There are no new nodes requiring further source comparison. The item requires only qcqs X, quasi-coherent F, an ordinary Zariski point and an arbitrary germ; no noetherian, separated, coherent or globally generated assumption is added.

Step 1 uses the explicit representative and restriction description in def-weil-pbc-module-stalk, the neighbourhood-refinement statement in lem-weil-pbc-affine-opens-basis, and the quasi-compactness assertion in lem-weil-pbc-affine-scheme-qcqs. I opened all three node statements; each says exactly that fact. We use one affine neighbourhood and never assume an intersection of affine opens is affine. The restriction of a representative preserves its germ directly in the colimit defining the stalk.

Step 2 uses def-weil-pbc-module-finite-type-presentation, whose statement explicitly defines restriction, finite free modules, section-induced maps, and finite presentation with nonnegative m,n. I also opened def-weil-sheaf-of-modules-category for the module action and semilinear restriction maps. The displayed multiplication formula commutes with restrictions and is linear by the module laws. Setting m=0 and n=1 gives the rank-one presentation directly. This is elementary, with no unproved quasi-coherence or exactness theorem hidden inside it.

Step 3 uses only lem-weil-pbc-module-finite-presentation-extension. Its statement gives not just the extended finitely presented module and map, but an isomorphism on U under which the maps agree. This is essential for the unit calculation. I checked its hypotheses individually: X is quasi-compact and quasi-separated by assumption; U is quasi-compact by step 1; F is quasi-coherent by assumption; O_U has finite presentation by step 2; multiplication is O_U-linear by its explicit construction. The node has the same unit as the item. It neither depends on this item nor requires a filtered-colimit theorem, so this proof does not recurse through the parent 01PJ claim.

Step 4 uses the exact stalk-map formula in def-weil-pbc-module-stalk. An isomorphism of restricted sheaves has inverse component at U, giving an actual section b in G(U) from 1. The equation psi|_U = mu_a composed with e gives psi_U(b)=a before taking germs. Thus psi_x(b_x)=a_x=s follows by the cited formula; no unnamed restriction/stalk comparison is used. The construction avoids treating an isomorphism merely as an equality of objects.

I checked B-E against the resulting files. B: no new statement-only node, duplicate notion, unsupported source tag or Mathlib leaf was introduced; all data and object types are in the original self-contained statement, and TeX backslashes are single after JSON decoding. C: citations.json quotes the full actual statement for every dependency at each step, including the elementary steps, and proof_deps is precisely their union. D: the proof carries the local map and unit calculation rather than replacing the item by a restatement; it applies the existing general extension lemma. E: for s=0 the same construction uses the zero multiplication map; F=0 also causes no exception; X empty has no x, so the statement is vacuous; for X affine the construction agrees with choosing a cyclic map locally, and it assumes no noetherianity. No new statement needs a separate small-case test. I corrected no source error or statement: the work fills the missing proof. Every step is shorter than 2000 characters and the four-step argument contains no hidden long comparison lemma.
