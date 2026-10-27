## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-ferrand-pushout-space-agreement.json`: unchanged statement and statement dependencies; four-step proof using the existing scheme pushout and general scheme-colimit upgrade criterion.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ferrand-etale-scheme-patching.json`: one new statement-only input, status `unsplit`, no Mathlib match. It states the scheme-theoretic etale patching unit and counit; it makes no assertion about maps into algebraic spaces.
- `citations.json`: one verbatim statement quotation for each of the five step/node citations.

Attachments: none. The project-source search for the item blueprint tag, Ferrand, pinching, and space-pushout terms found no exact finished declaration. The project Gluing module only provides open gluing and related quasi-separatedness. Existing sorried pinching declarations are not attachments. No Lean was written or compiled.

WANTED: none; the Stacks sources needed for this split are present.

The item had no proof. Its statement agrees with Tag 0EDP and the Situation in More on Morphisms, and needed no correction. The important omitted detail in 0EDP is that its criterion quantifies over all etale scheme maps, whereas the stated equivalence in 0ECL has separated objects. The new input includes the Zariski-local extension of its counit, explained below. No separation of P, quasi-compactness of etale sources, finiteness of j, or nilpotence of the closed immersion was introduced.

Nothing remains unfinished in the item's one-level split. The new unsplit node is the next independent scheme-theoretic task.

## Sources and route

I read `spaces-pushouts.tex`, lemma-colimit-agrees (Tag 07SX), its four hypotheses and proof, and lemma-pushout-along-closed-immersion-and-integral (Tag 0EDP) and its proof. In `more-morphisms.tex` I read situation-pushout-along-closed-immersion-and-integral, proposition-pushout-along-closed-immersion-and-integral (0E25), lemma-pushout-functor (0ECK), and lemma-pushout-functor-equivalence-flat (0ECL), including their proofs. The closed/integral/fibre-affine-neighbourhood assumptions of the item are exactly those of the Situation. The etale case of 0ECL uses 0ECK for existence and canonical cartesian squares, not merely an unspecified equivalence of categories.

The current blueprint is `literature/blueprint/latest`, pointing to main-20261024. I read its six-functors-basics unit and direct-images proof, especially (3). The inherited branch is a scheme-gluing prerequisite in the trait schematicity input; no chapter or unit route is changed. `blueprint_refs.py ancestor` returns None on this inherited chain; I preserve that value, its complete via list, and its explicit direct-images proof (3) place. Whole-blueprint searches for pushout, Ferrand, 0ECK, 0ECL and etale/pushout returned no equivalent blueprint statement.

## Mathlib and duplicate searches

I searched the whole DAG for 0EDP, 0ECK, 0ECL, 07SX, the source labels, Ferrand, pinching, and separated etale pushout terminology. Before creating the new id I checked its absence. I opened the relevant candidate statements, rather than using their proof text. The general 07SX criterion already exists, so it is reused. The scheme construction 0E25 already exists, so it is reused too.

All searches were run through the required msearch.py and their actual summaries are in searches.jsonl and in mathlib_searches. LeanFinder was run with both the compatible-etale-schemes and separated-cover phrasings; LeanSearch with the etale-site and algebraic-space-universal-property phrasings; Loogle with AlgebraicGeometry.Etale and CategoryTheory.IsPushout; grep with Ferrand/pinching/etale-pushout patterns and, separately, pushout/gluing in the etale morphisms file. All services answered. I read every hit: Scheme.Etale, its category and topology, HasPullbacksEtale, etale composition/base change, Scheme.GlueData.gluedScheme, and the unrelated integral and closed-immersion permanence declarations. They do not state the closed-integral patching theorem, nor is that theorem their one-line specialization. The alternative Finder search likewise returned only etale foundations, open gluing and unrelated affine-transition-limit declarations. There is no Mathlib leaf in this delivery.

## Not duplicates

lem-sfb-ferrand-etale-scheme-patching vs lem-sfb-ferrand-pushout-space-agreement: the new input constructs and recovers etale SCHEMES over a scheme pushout; the item proves a universal property for arbitrary ALGEBRAIC SPACE targets. Neither new clause is the item's conclusion.

lem-sfb-ferrand-etale-scheme-patching vs lem-sfb-ferrand-scheme-pushout: 0E25 constructs the base scheme and its affine charts; it does not state effectivity of compatible etale schemes or the etale counit.

lem-sfb-ferrand-etale-scheme-patching vs lem-sfb-scheme-colimit-upgrade-space-targets: 07SX is a general conditional upgrade criterion for small diagrams. It assumes etale base-change colimits and separated-family effectivity; it does not prove those Ferrand-specific inputs.

lem-sfb-ferrand-etale-scheme-patching vs lem-sfb-scheme-infinitesimal-etale-patching: that node assumes the closed immersion is a thickening, but permits a merely affine opposite map. Here the closed immersion is arbitrary and the opposite map integral with the fibre-neighbourhood assumption. Neither set of assumptions implies the other.

lem-sfb-ferrand-etale-scheme-patching vs lem-sfb-etale-affine-pinching-descent: that node requires a finite component map and an exact affine etale presentation and concludes a scheme pushout and flat base-change compatibility. It gives no effectivity of compatible separated etale objects and does not cover integral maps not locally of finite type.

lem-sfb-ferrand-etale-scheme-patching vs lem-sfb-space-pushout-compatible-etale-charts: that node is about algebraic-space charts across an affine thickening. It assumes a thickening and uses a pre-existing algebraic-space pushout, neither available here.

lem-sfb-ferrand-etale-scheme-patching vs lem-sfb-space-pushout-etale-base-change: that node requires an algebraic-space pushout along a thickening, and cannot be used to establish the present item's algebraic-space universal property without circularity.

lem-sfb-ferrand-etale-scheme-patching vs lem-sfb-closed-space-union-pushout: that node asserts an algebraic-space pushout for two closed subspaces with intersecting ideals zero. It neither constructs etale lifts nor covers a general integral leg.

lem-sfb-ferrand-etale-scheme-patching vs lem-per-open-separated-etale-pushout: its gluing leg is an open immersion and its other leg separated etale, and its output is an algebraic space. These are different hypotheses, construction and conclusion from the closed-integral scheme patching here.

No existing unmerged node has source tag 0ECK or 0ECL. Thus there are no extra same-source pairs for the new node.

## Review by Q01

I checked the item's statement against 0EDP with its referenced Situation open. It assumes exactly a closed i, an integral j, and an affine open containing each fibre image. It asks for a universal property in spaces over the given arbitrary S. The statement and all its hypotheses are retained. I read the chapter/unit records and the latest direct-images proof; this input stays on the inherited route.

Step 1 uses the STATEMENT of lem-sfb-ferrand-scheme-pushout: it explicitly supplies a scheme pushout and its quotient topology, hence joint surjectivity of a,b. I checked that its hypotheses are exactly the item's. The STATEMENT of def-weil-pbc-category-colimit supplies existence and uniqueness of comparison maps, so the source's constructed pushout and the arbitrary given P are isomorphic as cocones. Applying its uniqueness to the two maps to S verifies the relative universal property, rather than assuming a colimit in a slice is automatically an absolute one. Nothing about etale objects is taken from the proof of 0E25.

Step 2 uses the new input's explicit converse for EVERY etale U to P, including nonseparated U to P. Its conclusion is an actual scheme-pushout property of the inverse-image square, not just equality of underlying sets or recovery of isolated component objects. The over-S qualification follows by the same uniqueness calculation as step 1. The reference to hypothesis (ii) is explanatory; the general criterion is applied only in step 4.

Step 3 uses precisely the new input's forward statement and its CANONICAL isomorphisms. A compatible family in the span 2-limit supplies X', T', and their isomorphism over Z. Separatedness of the component structure maps is part of the criterion's assumption, so it is in force when patching is applied. The recovered maps commute with that isomorphism, which is required to identify the entire compatible family, not merely its objects. There is no use of proof-only data of another node.

Step 4 uses the complete STATEMENT of lem-sfb-scheme-colimit-upgrade-space-targets. Its base is S, its small category is the explicit three-object span, its joint-surjectivity premise is step 1, its ALL-etale-base-change premise is step 2, and its separated-family effectivity premise is step 3. Smallness poses no universe issue: the indexing category is finite. The conclusion of that node is bijectivity on maps to every algebraic space over S. I wrote out how a compatible family for the span is the pair f,g of the item, with their common Z-map. This checks both existence and uniqueness. The two cited existing theorem nodes have the same unit as the item; no off-unit tool-use declaration is needed.

For the new node I checked 0ECK and 0ECL statement and proof. A separated etale map is locally quasi-finite, so their etale specialization constructs P' and gives its separated etale structure map and cartesian recovery squares. The converse for separated etale U is the counit in the second paragraph of 0ECL. Here are the details for arbitrary etale U, which must not be silently assumed separated: cover U by affine opens U_alpha each mapping into an affine open of P (first cover by inverse images of affine opens, then refine by affine opens). Each U_alpha to P is separated: the map between affines is affine and separated, followed by an open immersion, and separatedness is preserved by composition. Each overlap U_alpha intersect U_beta maps to P separated too, because it is an open subscheme of U_alpha. Etaleness is inherited under those open restrictions. Thus the separated counit applies to every U_alpha AND every overlap; the overlaps are not assumed affine. Given compatible maps from U times_P X and U times_P T to any scheme H, the counit on U_alpha produces unique maps U_alpha to H. The counit on each overlap makes these maps agree. The scheme morphism gluing theorem gives a unique U to H extending the pair, and its restrictions on the two components equal the original maps because their inverse-image open covers do. This proves the arbitrary-etale counit without quasi-compactness or separatedness of q. This argument is supporting material for the next worker; the new unsplit JSON contains only the self-contained statement, with no proof or proof dependencies.

I checked B1-B10: every object of the new node is introduced, every nonstandard notion has its correct definition dependency (separated is instead defined inline), TeX has one level of escaping, the Stacks tags match their labels, the id is new, all actual Mathlib searches and negative verdicts are recorded, and blueprint origin/place are present. I checked C1-C8: every non-elementary fact in the item's assembly proof is in a cited statement, all five citations have verbatim quotes, no citation uses another node's proof, no dependency on this item is introduced, and no off-unit theorem is substituted for the unit route. I checked D1-D5: the new node is an etale descent theorem for SCHEMES, not a renamed space-pushout conclusion; the existing general colimit criterion performs the upgrade, and the previously omitted arbitrary-etale counit is accounted for explicitly. All four proof steps have fewer than 800 characters, so there is no long step concealing a further lemma.

For E1-E7 I checked particularly the absence of finite-type and nilpotence assumptions, correct pullback bases, the given isomorphism phi, separatedness only where available, and both relative structure-map uniqueness calculations. I tested the new statement on Z empty (disjoint union, compatible etale schemes are a pair), i an identity (the pushout is T), j an identity (the pushout is X), all schemes empty (including the zero ring affine chart), and non-surjective j (no spurious surjectivity required). A genuinely non-nilpotent pinching such as Spec k[x] glued to Spec k along x=0 is allowed. An integral nonfinite ring extension on the opposite leg is allowed: no finite-module argument enters. The nonseparated etale example given by the affine line with doubled origin mapping to the affine line is not excluded by the counit; the overlap gluing argument is exactly what handles it.

No statement dispute or source error was found. I corrected the potential inference from a separated equivalence to an arbitrary-etale counit by including the latter explicitly in the new node and explaining the Zariski argument here. No process files, live repository files, launcher files, or Lean files were changed.
