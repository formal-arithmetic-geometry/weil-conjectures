# Q144 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-etale-space-single-cover-effective-descent.json: item, split in five steps; not in Mathlib.
- dag/nodes/sec-six-functors-basics/lem-sfb-fppf-space-datum-sheaf-realization.json: statement-only prerequisite, unsplit; no Mathlib match.
- citations.json: ten verbatim statement excerpts for the ten step citations.

## Attachments

None. Searches of lean/WeilConjectures by the item tag, etale-space names, algebraic-space terminology and descent did not locate a declaration of the item or the new prerequisite. Scheme descent and sheaf morphism descent are not algebraic-space effectivity.

## Wanted sources

None. All sources used are in literature/stacks-project/.

## Corrections and scope

No change to the statement. The original source selection is correct. Tag 0ADV(1) is relevant even though v need not be finite type: the covering is a singleton and hence countable. Its proof does not require the descended map to be finite type. The imported proof was empty. The split now gives the actual algebraicity argument rather than making a new node asserting this item's effectivity clause.

The inherited blueprint chain has from.node = null because it terminates at a Lean module, as the imported place already explains. I ran blueprint_refs.py ancestor and retained its answer None, and read the newest blueprint/latest unit and direct-images proof (paragraph (3)). The new node inherits that null ancestor and the full via chain, with this item inserted first. It serves the already recorded alteration/moduli supporting input; the chapter and unit route are unchanged. This item is not the unit's key statement, so no unit record was edited.

## Not duplicates

lem-sfb-fppf-space-datum-sheaf-realization vs lem-trf-fppf-sheaf-representability-descent-data: the existing 02W5 statement is about scheme objects on a scheme covering of a scheme base, not algebraic-space objects over algebraic-space covers; its pullbacks are required to be schemes.
lem-sfb-fppf-space-datum-sheaf-realization vs lem-trf-fppf-scheme-data-sheaf-gluing: again the existing datum consists of schemes over a scheme covering; it does not construct sheaves over an algebraic-space base from algebraic-space local objects.
lem-sfb-fppf-space-datum-sheaf-realization vs lem-pe-set-sheaf-cover-descent: the latter assumes covering objects in a small site with fibre products. The spaces M,U here are sheaves rather than objects of the big scheme site; making that transition is precisely the new input.
lem-sfb-fppf-space-datum-sheaf-realization vs lem-sfb-keel-mori-stabilizer-preserving-etale: its 0ADT source reference supports a moduli-square argument; its statement asserts a cartesian coarse-moduli square, not the sheaf realization equivalence.
lem-sfb-fppf-space-datum-sheaf-realization vs lem-sfb-etale-space-single-cover-effective-descent: the new input only constructs a sheaf over an arbitrary fppf algebraic-space cover. It asserts neither that the sheaf is algebraic nor that its map is etale. These are proved in item steps 3 and 4 with existing nodes.

I searched the full DAG for 0ADT, descent-data-sheaves, descent/sheaf equivalences, and algebraic-space descent. Blueprint searches included 0ADV, 0ADT, 042B, descent data, effective descent, sheaves over, and algebraic spaces. No existing statement gives the new prerequisite. The existing fppf bootstrap and property-descent statements are reused. Mathlib search results are recorded without changing their query text, with the real search records from searches.jsonl. I read the returned abstract IsStack and regular-epi declarations: the former requires the stack property, and the latter supplies a kernel-pair coequalizer, not the new descent equivalence. No hit is a one-line specialization of the required result.

## Review by Q144

I read bootstrap.tex Tag 0ADV (lemma-descend-algebraic-space), its proof of (1), spaces-descent.tex Tag 0ADT (lemma-descent-data-sheaves), and Tag 042B (lemma-descending-property-etale). For the new node I checked the whole 0ADT statement and proof: it constructs a coequalizer sheaf, identifies its local pullbacks, and states an equivalence, without assuming finite type. Its omitted quasi-inverse checks are left to this new node's later split, rather than silently reproduced as an elementary fact in this item's argument. I also read the definition of fppf algebraic-space coverings in spaces-topologies.tex and the final-bootstrap theorem in bootstrap.tex.

Step 1 uses the chartwise-calculus statement for etale implies flat and locally finitely presented. The explicit fppf-covering hypothesis of the new node then applies: surjectivity is given. The normalized theta cocycle gives the required datum with the ordered factors shown. I did not infer quasi-compactness from etaleness.

Step 2 takes only sheaf realization and its specified overlap comparison from the new node. It does not take algebraicity from that node. Step 3 verifies every hypothesis of lem-sfb-fppf-space-atlas-bootstrap as stated: F is an fppf sheaf, V is an algebraic space, and for every test T and x in F(T) the displayed natural inverse maps identify the required fibre with T times_M U. The fibre-products/cover-base-change statement gives an algebraic space and surjective etale projection. The chartwise-calculus statement supplies flatness and local finite presentation. I opened all three statements and checked these exact conclusions. There is no diagonal hypothesis in the bootstrap statement, so no diagonal hypothesis is silently supplied. The site and universe stay those of the item; the singleton construction does not require a coproduct-size argument.

Step 4 uses the existing representable-fppf-etale-open-descent statement's explicit algebraic-space clause, with q=a and the three cover hypotheses already verified. I checked that the etale property is independently included and no source-local etale assertion is being used. Its source Tag 042B is target locality. In particular I do not call a non-quasi-compact a an fpqc morphism; the existing node states the needed fppf target-local version.

Step 5 uses the new equivalence on morphisms, with the existing fibre-products statement ensuring N_i times_M U belongs to its local algebraic category. The definition of algebraic spaces identifies natural transformations with morphisms. Descending both inverse arrows and using injectivity proves uniqueness and invertibility explicitly. All ten citations have quotes copied literally from the statement, rather than from a proof. The retained item statement's notions already have its five statement dependencies; the new node introduces its cover, category, arrows, cocycle, sheaf pullbacks and every ambient object explicitly.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the files and sources: the only new node has no proof, no hidden construction, and no mathematical hypothesis absent from 0ADT. It is a prerequisite before algebraicity, not a renamed conclusion. No step is marked elementary. Each proof step is shorter than 2000 characters; the longest is the written-out uniqueness argument, and the pullback comparison is just the universal property with natural inverse maps. The new statement works for the identity cover (the comparison is the identity equivalence), for empty base and empty covering (only the empty slice sheaf can occur), and for non-quasi-compact etale objects (no finite-type or quasi-compactness assumption is used). For the item, V empty descends to the empty space; the identity cover descends to V with its forced identity comparison. No source error or statement dispute was found. No off-unit proof tool is needed: the reused geometric nodes have the item's unit.

## Unfinished work

The new prerequisite is intentionally statement-only, for the next stage-1 worker. Nothing in this assigned one-level split remains unfinished.
