# Stage-1 repair: lem-coef-simplicial-local-bounded-lifting

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-local-bounded-lifting.json`: split statement, unchanged statement, six proof steps.
- `dag/nodes/sec-six-functors/lem-coef-bousfield-smith-bounded-generation.json`: one new unsplit statement, now the bounded-subobject lemma rather than the whole generation conclusion; no Mathlib match.
- `citations.json`: verbatim statement excerpts for each cited node in every item step.
- `report.md`: repair report and signed review.

The earlier sandbox report, item, citations and proposed nodes are retained in `repair-history/`. The unlanded proposed Mathlib leaf `lem-coef-lifting-coproduct-transfinite-closure` is retained there rather than included in the delivery: the repaired proof uses no coproducts and cites the existing pushout and transfinite closure nodes directly. There is one new node and zero Mathlib leaves in the delivery. No existing repository node was deleted or edited outside this item.

## Attachments

None. Read-only searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, Bousfield–Smith, bounded subobjects and local bounded lifting found no declaration of this result. The upstream master material is reference material, not evidence of a completed proof.

## WANTED

WANTED: Rezk, *A model for the homotopy theory of homotopy theory*, Proposition 9.1, final proof paragraph, printed p. 22, for the item. Read online at https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/rezk-segal-spaces.pdf; not in literature/. This paragraph states the bounded-generator claim and names the Bousfield–Smith argument; it does not supply that argument.

WANTED: Hirschhorn, *Model Categories and Their Localizations*, Chapter 4, Sections 4.4–4.5 (localization of subcomplexes and the Bousfield–Smith cardinality argument), for `lem-coef-bousfield-smith-bounded-generation`. The book is absent from literature/. The online Edinburgh PDF was found but the reader could neither extract its text nor render the attempted pages; the AMS endpoint was inaccessible. I do not claim to have read its detailed proof or verified an exact numbered theorem. The node explicitly records an agent-formulated specialization of this input, as requested by the maintainer, rather than inventing a theorem number. No source was downloaded or written to the shared repository.

## What was wrong and what changed

D5/E5 and C1: the returned Step 2 named the Bousfield–Smith argument but supplied none of its boundedness input. A retained partial repair merely made the whole retract-generation assertion into another node, which still moved the item into a new node. I replaced that assertion with the bounded-intersection enlargement statement: inside a local-equivalence inclusion X into Y, each small C is contained in a bounded D for which X intersection D into D is again a local equivalence. This is a genuine subobject input, not a statement about lifting classes or cellular generation. Its own proof remains unsplit; in particular the localization construction, accessibility rank and weak-equivalence detection needed to prove this input are not silently asserted in an item step. The item now proves its mapping-space lifting characterization, closure properties and complete successor/limit filtration from that input.

C4: `lem-coef-lifting-class-closure` is used only for its actual identities, binary composition and pushout claims or its definitions. `lem-coef-transfinite-left-lifting` is cited explicitly in Steps 3 and 5. The filtration adds one bounded subobject at each successor, so neither arbitrary coproduct closure nor an unproved closure theorem is needed.

The returned Step 3's unsupported claim of a bounded failing map is gone. Step 6 is the direct reverse inclusion from the definition of the representative family. The proof establishes the forward inclusion by extending over the explicitly constructed filtration, so it needs no contrapositive claim of that form. The item's statement, fixed f, every local-object test, size convention and arbitrary-representative quantifier remain unchanged.

## Not duplicates

`lem-coef-bousfield-smith-bounded-generation` vs `lem-coef-presheaf-weak-mono-bounded-enlargement`: the existing statement uses a presheaf interval, an anodyne class satisfying two interval pushout-product conditions, and bijections of interval-homotopy classes into naive fibrant objects. The new input uses Reedy fibrant simplicial spaces and weak equivalences of mapping simplicial sets for a fixed f. None of the interval/anodyne hypotheses or the identification of these two equivalence tests is supplied by that existing statement, so this is not a one-line specialization. I read its full statement and proof rather than importing its conclusion without those hypotheses.

`lem-coef-bousfield-smith-bounded-generation` vs `lem-coef-presheaf-bounded-intersection-replacement`: the existing statement constructs an injective replacement preserving intersections and size for a given set of monomorphisms; it says nothing about f-local equivalences or making an intersection inclusion a local equivalence.

`lem-coef-bousfield-smith-bounded-generation` vs `lem-coef-accessible-intersection-generators`: the existing statement assumes an accessible arrow class and weak saturation, and concludes a small generating set. The new statement is a uniform bounded enlargement of actual subobjects for the specified mapping-space equivalences; it does not assume accessibility and does not conclude cellular generation.

`lem-coef-bousfield-smith-bounded-generation` vs `lem-coef-accessible-localization-small-generators`: the existing node concerns detecting objects in an accessible reflective localization, not bounded intersection inclusions inside a local-equivalence monomorphism.

Before retaining the revised node I searched the whole DAG by Bousfield/Smith, bounded-subobject and local-equivalence terms and ran whole-blueprint searches for Bousfield, bounded subobject, subcomplex and local equivalences. No blueprint node states this Reedy mapping-space input. The nearest ancestor is `prop-coef-integral-exceptional-adjoint`; ancestry and via are retained. The current main-20261015 ancestor proof was read: this is supporting simplicial-space infrastructure of the inherited chain, not a literal claim in its coefficient-adjunction paragraph.

## What could not be finished

The bounded-subobject input is unsplit, deliberately, as the return authorizes. Its detailed localization/cardinality proof and archival source remain future work on that node. No compiler, Lake, Lean writing, live git command or push was run.

## Review by N4

I compared the retained sandbox with the current shared item, which is unsplit with empty proof. I read the stage brief, stage-1 contract, SETUP's three levels, GOAL, dag-sync, delivery-errors B–E in full, and the chapter/unit records. The proof stays on the inherited Rezk localization branch and introduces no SGA source. The current ancestor proof concerns derived coefficient adjunctions; the item was already introduced through the long mapping-space infrastructure chain. I did not alter that unit or pretend the auxiliary Rezk assertion is literally in the ancestor paragraph.

For the item I read Rezk Proposition 9.1 and its final paragraph online. It fixes one inclusion f, defines the fibrant testing objects and mapping-space equivalences, and uses a sufficiently large uncountable bound on generators. The item uses a total-simplex bound; an uncountable regular cardinal makes this equivalent to bounds on countably many bidegrees. For the new node, the source limitation is recorded explicitly above; its statement is the bounded-subobject formulation requested in the return, with all variables and the strict total-size bound introduced, no proof in its statement and no claim of a localized model structure. It is true in the identity-f case by bounded weak-equivalence enlargement, and in the empty-to-point case the local tests are contractible or empty where applicable. I checked X=Y directly (choose D=C), C empty, and the case of a countable simplex-generated subobject. The cardinal is strictly uncountable so this last case fits its strict inequality. I did not assume the bound can be arbitrarily increased while preserving the enlargement property.

Step 1 cites exactly the bounded-subobject node for gamma. All remaining representative coding uses countably many ordinal sets and function sets; these are small in the fixed universe. Isomorphism invariance is justified by inverse precomposition maps. The obsolete independent lambda-bound citation was removed.

Step 2 uses the actual mapping-fibration clause of `lem-coef-simplicial-space-reedy-cartesian`, with a monic i and the Reedy fibration Z to 1. Its Kan-fibration conclusion is therefore available. The Kan node supplies the exact boundary lifting characterization, including n=0. I spelled out the squares under the internal-hom definition, and the lifting-class node supplies the notation. This proves the characterization without assuming the localization model structure being constructed by the parent.

Step 3 cites the precise pushout/composition clauses of the lifting-class node and the ordinal/continuity theorem of the transfinite-left-lifting node; I opened and read both statements. Monicity of pushouts and unions is checked degree by degree with the explicit set construction and gluing universal property. Two-out-of-three comes from the Kan model and model-axiom statements, also opened and read; it is applied to mapping maps, not assumed for an undefined localized model.

Step 4 cites the well-ordering and transfinite-recursion statements, read in full, and the bounded-subobject input. Its invariant contains both A to E_alpha in T_f and E_alpha to B in W_f. Thus the enlargement input is applied only to an inclusion already proved a local equivalence. At successors the intersection is E_alpha intersection D_alpha, not A intersection D_alpha. At limits the chain is continuous by its union definition, and Step 3 supplies the induction invariant. No E_alpha is claimed bounded. Only D_alpha needs the bound. The domain E_alpha intersection D_alpha is automatically bounded as a subset. The recursion uses a well-order on the small set of subspaces to fix witnesses, and includes a fallback on invalid prefixes, so its rule is total. Every target simplex is inserted by its enumerated stage, and E_theta=B. For B empty the ordinal is zero and the invariant gives the identity case.

Step 5 uses only arrow-isomorphism transport of a square, pushout closure as actually stated, and the existing transfinite lifting theorem with the singleton class containing p. It gets A to B from the constructed filtration; no assertion about retracts, arbitrary coproducts or bounded failing maps is hidden. Step 6 uses the lifting-class definition and is elementary. For the two generic set-theoretic nodes I declared tool uses; they do not replace a unit's mathematical route.

All new-node Mathlib searches were run through msearch.py and their actual results are retained in searches.jsonl and the result files. The original claimed searches had no sandbox log, so I replaced the new-node records with the searches actually performed on this repair, tried two semantic phrasings, and reran the item's inherited queries. I read the hits: SSet skeleton/mono facts do not preserve local equivalences, Grothendieck-abelian generating monomorphisms require an abelian category, ordinary Bousfield orthogonal reflection tests Hom-set bijections, and small-object theorems assume a supplied generating set. None supplies this bounded-subobject lemma. I read the corresponding Mathlib source fragments. The actual Mathlib transfinite/coproduct closure theorem exists at line 303, but its proposed separate leaf is unnecessary and was removed from the delivery rather than recording the earlier incorrect line 159. Every item citation has a verbatim excerpt in citations.json. No statement dispute or change was necessary.

## Second reading by N4

- Item statement: checked against Rezk Proposition 9.1, clauses (1)–(4) and the final paragraph (printed pp. 20–21), with total-size bound compared to the source's per-degree bound; verdict: hypotheses and quantifiers are retained, and the regular uncountable cardinal makes the two countable-degree size conventions equivalent.
- New node `lem-coef-bousfield-smith-bounded-generation`: checked its self-contained definitions against Rezk's f-local objects and local weak equivalences and the Bousfield–Smith bounded-subobject input used to justify the final paragraph; verdict: statement-only, no proof dependencies or Mathlib match, and edge cases `X=Y`, empty `C`, and a countable simplex-generated `C` behave as stated.
- Step 1: checked the bounded-subobject citation and the small-representatives argument; verdict: the cited node supplies the cardinal and bounded enlargement, while the representative and arrow-isomorphism argument is explicit.
- Step 2: checked `lem-coef-simplicial-space-reedy-cartesian`, `lem-coef-kan-quillen-right-proper`, and `lem-coef-lifting-class-closure`; verdict: the mapping map is a Kan fibration for a monomorphism into a Reedy-fibrant object, and the boundary lifting correspondence includes `n=0`.
- Step 3: checked the exact identity, composition, pushout, and transfinite clauses of `lem-coef-lifting-class-closure` and `lem-coef-transfinite-left-lifting`, plus two-out-of-three from the model nodes; verdict: monicity and local-equivalence closure are argued degreewise and no coproduct closure is used.
- Step 4: checked `lem-weil-pbc-well-ordering-theorem`, `lem-weil-pbc-transfinite-recursion`, the bounded-subobject node, and the invariant at zero, successor, limit, and empty-target cases; verdict: the intersection is `E_alpha ∩ D_alpha`, only `D_alpha` is bounded, and the filtration reaches `B`.
- Step 5: checked transport across arrow isomorphisms, pushout closure, and the singleton-class application of `lem-coef-transfinite-left-lifting`; verdict: it proves the forward inclusion without retract or coproduct assumptions.
- Step 6: checked the definition of `T_f^square` and the representative inclusion; verdict: the reverse inclusion is elementary and correctly marked.

Changes made in this second reading:

- Corrected the item's `created.item` metadata to `lem-coef-simplicial-local-bounded-lifting`; the prior value named a different item and would fail delivery preflight.
- Added this section to record the source, hypothesis, dependency, edge-case, and step-by-step checks required for a second reading.
