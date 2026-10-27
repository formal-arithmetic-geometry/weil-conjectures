## Worker report

Files written under dag/nodes/sec-six-functors-basics/:

- lem-sfb-space-proper-noetherian-approximation.json: item, split into seven proof steps; statement unchanged; no Mathlib match.
- lem-sfb-proper-space-fixed-base-fp-limit.json: statement, unsplit; no Mathlib match (0A0W, fixed scheme base).
- lem-sfb-fp-space-qcqs-base-limit-descent.json: statement, unsplit; no Mathlib match (07SK over general qcqs scheme bases).
- lem-sfb-space-qcqs-base-eventually-proper.json: statement, unsplit; no Mathlib match (08K1 over general qcqs scheme bases).
- lem-sfb-space-qcqs-base-descend-closed-immersion.json: statement, unsplit; no Mathlib match (0850 over general qcqs scheme bases).

citations.json contains verbatim statement extracts for all proof-step citations. Searches are retained in searches.jsonl and the per-node search-results.json files. All four supporting nodes have empty proofs and proof dependencies. No new Mathlib leaves.

Attachments: none for this item. The project source was searched by the exact blueprint tag and by proper/Noetherian approximation terminology. The scheme-only NoetherianApproximation and nonempty_noetherianApproximation declarations, read in WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean, are not an attachment for an algebraic-space source. Their existing DAG nodes are reused. No Lean was written or compiled.

WANTED: none. All sources used are present locally.

The imported node had no proof. Its Stacks proof ends with “Some details omitted”, after selecting models and arrows individually. Independent selections do not establish a compatible system or affine transitions. The delivery supplies a category containing all proper finite-presentation models, restricts its arrows to closed immersions over base transitions, proves cofilteredness by descent and eventual closed immersion, and verifies its limit directly before directed reindexing. This retains the source route. It neither moves the conclusion into one new node nor creates a node for an elementary assembly operation. The fixed-base approximation is different from the item: its base stays T and its models need not be Noetherian or descend to an integer-finite-presentation base.

The existing affine-base 07SK and 08K1 statements cannot be applied directly to the possibly nonaffine scheme stages. I added the general qcqs-scheme-base versions actually supplied by Stacks rather than dropping the nonaffine case. The statement of the item is correct; no STATEMENT-DISPUTED change was necessary. The blueprint ancestor command returns None, consistently with the inherited null ancestor. I retained the recorded ancestry and filled every new from.place with the precise supporting input; same_as searches found no matching imported blueprint statement. The latest direct-images proof (3) was read; this supplies its inherited proper-family prerequisite without changing a chapter or unit route.

Nothing unfinished within this one-level split. The four prerequisite statements remain unsplit for later workers as required.

## Not duplicates

lem-sfb-fp-space-qcqs-base-limit-descent vs lem-sfb-fp-space-limit-category: the existing statement requires every T_i affine; the new statement permits nonaffine qcqs scheme stages. Object, morphism and equality descent are needed in precisely this greater generality.
lem-sfb-fp-space-qcqs-base-limit-descent vs lem-sfb-space-invertible-limit-descent: the latter descends invertible modules on a given space system; it does not descend algebraic-space objects or morphisms.
lem-sfb-space-qcqs-base-descend-closed-immersion vs lem-sfb-space-eventually-fibre-dimension: the latter is a dimension bound for fibres over affine stages, not closed-immersion descent.
lem-sfb-space-qcqs-base-descend-closed-immersion vs lem-sfb-space-eventually-flat: the latter descends flatness over affine stages, not closed immersion.
lem-sfb-space-qcqs-base-descend-closed-immersion vs lem-sfb-space-descend-separated: the latter descends separatedness over affine stages; a separated map need not be a closed immersion.
lem-sfb-space-qcqs-base-descend-closed-immersion vs lem-sfb-space-eventually-proper: the latter descends properness over affine stages; a proper map need not be a closed immersion.
lem-sfb-space-qcqs-base-eventually-proper vs lem-sfb-space-eventually-fibre-dimension: fibre dimension and properness are different properties; the new bases can also be nonaffine.
lem-sfb-space-qcqs-base-eventually-proper vs lem-sfb-space-proper-base-change: base-change stability gives persistence of properness, not its detection at a finite stage.
lem-sfb-space-qcqs-base-eventually-proper vs lem-sfb-space-flat-proper-fp-locality: locality and arbitrary base-change stability do not assert eventual properness in a limit.
lem-sfb-space-qcqs-base-eventually-proper vs lem-sfb-space-eventually-flat: flatness is a different property; the new bases can also be nonaffine.
lem-sfb-space-qcqs-base-eventually-proper vs lem-sfb-space-descend-separated: separatedness is only part of properness; the new bases can also be nonaffine.
lem-sfb-space-qcqs-base-eventually-proper vs lem-sfb-space-eventually-proper: existing 08K1 node requires affine T_i; the new node covers qcqs scheme T_i as used here.
lem-sfb-proper-space-fixed-base-fp-limit vs lem-weil-pbc-proper-limit-noetherian: the existing statement requires X a scheme and moves the base; the new 0A0W statement allows X an algebraic space and keeps T fixed.

lem-sfb-space-qcqs-base-descend-closed-immersion vs lem-sfb-space-relative-lfp-permanence: the newly live 05WT statement establishes local finite presentation of a morphism; it does not assert detection of a closed immersion at a finite inverse-system stage. It supplies the local-finite-type hypothesis used to justify the source of the new 0850 statement.

lem-sfb-space-qcqs-base-descend-closed-immersion vs lem-sfb-space-descend-closed-immersion: the newly live statement requires an inverse system of affine T_i; the new statement permits nonaffine qcqs scheme bases. The stage spaces in the new node are finitely presented, so the local-finite-type requirement of 0850 holds, but the affine-base restriction of the existing node still prevents its direct application.
lem-sfb-space-qcqs-base-eventually-proper vs lem-sfb-space-descend-closed-immersion: the latter detects closed immersions, not proper structural maps, and assumes affine bases.

lem-sfb-space-qcqs-base-eventually-proper vs lem-sfb-space-proper-strict-local-test: the newly live statement tests properness after every strict localization of one fixed scheme base; it does not detect properness at a finite stage in an arbitrary affine-transition system of qcqs scheme bases.

## Review by Q115

I read spaces-limits.tex at 0A0X and its cited 0A0W before writing the proof. For the four new nodes I read respectively 0A0W, 07SK (the object/morphism/equality descent statement and proof), 08K1 with Situation 084W, and 0850 with that same situation. For 0850 I also read spaces-morphisms.tex 05WT: a morphism between finitely presented spaces over a common base is locally finitely presented, hence locally finite type, so the local-finite-type hypothesis of 0850 is available. The qcqs hypotheses of Situation 084W hold because all its spaces are finitely presented over qcqs stages. The statements are restricted to scheme bases, not silently extended beyond the source. I read the base-change and finite-presentation composition statements and the elementary affine/closed-immersion tests in spaces-morphisms.tex as well.

Step 1 uses the complete conclusion of the new fixed-base approximation. The existing scheme approximation proposition really gives an affine-transition system of finite-type integer schemes and a limit, and its definition explicitly says the stages are Noetherian. I read the recorded Lean structure and theorem as a cross-check of these clauses. The directed-reindexing node preserves both the cone and the term/transition properties. The locally-Noetherian-quasi-separated node supplies quasi-separatedness, and pqf-lem-lft-fp-locnoeth gives local finite presentation over Spec Z; finite type supplies quasi-compactness. This step never treats a proper finite-type morphism as finitely presented over an arbitrary non-Noetherian base.

Step 2 takes object descent from the new 07SK node and properness detection from the new 08K1 node. The existing flat/proper/fp-locality statement explicitly preserves each property separately under any base change, so it permits common later stages. The separate fp-composition node says exactly that two finitely presented space maps compose. Applied to the model and T_j over Z it gives absolute finite presentation. Qcqs of the absolute source is read from the stated qcqs definition over affine Spec Z; there is no appeal to an unstated Noetherian algebraic-space theorem.

Step 3 only assembles data and compositions. The closed-immersion definition supplies the affine quotient-ring test, so composition and base change here are verified on scheme tests, by composition and tensor base change of surjections. The fibre-product node really constructs sheaf fibre products of spaces, not merely scheme products. The size-convention node gives the larger universe: all models and morphisms of the smaller-universe spaces form a set there. Thus no large indexing category is fed to a small-limit theorem.

Step 4 uses both the morphism descent and eventual equality clauses of the new 07SK statement. Its objects are finitely presented after base change by the cited locality statement. The new 0850 statement supplies exactly closed-immersion detection for a stage map between those objects. I checked that the source's local-finite-type hypothesis is ensured as above. The argument treats two objects and parallel arrows separately, proving both cofilteredness axioms. For objects with identical K-index the common refinement can retain it; this additional observation is used later and follows from descending the identity comparison of their two models. An imposed lower bound on J is respected by first passing to a common later stage.

Step 5 does not create an affine-permanence node. On an affine test W the projection is affine by the already given definition of the base transition, and the other factor is a closed subscheme of that affine scheme by the cited closed-immersion definition. Hence the total source is affine, which is precisely the conclusion required on that test. This is an elementary argument, not a hidden invocation of Chow's lemma or a properness descent result.

Step 6 uses the existing affine-space-limit node for exactly its sheaf-limit assertion, so the scheme cone of the base is valid against algebraic-space tests. The rest is an explicit universal-property argument: common refinements make the base family independent of its model, fixed-K refinements do the same for maps to X_k, and refinements with K-index l prove compatibility for l >= k. The fixed-base limit proved in step 1 supplies the unique map to X. The converse is written down, so an isomorphism of underlying objects is not assumed to commute with the structure map. Step 7 applies only the existing directed-reindexing statement to this already verified limit of arrows; every clause, including the same f, is retained.

I checked the delivery-errors B--E cases with the statements open: definitions and all object hypotheses are included; the source tags were checked against tags/tags; no new unsplit node has a proof; every non-elementary use is a node citation; quotes are copied verbatim from the actual statements; no statement is used for more than it says; scheme-only nodes are never applied to a nonschematic source; all new nodes are strict prerequisite results, not clauses of the requested conclusion. New nodes have no proof dependencies and only foundational statement dependencies, so they introduce no backwards proof cycle.

I searched the full DAG and the blueprint by source tags and notions, and the project Lean by tag and approximation terminology. Mathlib searches were run only through msearch.py: each of the item and four new nodes has two distinct semantic phrasings, Loogle, grep, and LeanSearch recorded from their actual output. I read the hits: they concern schemes, ring presentations, scheme limit calculations, or general category results and do not state the algebraic-space results. All services returned successfully. No unrun query is recorded.

For edge cases I checked empty X, empty T, a singleton approximation, a finitely presented proper f already defined at a stage, and nonseparated but qcqs T. Empty models cause no nonemptiness assumption on X: the model category is nonempty by existence of models, while the directed index is independently nonempty. Cofilteredness uses no surjectivity or faithful flatness of T -> T_j, so a non-surjective projection is allowed; eventual equality supplies the needed finite-stage conclusion. Closed immersion is stronger than properness, and step 4 does not infer it from properness. The source argument does not require f to be representable or X a scheme. Every step is shorter than 2000 characters; the limit comparison is one routine universal-property computation with the maps and inverses written explicitly.

No mathematical statement was corrected. During drafting I replaced independent arrow choices by the full category of models, corrected the general-base hypotheses against the affine-only existing nodes, and made the affine-transition and compatibility checks explicit. Generic off-unit scheme approximation and algebraic-space limit/fibre-product tools are declared in split_report.tool_uses; no route is replaced.

The first dry run found a newly live same-tag node, lem-sfb-space-relative-lfp-permanence (05WT). I opened its full statement and distinguished it above: it is the permanence prerequisite already checked in the Stacks source, not closed-immersion descent. No mathematical or node changes were needed.

The second dry run detected the newly live affine-base lem-sfb-space-descend-closed-immersion. I read its statement and recorded both requested distinctions; its affine-base assumption does not cover the nonaffine T_j used here.

The first push encountered a further newly live node, lem-sfb-space-proper-strict-local-test. I read its statement; it is a strict-local corollary, not eventual properness over arbitrary qcqs inverse systems. The difference is recorded above.

A later gate detected an edited definition paragraph in the live fp-composition statement. I read the revised statement: the clause used, "If both are of finite presentation, then g composed with f is of finite presentation", remains unchanged. I replaced its full-statement citation extract by that exact verbatim clause; the proof needs no change.
