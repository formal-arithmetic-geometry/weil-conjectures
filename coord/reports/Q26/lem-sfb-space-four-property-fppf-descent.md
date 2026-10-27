# Q26 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-four-property-fppf-descent.json`: existing statement, now split into nine steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-fppf-finite-affine-refinement.json`: one new statement-only lemma, status unsplit; no Mathlib match. It constructs a finite affine scheme refinement of a covering with algebraic-space members over an affine test scheme, including the affine faithfully flat coproduct.
- `citations.json`: an entry for every cited node in every step, quoting its exact statement.
- `searches.jsonl`: the ten actual launcher search records, retained without rewriting their results. `write_split.py` is the sandbox-only generation helper.

## Attachments

None. Searches of the read-only project Lean library for the item's blueprint tag and the algebraic-space notion did not find a declaration proving this item. Both Lean audit states were none. No Lean file was written or compiled.

## WANTED

None. All sources used are already in the literature checkout.

## What needed correction

The live item was unsplit, with no proof. Its statement has been retained, including the precise convention that quasi-finite means finite type with finite geometric fibre point sets. For arbitrary algebraic spaces one must not silently replace this by the chartwise definition in Stacks 0427: finite point sets need not be discrete without further assumptions. Steps 1 and 8 prove exactly the stated finite-point-set assertion by fibre products and field extensions. No statement dispute or added hypothesis is necessary.

The existing quasi-compactness descent input tests quasi-compact algebraic spaces, whereas the item tests quasi-compact schemes. I wrote out the equivalence using quasi-compact scheme atlases and the cited base-change/composition permanence of representable surjective etale maps. I also replaced an implicit assertion that an affine-to-affine scheme map is affine by the existing affine-open-cover criterion, applied to the singleton cover. The affine argument first obtains scheme representability from the stronger existing quasi-affine descent statement; only then does it use scheme affineness descent. The diagonal argument likewise establishes representability before using scheme descent.

The inherited blueprint ancestry has no blueprint node: `blueprint_refs.py ancestor` reports null. I retained its existing place and complete alteration/moduli via chain, and placed the new refinement immediately below this item. The current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, chapter and unit were read. This item supplies the space-property locality input for the representable-stack argument in that route; it does not replace the alteration/moduli argument. Searches of the whole blueprint for fppf, quasi-finite, affine, affine refinement and 0DFQ found no equivalent blueprint node. Generic off-unit scheme descent, coproduct, field-amalgamation and algebraic-space foundations are declared in `split_report.tool_uses`.

## What remains unfinished

Only the new refinement lemma remains statement-only, as required for a one-level split. Its proof is the finite affine-chart refinement in the proof of Stacks 0DFQ. The item itself has a complete assembly proof. There are one new node and zero new Mathlib leaves.

## Searches and reuse

Before creating the refinement I searched the whole DAG by its tag 0DFQ and by fppf/affine/refinement keywords, as well as the project Lean source and the whole blueprint. Existing scheme-only refinement and fppf-to-fpqc results cannot accept algebraic-space covering members; the existing space locality results do not assert the refining maps and their factorization data. I reused the finite-type and separated base-change, local finite type and quasi-compactness results, quasi-affine representability descent, the scheme descent results, the coproduct results and the common-field-extension lemma.

The item has five logged searches: LeanFinder twice with different phrasing, LeanSearch, Loogle and a full Mathlib grep. The new node has five: LeanFinder with two phrasings, LeanSearch, Loogle and AlgebraicGeometry grep. All services answered. The search records in both nodes use exactly those query texts. I read the returned scheme precoverage results in `Mathlib/AlgebraicGeometry/Sites/Fpqc.lean` and the scheme-cover refinement in `Mathlib/AlgebraicGeometry/Cover/QuasiCompact.lean`; neither constructs scheme refinement of algebraic-space members, and there is no AlgebraicSpace occurrence in the full Mathlib search. Scheme-only hits do not specialize to the statements here. All inherited item searches, citations and metadata have been preserved.

## Not duplicates

lem-sfb-space-fppf-finite-affine-refinement vs lem-sfb-space-quasicompact-fppf-local: the latter descends quasi-compactness of a morphism; the new node constructs finitely many affine schemes, maps factoring through specified covering members and an affine flat surjective coproduct over an affine test. Its proof uses related 0DFQ refinement material but its statement does not supply these data.

lem-sfb-space-fppf-finite-affine-refinement vs lem-sfb-space-quasi-compact-immersion-locality: that node descends immersions and quasi-compactness; it does not construct affine scheme refinements of covering families.

lem-sfb-space-fppf-finite-affine-refinement vs lem-sfb-space-lft-smooth-fpqc-locality: local finite type locality is a property theorem, with no finite refining scheme family or factorization data.

lem-sfb-space-fppf-finite-affine-refinement vs lem-sfb-space-flat-proper-fp-locality: flat/proper/finite-presentation locality does not construct an affine scheme refinement of an algebraic-space covering.

lem-sfb-space-fppf-finite-affine-refinement vs lem-pc-fppf-affine-refinement: the existing refinement starts with a covering by schemes. The new lemma permits arbitrary algebraic-space members, with etale scheme charts needed before scheme refinement can be applied, and allows an affine test mapping to an arbitrary algebraic-space target.

lem-sfb-space-fppf-finite-affine-refinement vs lem-trf-space-qc-finite-affine-atlas-refinement: that node selects a finite subfamily of a specified etale scheme atlas of a quasi-compact space. The new node refines a flat locally finitely presented covering with algebraic-space members and supplies flat locally finitely presented scheme arrows over the affine test and their factorization through those members. Its covering need not be etale.

## Review by Q26

I read delivery-errors B through E and checked the split against their mathematical objections, especially missing lemmas and citations that state less than a step needs. For the item I read Stacks spaces-descent 041Z, 041U, 0421 and 0427 with their proofs, and the base-change statements in spaces-morphisms 03WI, 03XH and 03KL. I read spaces-descent 0423 because it supplies the representability input reused in Step 4; descent 02L5 and 02L6 for the scheme descent applications; morphisms 01S8 and the closed-immersion affine criterion 01QO; and limits 0CNJ for the common-field-extension construction. For the one new node I read spaces-topologies 0DFQ, including the affine etale charts of the pullbacks and the finite subcover of their open images, as well as the fppf covering conventions 03Y8 and 03Y9. No SGA source was used.

Step 1 proves affine base-change stability directly on affine tests using the fibre-product universal property. It uses the existing stack finite-type calculus (which explicitly states agreement on algebraic spaces) and space separated composition/base change for the other base-change assertions. I read those statements and checked their hypotheses admit arbitrary h. The first dry run exposed a live dependency of the affine-locality node on this item, so I removed that citation and wrote out the direct test argument to avoid a cycle. The quasi-compact convention comparison uses the representable-etale scheme-test lemma's actual composition and arbitrary-space base-change clauses and the affine-test equivalence; the finite-fibre assertion is proved directly by an explicit universal-property identification.

Step 2 uses the new refinement's actual finite family, factorization maps and flat surjective affine coproduct. The sheaf fibre-product node supplies existence and the universal property. The iterated fibre products are identified by matching their pairs of sections; this does not use a missing comparison lemma.

Step 3 uses the exact clopen-partition description of sheaf coproduct sections, the scheme coproduct universal construction, and the finite-affine-coproduct spectrum statement. I checked the finite hypothesis: J is finite by the new refinement, even when the original covering is infinite. The identification is expanded on sections and restrictions instead of being hidden behind a representability assertion. The affine sources E_j follow from the affine property already established by Step 1 and the item's definition.

Step 4 uses quasi-affine descent only under its stated hypotheses: T and T' are affine schemes and p is flat surjective; no finite type or separation of E is assumed. The whole affine open is quasi-compact by the cited affine-scheme qcqs statement. After descent E is a scheme, so the scheme fpqc affineness result applies. The singleton affine-open-cover criterion supplies affineness of E' to T'; the defining inverse-image criterion then supplies affineness of E itself.

Step 5 uses actual locality statements, not definitions, for local finite type and quasi-compactness. Their fppf families allow arbitrary algebraic-space members. The convention comparison proved in Step 1 bridges their hypotheses and conclusions with the item's scheme-test definition, so finite type has precisely its two required parts.

Steps 6 and 7 use the representable absolute diagonal from the algebraic-space definition to make every relative-diagonal scheme test a scheme. I wrote out the section identification; equality of the two X coordinates is precisely the diagonal condition after refinement. The affine-cover closed-immersion criterion is used in both directions exactly as stated. The fppf-to-fpqc statement and closed-immersion descent are scheme results: they are applied only to V_j over T_0 and to the already represented scheme morphism. No scheme hypothesis on X or X times_Y X is imposed.

Step 8 uses the joint-surjectivity definition's field-extension lift, the algebraic-closure existence in its cited definition, and the common-extension lemma for the two extensions K/Omega and Lambda/Omega. I checked that the common embeddings agree on Omega, so they actually define a point of the required fibre product. Finiteness then passes through a surjective map of point sets. This establishes the literal geometric-fibre conclusion without chartwise quasi-finiteness or a finiteness-of-rational-points assumption.

Step 9 transports tests, atlases and compatible chart pairs along the two arrow isomorphisms. The chart-test node explicitly tests local finite type on these scheme maps, and the diagonal and fibre-product definitions give the displayed test correspondences. Empty targets and the empty covering were checked: an arrow to the empty sheaf has empty source, and all tests satisfy the properties. Identity covers, empty affine tests, singleton refinements and infinite initial coverings give the expected conclusions. The new lemma allows J empty only as needed for the empty test; finite selection over a nonempty affine test gives a jointly surjective nonempty family. It assumes no quasi-separatedness of the target or members.

Every step's cited node statement was opened and read; citations.json quotes those statements verbatim rather than paraphrasing their claims. No new node restates a clause of the item: the sole new lemma is the common covering construction used for affineness and the diagonal. Elementary fibre-product comparisons, finite-image reasoning and singleton-cover arguments are written in the steps. None of the steps exceeds 2000 characters. The imported statement, dependencies and blueprint history have not been weakened. I checked the remaining source assumptions and small cases above and corrected the two convention/citation gaps described earlier. This is my mathematical self-review of the split.

## Dry-run repairs

The first full dry run found a live cycle through lem-sfb-space-affine-locality and a wording check on an external reference to the item. I replaced the affine-locality citation by the direct affine-test argument and changed the wording to name the quasi-compact-scheme tests explicitly. The mathematical statement and the new lemma were unchanged.
