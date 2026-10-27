# Stage-1 delivery: lem-sfb-space-change-base-to-integers

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-change-base-to-integers.json — item, split into six steps; Mathlib has no exact match.
- citations.json — eleven step/node entries, each checked against the current node statement as a literal substring.
- report.md — this report.

No new nodes; no Mathlib leaves. searches.jsonl is the search command's own log. The sandbox initially contained only dispatcher brief markers; there was no earlier split or report to discard.

## Attachments

None. Searched lean/WeilConjectures for the item id, its blueprint docstring tag, change-of-base-scheme language, and algebraic-space/base terminology. There is no declaration stating the item. The separate Sheaf algebraic-space infrastructure is not a finished WeilConjectures attachment.

## WANTED

None. All sources used are present locally.

## Statement clarification

STATEMENT-DISPUTED: the phrase “carries fibre products ... to fibre products over S'” does not name the middle object and admits a false reading as preservation of products over the terminal base. If S is two disjoint copies of Spec(k), S'=Spec(k), and X=Y=S, then X times_S Y has two points, whereas j_!X times_{S'} j_!Y has four points. The corrected clause explicitly says that for X -> Z <- Y the canonical map

j_!(X times_Z Y) -> j_!X times_{j_!Z} j_!Y

is an isomorphism. This is exactly the fibre-product preservation in Stacks 03I4 and 04BB; the middle space is also the one used throughout the proof. It preserves all the intended clauses and hypotheses. This is an ambiguity in the imported wording, not an error in the cited Stacks result. No target signature is edited.

## Existing material and searches

Read the chapter record and unit record, SETUP's three levels, GOAL.md, the worker brief and delivery-errors B through E in both concatenated versions. Read the current latest blueprint sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md (id det-thm-sf-ctf-stability-direct-images), particularly (3). The inherited deformation-theoretic via chain remains the item's provenance; this helper changes no unit or chapter route. Its current blueprint.from.node is null, and blueprint_refs.py ancestor prints None. I retain that maintainer-owned provenance instead of inventing an ancestor.

Searched the whole DAG for 03I4, 03I5, 04SG, 04KK and change-base/smaller-base terminology, and searched blueprint_refs.py for “change base scheme”, “smaller base”, and “03I4”. No existing node duplicates the full item. The smaller-base blueprint hits concern quasi-affine schemes in Nagata compactification, not base forgetting for algebraic spaces. Opened the statements of the localized-sheaf equivalence, sectionwise sheaf limits, algebraic-space definition, scheme-as-algebraic-space node, fibre-product node, etale-atlas presentation and etale-relation quotient. The latter presentation/quotient results are unnecessary: direct scheme tests prove the two algebraicity assertions without another quotient theorem. The generic sheaf localization equivalence is already lem-weil-pbc-localized-sheaves-over-representable, so no duplicate is created.

Ran the prescribed msearch command with LeanFinder twice, Loogle, LeanSearch and two Mathlib grep patterns; read the returned results. The actual queries and returned names were copied from the command's searches.jsonl into mathlib_searches. Scheme.CanonicallyOver and Scheme.Over concern schemes; smallEtaleTopology concerns a scheme's site. DenseSubsite.sheafEquiv and Equivalence.sheafCongr do not establish algebraicity after changing a big base. Over.iteratedSliceEquiv only identifies an iterated category slice. Read its source at Mathlib/CategoryTheory/Comma/Over/Basic.lean:382 and the Presieve/Sieve overEquiv declarations at Sites/Over.lean:60,95. Neither is an exact or one-line specialization proving the item. Mathlib/AlgebraicGeometry grep for AlgebraicSpace|algebraic.space|changeBaseScheme returned zero hits. All services answered these queries; none is recorded as unavailable or as a fabricated empty result. The two older grep records in the repository item are retained as inherited history, not represented as newly executed searches.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. The existing localization equivalence and sectionwise-limit statements are cited as tools instead of recreated.

## Review by Q04

I read spaces.tex, section-change-base-scheme: 03I4 (lemma-change-base-scheme), its proof, 03I5 (definition-base-change), 04SG (lemma-category-of-spaces-over-smaller-base-scheme), and 03I6 (lemma-viewed-as-properties). I read sites.tex 00Y1 (lemma-essential-image-j-shriek), 03HT (lemma-describe-j-shriek-good-site), 03HU (lemma-describe-j-shriek-representable), and 04BB (lemma-j-shriek-commutes-equalizers-fibre-products), including their proofs. I read the first paragraph of spaces-properties.tex 04KK (lemma-2-morphism), which explicitly identifies the small ringed sites after replacing the base by Spec(Z). No SGA source is used. The proof is marked agent-written: it elaborates the scheme-test argument directly rather than pretending that the source's quotient-presentation proof is copied verbatim.

Step 1 uses the actual statement of lem-weil-pbc-localized-sheaves-over-representable, which gives both the equivalence and the concrete inverse fibre sheaf; it is not a citation to a definition of localization in place of the equivalence. Its small-site hypothesis holds in the common larger universe because def-weil-size-convention supplies small skeletons. def-pc-fppf-site gives exactly the slice objects, morphisms and coverings needed for relocalization. def-trf-scheme-algebraic-space states that the actual representable h_S is a sheaf; this justifies gluing the structure maps, rather than assuming that a raw coproduct is a sheaf. Once those maps glue, the original sheaf condition glues the fibre sections. This supplies the missing no-sheafification check explicitly.

Step 2 uses lem-weil-pbc-site-sheaf-sets-limits-sectionwise, whose statement covers the finite diagram in question. The displayed mutually inverse pair formulas prove the sectionwise bijection and commute with restriction and projections, so no unrecorded preservation theorem is used. The representable formula is proved directly by the forced composite into S, rather than citing the slice-of-slice equivalence as though it proved algebraicity. This is elementary from the cited sectionwise-limit theorem.

Step 3 uses def-trf-algebraic-space for the representable diagonal and the scheme-test definition of etale/surjective maps, and def-pc-fibre-product for existence of scheme pullbacks. I checked the delicate case where the two sections on T induce DIFFERENT maps T -> S. The proof first treats two separate S-schemes A and B, then pulls A times_X B back along T -> T times_{S'} T. It does not assert that a map to j_!X times j_!X has a unique S-structure. This proves diagonal representability without S -> S' separated, and the atlas test has a SINGLE section, so its S-structure really is unique. That fibre scheme and its projection are literally the original atlas test, which proves both etaleness and surjectivity without a new locality lemma. This is marked non-elementary because it proves an algebraicity clause, although every construction is spelled out from the two cited definitions.

Step 4 uses def-trf-algebraic-space for the reverse diagonal/atlas criterion and def-trf-scheme-algebraic-space for the representable map to S. For G(T,phi), both sections have the SAME specified image phi. Therefore their equality locus really is the equality locus in F. Evaluating p on the identity of the atlas U produces the S-structure, and naturality proves that the whole morphism has that composite; no stronger Yoneda theorem is taken from a node that only states full faithfulness. On the atlas fibre product, equality in F implies equality of images under p, so no condition has been forgotten. The equivalence's unit and counit already exist by step 1; restricting those maps proves the equivalence of full algebraic subcategories. This is also marked non-elementary rather than hiding the converse algebraicity check under “transport”.

Step 5 uses the small-site and structure-sheaf clauses of def-trf-algebraic-space. The general test formula of step 3 proves the if and only if for etale scheme objects, in both directions. Composing an arbitrary V -> j_!X with h_S gives the required inverse scheme object. A triangle over j_!X also commutes over S, so its maps match; coverings and restrictions on regular functions are the same underlying scheme data. This is elementary from the calculations already proved, not an extra unproved invariance lemma.

Step 6 again uses the representable-etale scheme-test clause of def-trf-algebraic-space, not the assertion that every fibre product of algebraic spaces is a scheme. Here the etale leg V -> Y makes V times_Y X a scheme. Step 2 gives the same pullback, with both projections, after base forgetting. The formulas commute with an arrow in V, so the functor comparison is on objects AND morphisms, including the same maps on regular functions. There is no omitted compatibility argument.

For B1-B9 and C1-C5: there are no statement-only new nodes, no new notation needing an uncited definition, and no searches attributed to an unexecuted command. Every proof dependency occurs in a step, and every step's external non-elementary assertion is a cited statement. The citation quotes were checked as exact substrings of the opened live statements. Definitions are used for their explicit scheme tests, not as substitutes for an existence or descent theorem. The two generic sheaf-theoretic tools are declared in split_report.tool_uses; no off-unit statement is silently used. All steps are below 2000 characters, so none needs a hidden-sublemma extraction for length.

For D1-D5: nothing is moved into a new node, and no new node restates a clause. The proof writes the coproduct sheaf check, the pair formula, both diagonal tests, both atlas tests, the inverse sheaf, and the site/functor comparison. There is no appeal to the source's “clear” sentence without these details. It cites no descendant of the item. For E1-E7: tested identity base change, S'=Spec(Z), arbitrary nonseparated S, empty X and empty atlas, and the two-point-base example above. Empty matching families give the unique empty-scheme structure map and the unique sheaf section. No nonemptiness, finite type, quasi-separatedness, properness or base separation is introduced. The essential correction is making the fibre-product middle object explicit and taking separate S-structures before the diagonal test.

## Unfinished work

None within this stage-1 item. No Lean was written, no compiler or Lake was invoked, and nothing in the shared repository or launcher was edited. The required server dry run and direct delivery follow this report; their terminal outputs determine the final disposition.
