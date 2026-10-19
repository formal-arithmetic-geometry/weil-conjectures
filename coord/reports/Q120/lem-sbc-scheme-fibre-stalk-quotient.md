# lem-sbc-scheme-fibre-stalk-quotient — Q120

## Files written

- dag/nodes/sec-smooth-base-change/lem-sbc-scheme-fibre-stalk-quotient.json: statement, split into five steps; Mathlib verdict: no declaration found proving the full canonical stalk-kernel formula.
- citations.json: one verbatim statement quotation for every node citation of every proof step.
- searches.jsonl: actual msearch.py records, read before recording the verdicts.
- report.md: this report.

## New nodes

None. No new Mathlib leaves. All the ingredients already have DAG nodes.

## Attachments

None. Searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag and for fibre/stalk, fiberι, stalkMap and kernel/quotient terms. The project uses fibre stalks and the surjectivity interface but has no declaration giving every clause here. Upstream master was read only as reference material; its declarations were not treated as completed proofs.

## WANTED

None. All used Stacks sources are present locally.

## Corrections and omissions in the imported material

The statement is correct, so it is unchanged. The item was created by the maintainer's Q32 review to extract a hidden general lemma from a long step of lem-sbc-composite-fibre-local-models. This delivery does not move that content into another new node: its affine reduction and map/ideal identifications are written out, and its algebraic ingredient is the existing lem-weil-pbc-fibre-ring-local-ring-natural-iso. Unlike the abstract ring-isomorphism variant, that node explicitly proves surjectivity, the kernel and the fraction formula, so it supports the canonical map clause.

The old imported Mathlib search records included services not run by the maintainer reader because network access was blocked. I replaced those inconclusive records with actual msearch.py searches in this sandbox; LeanFinder, Loogle, LeanSearch and grep all ran. I read the hits and tried a second semantic phrasing. Residue-field definitions, spectrum-of-stalk maps, ideal-sheaf kernel statements and fibre definitions do not prove this formula. Fiber.lean:99 gives IsPreimmersion of fiberι and SurjectiveOnStalks.lean:38 gives surjectivity, but neither computes the required kernel. The report does not claim a Mathlib leaf on that partial evidence.

## Tool use

lem-weil-pbc-fibre-ring-local-ring-natural-iso is a generic commutative-algebra tool outside the vanishing unit, declared in split_report.tool_uses. Stacks Schemes 0HA1 explicitly reduces to Algebra 0H9M; this is not a replacement of a unit step. All other cited statement nodes are Mathlib leaves (or definitions). No target, coefficient convention or base-change transformation is changed.

## Blueprint and duplicate search

Read the chapter sec-smooth-base-change, the unit sk-thm-vanishing and the current main-20261015 universal-test-vanishing proof. The item remains below the relative-dimension permanence argument in that proof's slicing paragraph, with the existing ancestry intact. tools/blueprint_refs.py ancestor confirms sbc-thm-universal-test-vanishing. Searched the full blueprint for 'fibre local', 'fibre ring', 'local ring fibre', '0HA1', '0H9M', 'local ring' and 'stalk'; none states this same scheme-level canonical quotient. Searched the whole DAG for 0HA1/0H9M and the local-ring/fibre/localization terminology. The ring-level local-ring-natural-iso is reused rather than duplicated. The isomorphism-only ring node omits the canonical map and is not used in its place. No nodes are created, so there are no new-node duplicate pairs.

## Review by Q120

I read the whole of delivery-errors B–E and checked each issue against this split and the local sources. For the item I read Schemes Tag 0HA1 (lemma-local-ring-fibre) and its proof, and Algebra Tag 0H9M (remark-local-ring-fibre), which give exactly the affine reduction used. I also read Schemes 01IJ/01HV, 01HY/01I1, 01I4/01JQ and 01JR at their labels and checked the tag-to-label mapping. There is no new node needing a source review. No SGA source is cited.

Step 1 uses the local affine definition and the spectrum convention to choose V around t and U inside g^{-1}(V). I opened lem-weil-pbc-affine-open-stalk-localization: clause (c) says the germ map is the localization, and clause (b) makes the identifications compatible with the original stalk. Choosing U in the open subscheme does not assume g affine, or that an inverse image of an affine is affine. This is a direct use of scheme local affineness, followed by the cited stalk identifications.

Step 2 uses the actual statement of lem-weil-pbc-spec-residue-field-identification, which identifies both the residue field and the morphism from its spectrum, not just an abstract field isomorphism. The quotient of the step-1 local-ring isomorphism identifies the original kappa(t) with this affine residue field. The statement of lem-weil-pbc-open-fibre-product supplies the open subscheme p^{-1}(U) with projection compatibility. Its hypotheses hold because g(U) is contained in V and the residue-field spectrum maps to t in V. The statement of lem-weil-pbc-fibre-product-affine-spectra supplies the tensor ring AND the projection b maps to b tensor 1. The homeomorphism clause in def-pc-scheme-fibre supplies existence and uniqueness of y'. This step does not cite only a definition of fibre products for an affine tensor-product theorem.

Step 3 uses the complete fraction description in affine-open-stalk-localization, the germ and composition clauses of lem-weil-pbc-scheme-stalk-map-composition, and locality in def-weil-locally-ringed-space-morphism. These statements were opened and read. The fraction formula is written explicitly by applying the germ formula to numerators and mapping inverses of denominator germs. Locality and preservation of units prove both contractions of point primes. Thus the actual projection stalk map, rather than an arbitrary map under an abstract isomorphism, is the theta used next.

Step 4 quotes lem-weil-pbc-fibre-ring-local-ring-natural-iso. I checked all of its hypotheses: A and B are arbitrary commutative rings, p and Q are primes, C is exactly B tensor_A kappa(p), and q is exactly the contraction of Q. Its statement gives surjectivity, the precise ideal p B_q and the isomorphism on fraction classes. It needs no finite type, flatness or Noetherian hypothesis. Its proof dependencies do not pass through this item; this is the strictly algebraic ingredient already split in the DAG.

Step 5 uses the maximal-ideal description in def-weil-pbc-localization-at-prime. The equality of extended ideals is proved by both containments: a/u from p A_p maps to a multiple of phi(a), and each phi(a) is the image of a/1. Denominators are invertible because their contractions avoid p, as checked in step 3. Every germ is a fraction by step 1, so the resulting quotient isomorphism sends every class to its actual image under p-sharp. No unproved naturality or transport assertion is used for that final clause.

I checked small cases explicitly. For g=id_T the fibre is Spec kappa(t); the map is the residue quotient with kernel m_t. For g:Spec Z[x] to Spec Z at the point (p,x), the stalk is Z[x]_(p,x), and quotient by p gives F_p[x]_(x), not the residue field at y; this distinguishes the fibre local ring from a point residue field. At a point over the generic point of Spec Z, m_t=0 and the projection stalk map is an isomorphism (all nonzero integers are already inverted in the source stalk). For a nonreduced base k[epsilon]/(epsilon^2), g=id and its unique point gives quotient k with kernel (epsilon), so reducedness was not smuggled in. Empty schemes cause no exception since the statement assumes y exists. None of these cases requires y or t closed.

For the B–E checklist: no new statement or definition is introduced, all notions in the statement retain their existing definition dependencies, mathematical text uses single TeX escapes in the decoded JSON, sources use checked Stacks tags and labels, searches were actually executed and read, and the item carries its filled blueprint provenance. Every non-elementary fact used is a cited statement, with verbatim evidence in citations.json; elementary steps only choose neighbourhoods or compute images of fractions and generators. There is no new clause-restating node, hidden comparison, circular induction or weakened statement. No non-elementary step is longer than 2000 characters (the longest is 1046); I also reviewed the shorter steps for hidden lemmas. The five-step proof leaves no unproved mathematical step in this item; existing dependencies remain their own work items. The required server checks and delivery result follow below.

## Unfinished work

None in this item's split. No Lean was written or compiled, no build tools ran, and no shared repository or launcher file was edited.

## Validation

The required deliver.py --no-push exited successfully: `OK (not pushed) deliver/Q120/lem-sbc-scheme-fibre-stalk-quotient at f4b717d9fb: preflight passed`. This ran the server preflight including the DAG and split checks. No diagnostics required a repair.
