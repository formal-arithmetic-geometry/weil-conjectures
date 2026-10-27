# Q107: lem-sfb-koszul-split-conormal-cancellation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-koszul-split-conormal-cancellation.json`: statement, split into six steps; statement and statement dependencies unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-koszul-generators-from-fibre-basis.json`: new statement-only lemma, unsplit; no Mathlib match. Source: Stacks 067N(3), `divisors.tex`, `lemma-generate-regular-ideal`.
- `citations.json`: one verbatim statement quotation for each of the eleven step/node citation pairs.
- `report.md`: this report. The required search command recorded nine searches in `searches.jsonl`.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the item id, split conormal terminology, Koszul cancellation, and generator/basis terminology. There is no project declaration giving the item. `RegularLocalGeneratorsRegularSequence.lean` concerns regular systems of parameters in a regular local ring, a stronger hypothesis absent here. `KoszulConormalBasis.lean` gives a basis once the regular generators are already known; it is not the converse local generator-selection result. Generator-chain-map and homotopy declarations do not assert either lemma. No attachment is claimed from a sorry declaration.

## WANTED

None. Every mathematical source used is present in `literature/stacks-project/`.

## Corrections and scope

The item was unsplit, with no proof to preserve in the sandbox. Its statement is correct as an affine version of Stacks 068Z(3); no statement correction or dispute is needed. The source uses both Koszul-regularity assumptions, not ordinary regularity under an implicit Noetherian hypothesis. The proof's fibre injection is obtained from the actual retraction, not by asserting that tensoring with a residue field preserves injections.

The inherited `blueprint.from.node` is null. `tools/blueprint_refs.py ancestor` returns None: following `created.item` reaches `lem-sfb-admissible-direct-image`, created under a module name rather than a blueprint node. I retained the inherited chain, recorded the exact 068Z/067N supporting place, and prepended this item to the new node's via list. The existing blueprint ancestry text identifies `det-thm-sf-ctf-stability-direct-images`, proof (3); I read its current text, proof and unit under `literature/blueprint/latest/`, as well as the DAG chapter and unit. This is supporting algebra below the existing route, not a change to a unit or chapter.

Generic tool use: `lem-sc-koszul-regular-flat-base-change` is from the Picard unit. It is declared in `split_report.tool_uses` and is used only for the further localizations after the two applications of 067N. The prefix criterion is the existing `lem-sfb-koszul-prefix-quotient-criterion`, which states exactly the needed 068M direction; no second truncation node was created.

## Not duplicates

No existing node's source has Tag 067N. Whole-DAG tag and key-word searches and whole-blueprint searches for `067N`, `068M`, `Koszul`, `Koszul generators`, `minimal generators`, `regular ideal`, `fibre basis` and `conormal` found no existing generator-selection statement. The id was unused before creation.

lem-sfb-koszul-generators-from-fibre-basis vs lem-sc-koszul-conormal-basis: the existing lemma produces a conormal basis from a specified Koszul-regular sequence. The new lemma takes lifts of a basis at one prime and makes those specific lifts Koszul-regular generators on a principal neighbourhood. The converse change-of-generators argument is not a one-line specialization of the existing statement.

lem-sfb-koszul-generators-from-fibre-basis vs lem-sfb-koszul-prefix-quotient-criterion: the existing node descends the tail of a known regular concatenation through a known regular prefix; it does not choose either generating sequence. I cite it in step 5.

lem-sfb-koszul-generators-from-fibre-basis vs lem-sfb-koszul-closed-immersion-affine-criterion: the latter compares a geometric immersion property with the existence of some affine Koszul generators; it does not make prescribed lifts of a fibre basis into generators. The new lemma is a single-ideal input, not cancellation for nested ideals or a clause of this item.

## Review by Q107

I read the complete statement and proof of Stacks 068Z (`divisors.tex`, `lemma-permanence-regular-immersion`) and its actual assertion-(3) inputs: 067N (`lemma-generate-regular-ideal`) and 068M (`more-algebra.tex`, `lemma-truncate-koszul-regular`). I also read 063G (`lemma-regular-ideal-sheaf-scheme`) to check the affine/principal-open interpretation. The tag-to-label pairs 067N and 068M were checked in `tags/tags`. The new node is the single-ideal assertion 067N(3) on an affine scheme: a finite regular generating sequence has a free conormal module, a new fibre basis has the same length, its comparison matrix has determinant nonzero at the prime, and on a smaller neighbourhood this matrix is invertible. The source's change-of-basis argument then supplies the new Koszul generators. This determinant/change-of-basis result is the genuine lemma left as a statement-only node, not an elementary fact invented as a new node.

For step 1 I opened `def-weil-ring-localization-away` and `def-weil-pbc-localization-at-prime`. They give the fraction rings, local maximal ideal and residue field actually used. The inverse image of q contains J, h is outside that inverse image, and the stated hypothesis therefore supplies both finite regular generating lists in A. Prime extension and iterated localization are checked directly by their fraction maps; no finite generation of J away from this neighbourhood is assumed.

For step 2 I read the full statement of `def-weil-pbc-module-tensor-product`: it defines balanced tensors and their relations. Tensoring the retraction identity is verified on pure tensors. The forward and inverse maps to each localized residue module are written explicitly; J contained in p makes the product relations vanish. Thus the fibre inclusion really has a left inverse. No preservation-of-exactness lemma is being inferred from a definition or from right exactness. The exactness hypothesis is retained even though this calculation needs only its stronger specified retraction data.

For step 3 I read `lem-weil-pbc-vector-space-basis-through-vector`. Its statement extends every independent subset, not just a single vector; this is exactly what the image of the chosen I-fibre basis needs. Finiteness comes from finite spanning lists, and multiplying individual basis vectors by their nonzero denominator scalars retains their independence and span. This explains why the representatives f_i and g_j can be chosen in I and L themselves, rather than merely as germs.

For step 4 I read the new node's statement, `lem-weil-pbc-localization-flat`, and `lem-sc-koszul-regular-flat-base-change`. The new node requires one prime containing the ideal, an already existing finite Koszul generating sequence, and the proposed fibre basis. All are in force for both I and L. Each new localizer is outside the same prime. The flatness node explicitly covers arbitrary multiplicative sets, and the Koszul node explicitly covers a finite sequence under a flat algebra map without Noetherian or proper-ideal assumptions. Thus both sequences remain regular on the common principal open; localization also preserves their displayed generating equations.

For step 5 I opened `lem-sfb-koszul-prefix-quotient-criterion`. It explicitly assumes that the prefix is Koszul-regular and says concatenation is regular if and only if the quotient tail is regular. Both needed hypotheses have been obtained in step 4, over the same ring B. The quotient ideal is generated by the tail by writing out the original generating combination and discarding the prefix in the quotient. This does not claim arbitrary truncations of a Koszul-regular sequence are regular.

For step 6 I read `lem-weil-pbc-localization-quotient-commute` and `def-weil-pbc-koszul-complex`, besides the localization definition already used. The former explicitly identifies (R/K) localized at the image of v with R_v/KR_v, by its fraction formula. The latter gives finite exterior-power terms and the differential with sequence coefficients, so the coefficientwise ring-isomorphism maps and their inverses commute with differentials and identify homology. I spelled this out instead of hiding a transport assertion. Writing the two localizers as a/h^e and b/h^f yields v=hab outside p, so u is indeed outside q. Both sides use the same image ideal, and no conclusion only at the local ring is substituted for the required neighbourhood statement.

I checked small cases: K=0 recovers the assumed property of J; K=J gives the zero ideal in R/K and an empty tail; J=R or R/K=0 leaves no primes to test. For K=(x), J=(x,y) in k[x,y], the construction gives y modulo x. For K=(x^2), J=(x) in k[x], both ideals have regular generators but the conormal map is zero on its nonzero source; the missing splitting correctly prevents a false conclusion in k[x]/(x^2). For the new node, I=(x) in k[x,y], p=(x,y), and f=x(1+y) requires shrinking by 1+y as its statement allows. A redundant list (x,0) fails its fibre-basis hypothesis. Empty input sequences work, and a zero ring has no prime. Polynomial rings in infinitely many variables give non-Noetherian test examples without changing the argument.

The Mathlib searches were run only with the required command and recorded exactly from its JSON log, with successful LeanFinder, Loogle, grep and LeanSearch calls and a second phrasing. The source of the most plausible hits was read: RegularSequence.lean explicitly lists Koszul regularity as TODO; Regular/Flat.lean preserves ordinary weak regularity, not this homological notion; Smooth/Basic.lean's split injection is a formally-smooth criterion for a different cotangent map; Extension/Cotangent/Basis.lean constructs a presentation and does not establish Koszul regularity; Localization/Free.lean spreads a module basis, not ideal regularity. These are not matches or one-line specializations.

Against delivery-errors B--E, the new node is self-contained, introduces every object, has definition dependencies, has no proof steps or proof dependencies, and has only the tag actually read for it. Every step's cited node statement was opened and is quoted verbatim in `citations.json`; the steps use their statements, not hidden arguments in their proofs. There is no cancellation clause moved into a child node, no circular induction, and no unmentioned Noetherian, regular-local-ring or flat-residue-field hypothesis. All six steps are shorter than 2000 characters. Only the Q107 sandbox was written; no Lean files, compilation, Git command in the shared repository, or launcher edits were used.

## Outstanding work

No mathematical part of this one-level split is unfinished. The new node is intentionally unsplit for a subsequent stage-1 worker. Server dry run and delivery results follow below.

## Server validation

The required `deliver.py Q107 lem-sfb-koszul-split-conormal-cancellation --no-push` invocation exited 0 and printed `OK (not pushed)` at `30aa2d0ad48`: server preflight passed. No check failures required repair. This is the completed one-level split with one new unsplit statement and zero new Mathlib leaves.
