# Q17 stage-1 report

## Files written

- `dag/nodes/sec-nagata-compactification/lemma-nagata-relative-proj-invertible-tensor-powers.json`: existing statement item, split in four steps, not a Mathlib leaf.
- `citations.json`: eight verbatim statement quotations, one for every step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `prepare.py` is the item-local preparation script.

New nodes: 0. New Mathlib leaves: 0. No unit record was changed: this item is not the key statement of the blow-up unit.

## Attachments

None proposed. The task specifically forbids repeating the previously rejected ATTACH disposition. I searched the supplied project Lean by the full item id, the claimed declaration and the invertible-Rees notion. In the currently supplied read clone, `WeilConjectures/Blowup/FlatBaseChange.lean` now exists and lines 172--184 contain `AlgebraicGeometry.Scheme.IdealSheafData.isIso_relProjHom_reesData_of_isInvertible`, whose proof uses the invertible blow-up map and the comparison isomorphism. Its conclusion matches the NEW blueprint statement, not the old additional O(1)/degree-one-map clauses. I leave the inherited Lean audit unchanged and deliver the requested stage-1 split, without making a new attachment claim. The affine node is already attached in the shared DAG; it is reused, not edited.

## WANTED

None. All documents used were available under literature/. No source was downloaded.

## Statement and proof corrections

The item has an explicit `blueprint_update` from main-20261023, commit c9b5f3ad18a6654dbbee6f7d7b4b4af85e01463f. I read the CURRENT statement and companion `.proof.md` in `literature/blueprint/latest/blueprint/sec-nagata-compactification/sk-lem-nagata-sketch-blowups/`. As that update directs, the delivered statement is its exact new statement: the specified structure morphism from relative Proj of the Rees algebra is an isomorphism. The old imported statement instead used tensor powers and added O(1) and universal-degree-one-map conclusions. This is an explicitly reported synchronization with the mandated source, not a claim that those old conclusions are false; there is no STATEMENT-DISPUTED mathematical assertion to correct here.

The imported proof did not cite the relative-Proj restriction result in its uses list, despite listing it in proof_deps. It also treated gluing as automatic without citing a morphism-gluing statement. I repaired both, and proof_deps is now exactly the union of the eight actual uses.

The existing affine node's live statement still uses the tensor algebra. Its `blueprint_update` states the Rees version, but a citation must use its actual statement. Accordingly step 2 explicitly constructs the multiplication equivalence from the affine tensor algebra to the affine sections of the Rees algebra. Step 3 cites graded-equivalence invariance of Proj before applying that unchanged affine statement. No conclusion is borrowed merely from another node's proof or update field.

## Searches and reuse

I searched the whole DAG and imported blueprint with `tools/blueprint_refs.py search` for the item title and for "invertible ideal on", and searched Lean and DAG source by the relevant names and concepts. I read the matching affine, Rees, invertible-ideal, relative-Proj, affine-module comparison and morphism-gluing statements. The blow-up Cartier-isomorphism corollary is the equivalent blow-up formulation, recorded in same_as. I do not cite it to prove this item: it is downstream material, and doing so would replace the required local affine proof. No new lemma was needed.

Six searches were run through the required msearch.py command and preserved in searches.jsonl: two LeanFinder phrasings, two Loogle queries, one Mathlib grep and one LeanSearch query. Both semantic phrasings returned ordinary Proj standard-chart results or unrelated subscheme/normalization results. LeanSearch returned ideal-sheaf operations and a cover-gluing isomorphism; none states the relative Rees assertion. The first Loogle query used the unrecognized identifier Ideal.IsInvertible; its precise error is recorded, and the corrected AlgebraicGeometry.Proj query succeeded. The Mathlib grep found no relative invertible-Rees isomorphism. All six queries are recorded verbatim in mathlib_searches; no unavailable service was described as an empty mathematical result.

I read `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean` lines 150--169 and `ProjectiveSpectrum/Scheme.lean` lines 829--837: `Proj.basicOpenIsoSpec` and `ProjectiveSpectrum.Proj.isIso_toSpec` identify a single standard open with its homogeneous-localization spectrum. They do not assert this relative invertible-Rees statement. I also read the existing gluing leaf's declarations in `Mathlib/AlgebraicGeometry/Gluing.lean`, around lines 448--478. No compiler or Lake command was run.

## Not duplicates

No new nodes. Existing affine calculation, affine tilde/sections adjunction, relative-Proj functoriality, relative-Proj existence, affine-open basis and scheme-morphism gluing are cited directly. The local inverse gluing and the rank-one basis computation remain steps, since their arguments take only the displayed elementary computations and these cited statements.

## Review by Q17

I read the worker brief, the stage-1 rules, the chapter and blow-up unit records, the three blueprint levels in SETUP.md, GOAL.md, and delivery-errors.md B--E in full. The route remains the unit's Rees/Proj affine-chart route. I read the current item's statement and complete proof, and the current affine statement/proof from the latest blueprint. There are no new nodes with additional sources to audit. I additionally read Stacks constructions.tex Tag 01NQ, label lemma-glue-relative-proj, for the structural affine restriction; schemes.tex Tags 01IT (lemma-basis-affine-opens), 01IB/01ID (lemma-equivalence-quasi-coherent/lemma-colimit-quasi-coherent), and 01JB (lemma-glue) for the explicit supporting operations. I checked constructions.tex Tag 01N0, lemma-surjective-graded-rings-map-proj, and its functorial context for the existing graded-equivalence tool. Stacks 0807, divisors.tex lemma-blow-up-effective-Cartier-divisor, corroborates the final assertion but its universal-property proof is not substituted for this unit's affine route. No SGA source is used.

Step 1 uses exactly the invertible-ideal definition (locally free rank one WITH its ideal inclusion) and the affine-open-basis statement. The basis theorem applies inside each trivializing open. Injectivity is proved rather than assumed: multiplication by the basis section factors through the isomorphism onto the ideal and its actual inclusion. Iteration gives injectivity for every power. No reducedness, domain, Noetherian, finite-type, quasi-compactness or separatedness hypothesis is introduced.

Step 2 uses the statement of the sheaf Rees definition, which explicitly supplies the graded algebra, its multiplication, and quasi-coherence, and the affine tilde/sections adjunction. I checked that the latter's statement supplies an isomorphic unit and counit and preservation of all small colimits, not merely an unproved slogan about sections. Applying it to the N-indexed coproduct on an AFFINE V_i gives precisely the finite-sum affine graded ring. Each power subsheaf has the displayed generator a_i^n; injectivity was proved in step 1. Multiplication from tensor powers is therefore bijective on every homogeneous piece, and its product/unit compatibility is written on basis multiples, including n=0. This is an explicit short computation, not a new unsplit restatement of the main lemma.

Step 3 uses relative-Proj existence for restriction OVER V_i, clause 2 of relative-Proj functoriality for the degree-preserving algebra equivalence over the identical degree-zero base, and the affine tensor-powers node for the Proj of T_i being canonically V_i OVER V_i. I opened all three node statements. The affine node really includes the over-base assertion, so the conclusion concerns the specified structure morphism rather than an unspecified abstract isomorphism. The graded equivalence meets the base-identity hypothesis by its n=0 formula. The tensor-versus-Rees discrepancy in the live affine statement is handled by step 2, not ignored.

Step 4 uses the scheme-morphism-gluing leaf, whose actual statement gives existence AND uniqueness for morphisms agreeing on all intersections. The local inverse maps land in the required inverse-image opens because their composites with pi are inclusions. On each overlap they are both inverses to the same restricted structure map; the written equation s=s(pi t)=(s pi)t=t verifies agreement. Gluing gives one global inverse, and the same leaf's uniqueness checks both composite identities on the respective covers. Intersections need not be affine; no hidden finiteness assumption enters.

I tested the empty scheme/empty cover (the gluing leaf still yields the unique inverse), the unit ideal (ordinary A[T] on every chart), nonreduced rings with a regular generator (e.g. A=k[epsilon]/(epsilon^2), a=1), and non-domain rings admitting regular nonunit generators (e.g. A=k[x] times k[x], a=(x,x)). The zero ideal on a nonempty scheme and a zero-divisor-generated ideal such as (epsilon) are not invertible rank-one ideal subsheaves, so the proof never applies to them. All powers retain injectivity even in nonreduced rings. There is no global generator assumption. Every step is shorter than 2000 characters. Every non-elementary ingredient is a cited existing statement. I checked the candidate proof dependencies transitively for a return path to the item: none. Eight citations were checked verbatim against current statements before writing citations.json.

Two generic off-unit tools are declared in split_report.tool_uses: affine tilde/sections comparison and clause 2 of graded-Proj functoriality. Neither replaces the local affine route. The other off-unit citations are existing Mathlib leaves or the already closed relative-Proj existence interface. No top-level tool_uses field was changed.

## Unfinished work

No requested mathematical work remains. The required server dry run and direct delivery follow this report. Independent maintainer review remains the project's normal review step.
