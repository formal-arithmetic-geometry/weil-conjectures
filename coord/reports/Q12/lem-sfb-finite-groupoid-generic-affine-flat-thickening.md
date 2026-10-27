# Stage-1 delivery: lem-sfb-finite-groupoid-generic-affine-flat-thickening

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-groupoid-generic-affine-flat-thickening.json: unchanged statement, nine proof steps, status split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-presented-groupoid-rank-filtration.json: statement-only lemma, unsplit; no Mathlib match. It supplies finitely presented invariant rank strata, not the affine neighbourhood in the item.
- dag/nodes/sec-six-functors-basics/lem-sfb-generic-point-fp-closed-interior.json: statement-only lemma, unsplit; no Mathlib match. It supplies an underlying-set neighbourhood inside a finitely presented closed subscheme at a component generic point.
- citations.json: one verbatim statement quotation for each use in every item step.

## Attachments

None. I searched the item tag and invariant-affine, scheme-groupoid, generic-thickening and rank-filtration concepts in lean/WeilConjectures. InvariantAffineNeighbourhoods.lean proves a finite locally free descent-datum result, with an affine-orbit hypothesis, not this finite, possibly nonflat groupoid and thickening assertion. The constructible-generic-point theorem in WeilConjectures/Mathlib/Topology/Constructible.lean:195 assumes a Noetherian space; the new generic-interior node deliberately makes no Noetherian assumption. Neither is an exact attachment. No Lean was written or compiled.

## WANTED

None. All mathematical sources used are available in literature/stacks-project.

## What needed repair or clarification

The imported statement agrees with Tag 0ABC and is unchanged. The existing almost-dense-flat-locus node states neither finite presentation of its thickening nor containment of generic orbits; those are properties of the construction in its proof, not properties available from its statement. I therefore do not cite that node for those properties. Instead I build a finite disjoint union of invariant open interiors of the finite-presentation rank strata. This is the same rank-stratum mechanism underlying 0ABB, with no reliance on undocumented output of 0ABA.

The existing locally-free-groupoid-invariant-affine node states the one-orbit result only. A union of affine opens need not be affine. I wrote out the norm shrinking with a single prime-avoidance element nonzero on the whole finite union of orbits, using the existing general norm-locus-affineness statement. This is the construction in 03JE, with its finite set enlarged; it does not create a node restating the affine conclusion.

The printed proof of 0ABB says a piece W_r meeting the rank-(k+1) neighbourhood has r=k, while its final displayed piece is W_(k+1); the consistent index is r=k+1. The direct interior construction avoids relying on this indexing slip. It also avoids the need to extract individual W_r from an existence theorem's proof.

The item's existing blueprint ancestor is null, as confirmed by tools/blueprint_refs.py ancestor; I preserve that value and the full recorded alteration-chain place and via list. The newest blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/, including the current direct-images proof. No chapter/unit record is changed; this is a supporting prerequisite far below the recorded alteration route.

## Not duplicates

lem-sfb-finite-presented-groupoid-rank-filtration vs lem-sfb-finite-groupoid-invariant-rank-filtration: the existing 0AB9 statement assumes only finiteness and asserts no finite presentation of Z_n; the new statement assumes finite presentation of s,t and asserts finite presentation of every Z_n. That added conclusion is essential to the generic-interior lemma and the finitely presented thickening, and cannot be obtained by specializing the old statement. The new lemma is the 0ABB refinement of the existing filtration, not a clause of the item's affine-neighbourhood conclusion.

The existing coherent-universal-rank-locus node assumes a Noetherian base and concerns a coherent module; it does not provide this arbitrary-base invariant groupoid filtration. The generic-interior search found no existing DAG or blueprint statement covering a finitely presented closed immersion into an arbitrary scheme at a component generic point. No new affine-cover, finite-set prime-avoidance, thickening-affineness or finite-product lemma was created.

## Review by Q12

I read More on Groupoids Tag 0ABC (more-groupoids.tex:2582–2616) and the full 0ABB addendum (2535–2578), plus the 0AB9 rank-stratification proof and 0ABA construction. For the new rank-filtration node I read Divisors Tag 05P8 (divisors.tex:1384–1421), especially its final finite-presentation assertion, and 0ABB's first paragraph which applies it to the invariant filtration of a finite finitely presented groupoid. For the new generic-interior node I read Properties Tag 0AAW (properties.tex:59–80), Chevalley Tag 054K (morphisms.tex:4397–4404), and Algebra Tag 00EV (algebra.tex:4739–4757). The last gives the affine explanation: a finitely generated ideal contained in a minimal prime is nilpotent after localization there, and finitely many denominators yield a basic open contained in its vanishing locus. This is a support assertion, never a scheme-theoretic factorization assertion. New nodes carry statements only; their later proofs remain queued.

Step 1 uses exactly the new finite-presentation rank filtration and the finite-fibres clause of finite-closed-map-finite-fibres. Membership in an invariant closed stratum is constant along an arrow. Empty input uses Spec(0); positive input makes the finite set F nonempty. The filtration's empty intersection supplies a rank for every point, with no global finite rank bound or quasi-compactness assumption.

Step 2 uses the new generic-interior statement on Z_(r-1), not a Noetherian generic-flatness theorem. Intersecting its neighbourhood with the open complement of Z_r gives interior in D_r. The closed-map clause of finite-closed-map-finite-fibres makes H(E) open; subset-saturation-invariant proves its invariance, and inversion and the identity in def-a1-groupoid-scheme prove H(E) consists of points whose whole orbit is in E. This proves the selected orbits survive shrinking. All three cited statements were opened and their actual conclusions checked.

Step 3 uses the quotient-ideal description of closed immersion and the fibre-product definition to glue the finitely many disjoint thickened pieces. The closed-immersion-finite-presentation-ideal criterion is applied twice: the given finite presentation of Z_n supplies local finite generation, then its restrictions supply finite presentation of W′ into W. Equality of source/target inverse images of the two factors gives scheme-theoretic invariance, not merely invariance of support.

Step 4 uses the finite locally free maps on the rank strata from the new filtration. Equal inverse-image subschemes plus uniqueness of lifts through the closed monomorphism identify the double restriction with a single pullback. Finite-morphism-permanence gives global finiteness. Flatness and local finite presentation on the disjoint open pieces are literally the same stalk maps and local presentations, as the two definition nodes specify. Inversion swaps source/target. I added the local nil-ideal argument showing Q→R_W is a homeomorphism; this checks that no arrows disappear from the point orbits upon replacing W by its thickening.

Step 5 checks quasi-separatedness rather than assuming it for an arbitrary subscheme. Pullbacks of affine opens of U lying in W are affine by the closed-immersion quotient-ring description; their intersections are closed pullbacks of quasi-compact intersections in U, using pqf-lem-qs-intersection-qc. The affine-cover criterion gives quasi-separatedness of X. Its points in F are component generic points because the ambient restriction was open and the thickening is a homeomorphism. The existing generic-point affine-neighbourhood theorem supplies a common affine A. I checked that it permits an arbitrary point plus finitely many distinct component generic points; choose that point in F, deduplicating F, so its hypotheses hold.

Step 6 repeats the already proved H(E) construction on the now finite locally free restricted groupoid. Basic-open basis plus prime avoidance produces a single f nonzero at all points of F with D(f)⊂B; the text proves the latter containment from ideal membership, rather than asserting it. The prime-avoidance node allows any finite nonempty family of prime ideals, including repeated or comparable ones, so no additional incomparability lemma is used.

Step 7 checks every hypothesis of descent-norm-locus-affine: its object scheme is X, its affine A is ours, its W is B, and its U is V′=H(D(f)). Invariance of B gives a^(-1)(B)⊂b^(-1)(A). Inversion supplies the exact complement-image formula stated by the norm lemma. The lemma makes V′ affine without assuming B affine, constant rank globally, or affineness of a union. I opened the statement and quoted it in full in citations.json.

Step 8 uses open-immersion and closed-immersion definitions for the corresponding open V across a homeomorphic thickening. Local finite generation of the restricted ideal gives finite presentation by the same criterion; closed-affine-union-affine with one member gives affineness of V. I explicitly checked that invariance passes first on points using Q→R_W and then on schemes by equality of closed pullbacks on the common inverse-image open. It does not infer scheme-theoretic containment from set-theoretic containment.

Step 9 checks the exact double-fibre-product arrow formula in the item. The finite, flat, locally finitely presented source on X restricts to the invariant open V′, hence remains finite locally free; inversion handles the target. The finite-morphism-permanence node supplies finiteness under the needed base change, while the two local definitions handle open restriction. No unjustified tensor exactness, arbitrary-base generic flatness, or general nonflat base-change assertion occurs.

Small cases checked: m=0; empty U (only the m=0 case); the identity groupoid, where only the rank-one piece matters; repeated u_j and repeated orbits; several distinct generic components; nilpotent nonreduced object schemes; non-Noetherian schemes and unbounded ranks on different components. The construction uses only the finitely many ranks meeting the selected points, so no finite global stratification is claimed. The generic-interior lemma specifically requires finite presentation: dropping it would fail for arbitrary infinitely generated ideals at a minimal prime. The new rank lemma imposes finite presentation where the old one does not. All steps are shorter than 2000 characters and none hides a separately invoked comparison or standard lemma; the non-elementary rank, generic-interior, affine-neighbourhood and norm inputs are cited nodes.

I checked B–E of delivery-errors: self-contained statements and definition dependencies; Stacks tags and exact local source labels; logged Mathlib searches in two semantic phrasings plus Loogle and source grep; no proof in a new unsplit node; no clause relabelling; every non-elementary input is cited; every citation has a verbatim quote; no citation of another node's proof; no new cyclic dependency or route substitution. Server review_split and check_dag both passed before the report was written. Generic off-unit tools are declared in split_report.tool_uses for maintainer review. No SGA source is used.

## Unfinished work

None for this stage-1 split. The two new unsplit supporting lemmas are intentional queue items, not unfinished portions of the item proof.
