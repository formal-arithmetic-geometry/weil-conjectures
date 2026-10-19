# Q14 stage-1 report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-topos-localization-site-presentation.json`: item, statement, split into six steps; no exact Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-sieve-sheaves-covering-site.json`: new statement-only unsplit supporting lemma, no exact Mathlib match. This bridges the sieve-topology definition of a Grothendieck topos to the covering-family-site hypothesis of the existing comparison lemmas.
- `citations.json`: one verbatim statement excerpt for each of the 14 proof-step citations.

The new node has no proof or proof dependencies. The only mathematical construction split here is the assigned item. No unit realization edit is needed: the item is an auxiliary descendant, not the unit's key node. One new node; zero Mathlib leaves.

## Attachments

None. Searched the project under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint id and for topos localization, subcanonical presentations and site-comparison terminology. No declaration supplies the item or the new bridge. Upstream master was not used as evidence of a proof.

## WANTED

None. All source material used is available in `literature/stacks-project/sites.tex` and its tag map.

## Problems found and corrected

The imported item is mathematically correct and its statement is unchanged. Its initial lack of a proof hid a scope issue: `def-weil-pbc-topos` was updated to define sheaves for arbitrary covering-sieve topologies on a small category, with no categorical pullbacks. In contrast, `def-weil-pbc-sites-and-cohomology` and the existing 03A1 comparison node use covering families whose pullbacks exist. One cannot apply that comparison to the arbitrary initial category without an intervening theorem. The new unsplit bridge records exactly this intervening result. It does not assert subcanonicity, finite limits, representability of a prescribed object, a slice equivalence, or the inverse-image formula; the item's steps carry those arguments.

The bridge's source is explicitly identified as an agent generalization of the good-site/comparison construction to a sieve topology. Stacks 03CI and 03A1 are not claimed to state it literally with that starting convention. The expected argument for its eventual split is to take a small full category of sheaves containing the associated representables and closed under finite limits, equip it with epimorphic covering families, and prove restricted-Yoneda comparison using matching families on covering sieves. Sieve sheafification is available in 00ZM. This argument is explanatory material in this report, not a proof smuggled into the new node's statement.

The argument does not need 03CI's stronger closure under all subsheaves; finite-limit closure suffices for the item. The equivalence-on-slices and inverse-image identification are written explicitly rather than invoking undefined transport. Corrected the localization-adjunction source tag to 00XR after checking the tag map.

## Searches and blueprint route

Read the chapter `sec-trace-formula`, unit `sk-i-curve-zero`, the current ancestor node `lem-trf-local-term-locality` including its `blueprint_update`, and the item's ancestry. This is generic site-localization input beneath the normal-cone specialization branch, with no change to the curve-zero unit's route. Searched the entire imported blueprint using `blueprint_refs.py` for `topos`, `subcategory`, `localization`, `03A1`, `sieve`, `03CI`, and `covering-family`, and searched the whole DAG for the source tags and the site/slice/generator notions. No blueprint node states the bridge or the item in another form, so `same_as` is empty.

All Mathlib searches were run through the prescribed `msearch.py`; `searches.jsonl` contains their actual answers. The bridge has LeanFinder (two phrasings), Loogle, grep and LeanSearch records. Read `Mathlib/CategoryTheory/Sites/Pretopology.lean:45,139-168`: `GrothendieckTopology.toPretopology` assumes `HasPullbacks C` and therefore does not prove the bridge for arbitrary C. Read `Sites/DenseSubsite/SheafEquiv.lean:10-42`: the comparison assumes a dense-subsite functor and two already supplied topologies; constructing these for a full category of sheaves is not a one-line specialization. The initial item search found subcanonical topologies, Yoneda, and sheafification on already essentially small sites, not the chosen-object presentation. One exploratory Loogle query used unqualified identifiers and returned an unknown-identifier message; it was not treated as evidence of absence, and the fully qualified query was also run.

## Not duplicates

lem-trf-sieve-sheaves-covering-site vs lem-trf-topos-localization-site-presentation: the new bridge only changes an arbitrary sieve-site presentation to a covering-family-site presentation; it contains none of the chosen-object, subcanonical, finite-limit, slice or inverse-image conclusions.

lem-trf-sieve-sheaves-covering-site vs lem-weil-pbc-topos-compatible-generators: the existing statement starts with covering-family sites and a left-exact functor and constructs compatible generator categories; it does not remove the pullback-existence requirement on the initial sieve category.

lem-trf-sieve-sheaves-covering-site vs lem-weil-pbc-site-of-sheaf-generators: the existing statement assumes a precoverage with the isomorphism, composition and base-change axioms and pullbacks, and an already given fully faithful finite-limit-preserving generator functor; the bridge starts with an arbitrary sieve topology and provides an ordinary site presentation.

lem-trf-sieve-sheaves-covering-site vs lem-weil-pbc-sheaf-subcategory-comparison: the existing statement assumes a site in the covering-family sense of its cited definition and an already given small pullback-closed subcategory of its sheaves. The bridge makes the initial covering-family-site hypothesis available from an arbitrary sieve site; this scope difference is why the existing comparison cannot simply be cited in step 1.

## Review by Q14

I read the complete proofs of Stacks 03CI (`lemma-topos-good-site`) and 03A1 (`lemma-special-equivalence`), 04GZ (`lemma-localize-topos`) and the fibre construction in 00Y1 (`lemma-essential-image-j-shriek`), the localization and continuous/cocontinuous descriptions in 00XZ and 00XR, and sieve sheafification 00ZM for the new bridge. The new node has a statement only and its source explicitly labels the generalization; no source is silently attributed a stronger hypothesis range than it has.

For step 1 I opened the current topos definition: it supplies precisely a V-small sieve category, its topology and the equivalence. The new bridge states an equivalence with a V-small covering-family site, so the step takes exactly its statement and makes no assumption that the original category has pullbacks. The image B of A is introduced here.

For step 2 I read the statement of the existing sectionwise-limits node: it gives the terminal sheaf and all the particular pullbacks used, since the new starting site S is now a covering-family site. Sheafification of representables is the object defined in the cited sheafification node. The smallness argument is written as a subset of a product of small sets; V is closed under those products and countable unions. All cospans, not merely cospans with a particular target, are added, and old objects are retained. Each finite diagram occurs at a finite stage. The explicit product and diagonal constructions then give finite limits without invoking another closure theorem. This is an elementary construction from the cited limit-existence statement, not a new mathematical lemma.

For step 3 I opened the entire statement of the subcategory-comparison node and checked all three hypotheses against step 2. Its statement gives the small subcanonical site, the Hom formula for N, the equivalence, and representability of N(B). Those properties are not borrowed from its proof. For the geometric terminology the cited definition asks only for an adjunction and finite-limit preservation; the equivalence's unit/counit and universal properties supply them.

For step 4 I opened the localized-sheaves-over-representable statement, which explicitly gives the equivalence, its fibre quasi-inverse and its natural unit/counit, without assuming subcanonicity. Here subcanonicity has actually been proved, so identifying h_U with its associated sheaf is justified by the universal property. The localization definition explicitly gives the stated covering families. The slice equivalence induced by e is described on arrows and its inverse follows from the same unit/counit; it is not an unproved comparison theorem.

For step 5 I checked the entire continuous/cocontinuous-adjunction statement. It does give restriction as a geometric inverse image, including its right adjoint, under exactly those two functor hypotheses. The proof verifies both for the forgetful slice functor: underlying covers and their pullbacks give continuity, and every cover of V lifts over the specified V-to-U map for cocontinuity. Composition of geometric morphisms is stated in the cited geometric-morphism definition.

For step 6 the sectionwise-limits statement supplies the product calculation, and the localized-sheaves statement supplies precisely the fibre formula used. The bijection is displayed with its inverse, its compatibility with restriction is checked, and it is natural in H. Thus no fact about an unproved slice-comparison construction is being used. The transported inverse image is actually the product-over-A functor in the conclusion.

I checked B through E of the delivery-error checklist: the new statement introduces all objects and universes and cites their definitions, has no hidden proof, and has complete source labels; every non-elementary step cites its actual input; the new node is neither a clause-restatement nor a duplicate with the same hypothesis range; no source route uses SGA. Checked possible cycles in the chosen dependency statements and left the whole-graph check to server preflight. Every step is shorter than 2000 characters, and none hides an unnamed lemma. The longest is the explicit elementary finite-limit closure.

Edge cases: A may be initial (the localized sheaf topos is the degenerate slice, with empty covers allowed), terminal (the slice equivalence becomes the expected original topos), or any non-subterminal object (the fibre contains arbitrary pairs (x,a), so no mono assumption is introduced). The original sieve category may be empty or have no pullbacks: the bridge explicitly covers it. The bridge is also consistent with the trivial topology, where its sheaf category is a presheaf category, and the topology allowing empty covering sieves, where some sections are forced to be singletons. No point, enough-points, finiteness, or subcanonical hypothesis on the original presentation is used.

## Unfinished work

The one new supporting node is intentionally unsplit, as required by the one-level delivery rule. No part of the assigned item's six-step proof is left unstated. Dry-run and push results will be recorded after the required server checks.
