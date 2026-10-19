# Q41: lem-a1-constructible-pullback-t-exact

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-constructible-pullback-t-exact.json`: statement, split; no Mathlib match for the full completed/rational/common-stage assertion. The statement and statement dependencies are unchanged. Eleven proof steps, existing dependencies only.
- `citations.json`: one verbatim quoted statement per step/dependency pair.
- `report.md`: this report. Supporting searches and PDF text extractions are retained in the sandbox only.

## New nodes

None. Zero new Mathlib leaves. The finite scalar-model computation is written out in Steps 3 and 5 using existing exactness, flatness and inverse-limit statements; it is not handed off as a restatement of t-exactness.

## Attachments

None. I searched `WeilConjectures/` for the exact blueprint id, constructible pullback, and t-exact/cohomology notions. `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible.mapDerivedCategory_upperStar`, `CategoryTheory/DerivedCategory/Constructible.lean:263`, concerns ordinary coefficient-valued etale sheaves. `AlgebraicGeometry.ProEtale.DerivedCategory.boundedAdicConstructible_mapDerivedCategory_upperStar`, `SixFunctors/ProEtale/Adic/Truncation.lean:117`, and its cohomology/truncation comparisons concern the ambient derived category of `AdicSheaf l X`. The implementation notes in that file explicitly say that the rationalized E category has no cohomology sheaves implemented there. They do not supply this item's E rationalization, the common finite-field pair-category compatibility, or the specified point-fibre formula. No partial declaration is claimed as an attachment, and no compilation was run.

## WANTED

None. Read the locally supplied Bhatt--Scholze PDF, sections 3.1, 6.5, 6.6, 6.8, BBD 1.3.3, 1.3.6 and 1.3.17 (printed pages 29, 31, 36-37), and the existing generic t-structure nodes. Read Stacks `sites-modules.tex`, Tag 093M (`lemma-completion-flat`), and the completed-coefficient discussion in `proetale.tex` together with Tag 09C2 (`lemma-describe-constructible-complexes`). No SGA source is used.

## Problems in the imported node or brief

There was no proof in the item and only one inherited grep record. The source explicitly presents t-exactness as an agent inference, not as a theorem quoted verbatim from Remark 6.8.15. That remark distinguishes general ringed pullback from ordinary inverse image. The delivered proof respects this distinction: general completed pullback is computed on the finite scalar models; only immersion/site restrictions are taken to be exact ordinary inverse images. The statement itself is correct and is unchanged; no STATEMENT-DISPUTED correction is needed.

The current blueprint's ancestor is `lem-a1-finite-map-purity`, first paragraph about the fibre stalks. I read that proof, its chapter and the unit `sk-thm-dl-a1-upper`. The item supplies the t-structure/coefficient bridge for the already split intermediate fibre-comparison lemma. It does not change either the purity argument or the unit's filtration/Fourier route. Generic off-unit tools are declared individually in `split_report.tool_uses`.

## Searches and reuse

I ran the required searches through msearch.py and read their outputs; exact tool/query strings, hit names and verdicts are in the item and searches.jsonl. There were two semantic phrasings for the item, further semantic searches for the scalar-model calculation, Loogle queries and source greps. The online generic exact-functor hits are relevant tools, but not this item. The grep for `mapDerivedCategoryHomologyFunctorIso` in pinned Mathlib found nothing; the project's auxiliary Mathlib namespace contains such developments. The adic/perfect search returned algebraic AdicCompletion comparisons and free sheaf pullback, not completed constructible categories. LeanSearch was available for the searches used here; no failed service has been recorded as absence.

I searched all DAG nodes by t-exactness, completed pullback, integral local models, exactness, and the sources; ran blueprint_refs.py searches for pullback, t-exact, perfect and constant model; and read the relevant node statements. The existing `lem-weil-pbc-integral-stratified-perfect-characterization` already states precisely the detailed-integral-category comparison, including uniform reduction bounds and finite etale-origin witnesses. This avoids making a duplicate model lemma. I also checked transitively that the principal candidate dependencies do not reach the item; the server dry run remains authoritative.

## Not duplicates

No new nodes; no new/existing pairs to distinguish.

## Review by Q41

I read Bhatt--Scholze Lemma 6.5.8 and Remark 6.5.10 for exact completed-coefficient restrictions, Lemma 6.5.9(4)-(5) for completed pullback, Proposition 6.6.11 for perfect models on finite stratifications, Definition 6.8.10 and Proposition 6.8.11(3) for integral cohomology, and Proposition 6.8.14(2)/Remark 6.8.15 for rationalization and operations. I checked the item against these with the actual definitions of the rational E category and the Qlb common-stage category open. In particular, Qlb is the pair category, without an added Karoubi completion. I read the full statements of all cited nodes; citations.json reproduces them verbatim so the review can check each use against the interface rather than its proof.

Step 1 uses finite-type-over-Noetherian and the finite fibre dimension bound with base Spec k, then the precise integral stratified-perfect characterization. The preservation theorem supplies the completed pullback's constructible values and quotient comparisons, not t-exactness. A field has only the zero and unit ideals, and Spec k has one point; hence the base hypotheses hold. No separatedness is added to X or W.

Step 2 uses the characterization's actual stratum maps and cover models. The immersion comparison states exactness and completion compatibility, while weakly-etale-localization and site-restriction-exact give exact restriction to a cover. The products statement is sectionwise, so the explicitly given two-coordinate Roos model survives restriction. The exact-functor/cohomology statement supplies the resulting cohomology equation. None of these uses general completed ringed pullback as an exact ambient functor.

Step 3 is the displayed quotient-tower calculation on one bounded finite projective complex. The bounded-flat K-flat lemma licenses computing its derived reductions termwise. Completed-constant-sheaf-reduction gives the quotients; the canonical finite ring map and finite inverse-image exactness give the same scalar matrices after pullback. Milnor-epimorphic identifies the derived limit of each projective term with its ordinary limit. Exact Rlim permits the finite-cone construction of the bounded complex. Finite sums and a given projector can be evaluated directly in the product/limit coordinates; this is the elementary part, not an unquoted theorem about arbitrary constructible K. The argument keeps every quotient transition, rather than commuting canonical truncation with coefficient reduction.

Step 4 uses pullback-stratification and constructible-preimage exactly for the actual fibre products. The site definition gives the covering after base change. The integral composition lemma is valid for all the auxiliary schemes on which ell is invertible; the pro-etale covers need not be finite type or Noetherian. Its source and target are the detailed integral completed categories, so it compares the needed functors. Step 2 makes the immersion/cover pullbacks in that comparison ordinary restrictions. Empty inverse images are discarded without requiring a nonempty fibre.

Step 5 uses completed coefficients flat over the constant R, which Tag 093M and the cited reduction node state; it does not assert flatness over the inverse image of the completed source ring. The exact-functor/cohomology node gives the scalar cohomology equation. The underived tensor comparison is written with its map and inverse on balanced tensors. Since it is applied to the already zero source cohomology sheaf, ordinary pullback suffices to obtain zero on the target. I checked this on the torsion model R/pi and on finite free modules: R/pi is a degree-zero integral object even though its derived finite reductions have a negative Tor term. The proof does not confuse those reductions with canonical truncations.

Step 6 invokes noetherian-stratum-detection on W, whose Noetherianity was established in Step 1, and uses its statement on the underlying abelian cohomology sheaves. Exact restriction ensures this is the same cohomology tested on the covers. The definitions of the integral halves then give the two inclusions, using boundedness to choose the other endpoint of the interval. This also tests shifts of degree-zero objects, K=0, empty W and non-surjective h.

Step 7 uses completed-pullback-triangles for exactness and semilinear-scalar-localization for the actual raw rational functor and its shift comparison. The rational halves are isomorphism closures, so choosing a suitable integral representative is justified by their definition. It would be wrong to demand that every integral representative have the chosen rational bound; the proof never does. Step 8 uses the pair-category definition at one common finite field. Distinguished triangles and arrows have that finite-stage meaning, which proves exactness and the two bounds there as well.

Step 9 uses the bounded t-structures supplied by constructible-truncations, not merely the definition of a standard pair. The generic t-exact truncation-comparison lemma supplies unique canonical comparisons, including their maps. The heart-short-exact-triangles node states both directions used to prove exactness on the heart. Step 10 checks finite coefficient extension using exactly the pullback scalar-extension isomorphism, the stated truncation compatibility and the natural-transformation/composition part of the generic comparison lemma. Thus it checks canonical maps, not just objectwise isomorphisms.

Step 11 uses the exact point-sections theorem, whose hypotheses include algebraically closed k and the final object s. The fibre definition specifies sections followed by localization at E. Module-localization-exact and exact-functor/cohomology justify that localization step; localized-tstructure identifies rational truncations with integral ones. Point-sections-scalar-extension supplies exactly the point comparison, including identity and tower equations. I checked the degree-zero conclusion for a heart object, the zero fibre, and j positive or negative. The assertions at Qlb are the same finite-stage equations, transported by the comparisons in Step 10.

I checked B--E: no new unsplit nodes, no duplicate creation, no unrun searches, no changed statement, no hypothesis of flatness of h or separatedness, no source-to-target ring identification for a general h, and no circular dependence through the finite-fibre comparison. Every cited fact is a node statement, not an inference from that node's proof. All proof steps are below 2000 characters; the only inline scalar comparisons are the direct finite-projective tower calculation and the two explicit inverse balanced-tensor maps. These routine computations use the cited more general tools and do not warrant another node. I corrected the first draft by explicitly citing the K-flat criterion for the model and the rational-truncation comparison in the point-fibre step.

## Unfinished work

None in this one-level split. The existing unsplit dependencies remain items of their own; no claim is made that this stage-1 delivery supplies Lean proofs.

## Validation

Required `deliver.py Q41 lem-a1-constructible-pullback-t-exact --no-push` exited 0: `OK (not pushed) ... at e2ddaedd4a: preflight passed`. This includes the server DAG and split-review checks. No check_dag.py, review_split.py, preflight_delivery.py, Lean, Lake or compiler was run locally. The final push is performed by the normal delivery tool after this completed dry run.
