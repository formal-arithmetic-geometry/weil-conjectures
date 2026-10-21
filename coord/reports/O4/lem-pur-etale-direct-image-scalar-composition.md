# O4 stage-1 delivery

Item: lem-pur-etale-direct-image-scalar-composition. Date: 2026-10-21.

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-etale-direct-image-scalar-composition.json: statement, split into seven steps; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement quotation for every node/step citation.
- report.md: this report. searches.jsonl is the search command's own log; write_split.py is sandbox-only drafting material.

## Attachments

None. The project search under lean/WeilConjectures found neither the item blueprint tag nor a declaration establishing all its clauses. Ordinary extension-of-scalars/pullback coherence in SixFunctors/Etale/UpperLowerStar/ExtendScalarsComp.lean is not the requested unbounded, arbitrary A-to-B, direct-image assertion. RestrictScalarsLowerStar and CoefficientChange concern restriction of scalars rather than the present extension-of-scalars counit comparison. The already existing scalar composition node has a Sheaf/Paper/ScalarPullbackComposition.lean theorem whose proof is sorry, so it is reused as a DAG dependency, not claimed finished.

## WANTED

None: all sources used are available locally.

## Findings and changes

The starting node had a statement and prior Q11 Mathlib searches but no proof, and the sandbox had no earlier item or report. I retained those prior searches and metadata and appended only the seven searches recorded by this item's msearch.py calls. Their actual logged results are preserved in the new search entries. The second semantic phrasing found CategoryTheory.mateEquiv_hcomp and mateEquiv_vcomp; these are already covered by the existing Mathlib leaf lem-weil-pbc-mate-pasting. They do not alone state the item's assertion with the independently specified scalar, pullback and K-injective composition comparisons. Loogle found Adjunction.comp and its counit formula. The generic rightDerivedNatTrans_comp hits concern composition of transformations, not these mixed derived coefficient squares. The grep calls locate the generic mate laws and counit formula; their declarations were read at Mates.lean:170,209 and Basic.lean:568,580. No service was unavailable.

The statement's mathematical content is unchanged. I added def-pur-etale-scalar-pullback-iso as the precise definition reference for the canonical K-flat-normalized scalar/pullback isomorphism already in the statement, and retained its general tensor/pullback reference. No hypothesis was strengthened, no conclusion weakened, and no target was edited. No statement dispute was found.

The source Stacks 0E46, remark-compose-base-change, explicitly omits the verification. Thus proof_origin is agent, and the node supplies that verification rather than claiming the omitted calculation is printed in Stacks. I read sites-cohomology.tex at 0E46, 07A4 (lemma-pullback-tensor-product), 07A6 (lemma-adjoint), and 0D6E (lemma-derived-pushforward-composition), including the adjacent 0D6D K-flat composition argument. I also read the current main-20261015 cor-pur-vector-bundle-purity proof: paragraph 2 requires coefficient reduction to commute with composition of integration adjunctions before transposition. The present ordinary direct-image square supplies precisely that input. It does not change the purity route and uses no SGA source.

## Not duplicates

No new nodes. Existing lem-sf-scalar-pullback-composition provides the left square; existing lem-sfb-ringed-derived-monoidal-comparisons provides canonical composition and identity normalization. The ordinary direct-image scalar-composition assertion is not a restatement of either statement. Whole-DAG and blueprint searches included scalar composition, scalar pullback composition, direct-image composition, mate, and 0E46, and the relevant candidates' statements were opened. The blueprint reference remains the nearest ancestor cor-pur-vector-bundle-purity, with the already specified coefficient/composition paragraph and same_as empty.

## Review by O4

I read delivery-errors B through E, the stage-1 contract, the three blueprint levels in SETUP, GOAL, the chapter sec-smooth-purity and unit sk-prop-an. I checked the sources and the actual statement of each cited node, not a proof-only construction.

Step 1 uses prop-weil-pbc-inverse-image-modules-exact to identify constant-ring inverse image with exact module pullback. Its statement supplies exactness, the adjunction, and the canonical module identification. I then specialized lem-sfb-ringed-derived-monoidal-comparisons to the two constant-ring morphisms r and s. Its statement explicitly identifies the K-injective-normalized kappa with the canonical composite adjunction and gives the iterated counit and identity-adjunction clauses. Thus the step does not silently replace the given compositor by some abstract isomorphism. Small sites are those already used to define the item categories, and the cited result permits unbounded inputs and nonflat ring maps.

Step 2 uses lem-sf-scalar-pullback-composition, whose statement explicitly quantifies every unbounded A-module derived object, arbitrary commutative rings, and arbitrary composable scheme maps. I checked the substitution j1=r, v=s and j2=sr, the direction of both pullback compositors, and the positions of Q_X and Q_Z. def-pur-etale-scalar-pullback-iso fixes exactly the normalized isomorphism appearing there. The step does not use the bounded-below projection-formula comparison in lem-pur-etale-scalar-mate-projection; only the unbounded scalar-composition statement is applied.

Step 3 uses the canonical Hom bijection explicitly provided by def-kun-projection-formula-map and the counit characterization in lem-weil-pbc-adjunct-counit-identity. The latter states exactly epsilon composed with L of the adjunct equals the original arrow. This yields the displayed characterization of chi without assuming chi is invertible.

Step 4 is substitution into those cited formulas, rather than a further theorem: I type-checked its source P_r,B P_s,B Q_Z V and target Q_X M, and its comparison with F includes the inverse of Q_Z(kappa_A). I made explicit the naturality of lambda_sr that moves this inverse through the scalar comparison before applying the counit normalization. Thus the comparison is to the specified F, not just an isomorphic unnamed map.

Step 5 writes the full composite-adjunction adjunct of G and the precise naturality equation for epsilon_s at chi_r. The domains of that equation are P_s,B R_s,B Q_Y U and its codomain is R_r,B Q_X M. Applying P_r,B and composing epsilon_r gives the stated rewrite. It uses only functoriality and counit naturality from the already fixed adjunction.

Step 6 substitutes the two Step-3 equations and writes the naturality equation for lambda_r at epsilon_s,A,U. This epsilon has source P_s,A V and target U, so the order and all coefficient categories in the displayed formula agree. Its final arrow is exactly T of Step 4. The Hom bijection is injective, hence F=G; cancelling the source comparison restores precisely the item equation. These steps are elementary equalities from the earlier cited statements, not missing auxiliary lemmas.

Step 7 checks the identity rather than assuming it follows from the composition conclusion. The ordinary composition comparison of two identity pullbacks is the identity chain map, and the stated K-flat formula of lem-sfb-ringed-derived-monoidal-comparisons identifies its derived version with that map. I explicitly cited lem-pc-kflat-resolution, whose statement gives flat-term K-flat resolutions of every site-module complex, to pass from the formula to all derived objects. Applying the existing scalar-composition law twice at the identity makes lambda_id an invertible idempotent; cancellation makes it the identity. The canonical identity counit then makes chi_id the identity. No new lemma is hidden in the cancellation.

For B/C/D/E checks, there are no new nodes needing standalone statements, independent searches, or duplicate exclusions. Every external use has a verbatim quote in citations.json. The two off-unit normalized coherence statements and the K-flat-resolution tool are declared in split_report.tool_uses with their purpose. I checked their statement/proof dependency closure contains no path to this item. The steps carry the proof, rather than restating the conclusion in new children. Each step is under 2000 characters. The only elementary steps are the displayed substitutions, naturality squares, associativity and Hom-bijection cancellation; the structural coherence steps are marked non-elementary.

I tested the identities on M=0, an empty source scheme, the zero coefficient ring, identity scheme maps, and phi=id. For phi=id the scalar comparison becomes the usual identity coefficient comparison, so the formula reduces to the same normalized composition counit. For a nonflat finite quotient such as Z/4 -> Z/2 the proof still uses derived Q throughout and never applies ordinary tensor exactness, projection-formula invertibility, or preservation of K-injectives by Q. No boundedness, properness, Noetherian, constructibility or invertibility hypothesis is needed by any application. No Lean was written and no compiler or build tool was run.

## Unfinished work

None in the requested one-level split. All non-elementary inputs already have DAG nodes. The server dry run and direct delivery are performed with the prescribed delivery tool after writing this report.
