## Worker report

Item: lem-sfb-integral-coefficient-square-normalization. Group Q111. Stage 1 only.

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-coefficient-square-normalization.json: statement unchanged; eight proof steps; status split; preserved prior metadata and searches, appended the searches run by Q111.
- citations.json: one verbatim statement quotation for each node used in each proof step.
- report.md: this report and self-review.

## New nodes

None. Zero Mathlib leaves. All required general results already have DAG nodes. In particular I did not create a duplicate completion-flat node or a special-case K-flat pullback node.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, integralCoefficient/integral_coefficient and completion/pullback terminology. No declaration found states the whole item, including the normalized chain isomorphism, prescribed quotient maps and all three K-flat assertions. The continuousSheafToLowerStar_naturality result in AlgebraicGeometry/ProEtale/ContinuousSheafPullback.lean concerns continuous abelian coefficients and does not give this whole statement. I read its statement and the surrounding pullback construction; I did not claim an attachment from it.

## WANTED

None. The source material needed for this split is present. No SGA source was used.

## Findings and changes

The item was unsplit with no proof. Its assertion is retained verbatim. The phrase "completed scalar-extension identification" refers to ordinary scalar extension along the isomorphism of the completed coefficient ring; the proof explicitly uses the ordinary tensor pullback, and introduces no extra completion functor. The argument must not claim that geometric inverse image commutes with arbitrary inverse limits. The coefficient presentation is obtained instead from the existing normalized compact-adic identification.

The proof of the unit's integral constructibility result is not replaced: this item supplies precisely the coefficient and representative facts in the first and final paragraphs of det-lem-int-tensor-pullback. The chapter and unit records are unchanged.

## Searches

I read the item, dag/chapters/sec-six-functors-basics.json, dag/units/sk-lem-int-tensor.json and the current blueprint proof. I searched the whole DAG for Tags 093M and 0G7E and completion-flat/pullback-K-flat, plus constant-completion, scalar restriction and constant inverse-image names. I read the full statements of every node cited in the eight steps. Before settling the zero-new-node split, blueprint_refs.py ancestor identified det-lem-int-tensor-pullback; blueprint searches included "completion flat", "K-flat", "constant.*complet", "cartesian", "restriction.*scalars", "coefficient square normalization", "constant-to-integral", "flat-term K-flat", and "inverse image of the coefficient". The latter returns sk-prop-sfb-cartesian-coefficients, which is used, and none states the entire item.

All new Mathlib queries were run through the prescribed msearch.py Q111 item command and their actual results are in searches.jsonl and appended to mathlib_searches. Both LeanFinder phrasings were read: the first returned algebraic completion flatness, completion naturality and local cohomology; the second returned ordinary sheaf pullback identities and free-generator comparisons. Loogle returned the restriction-of-scalars definition and its elementary equations. LeanSearch was available and returned constant-sheaf characterizations and light-condensed discreteness. The two source greps were for completion/K-flat in Algebra/Category/ModuleCat/Sheaf (no hits), and for restriction/pullback (17 hits). I read ChangeOfRings.lean:30–43 and PullbackContinuous.lean:45–65. Their statements do not give the completed pro-étale coefficient theorem; none is recorded as a match. Inherited O3 searches remain unaltered and are distinguished from Q111's six logged queries.

## Not duplicates

No new-node/existing-node pairs: no new nodes are proposed. The split reuses lem-sfb-compact-adic-continuous-identification, lem-weil-pbc-completed-constant-algebra-flat-quotients, lem-weil-pbc-flat-scalar-restriction-kflat and lem-weil-pbc-ringed-topos-kflat-pullback rather than restating them.

## Tool uses

The split_report.tool_uses entries declare existing general tools from other units; no maintainer-owned tool_uses field was written. The integer topology and normalized coefficient presentation check the hypotheses of the Stacks completed-ring tool; constant-ring inverse image supplies the canonical scalar comparison; the two K-flat tools cover scalar restriction and ringed-topos pullback. These are generic lower-level tools needed by the same blueprint route, not alternative routes to constructibility. sk-prop-sfb-cartesian-coefficients is expressly invoked in the blueprint's opening sentence. Its statement is used only for untwisted integral coefficients and exactness. The proof never applies its finite-ring clause to the infinite discrete ring A: that case comes from lem-pe-constant-left-module-inverse-image.

## Review by Q111

I read det-lem-int-tensor-pullback.proof.md, including its first paragraph and final "Comparison with the Stacks Project" paragraph; I also read the current integral-limit proof, steps 1–4, and the Cartesian coefficient and module-pullback definitions. In Stacks sites-modules.tex I read Tag 093M, label lemma-completion-flat, including its canonical quotients. In sites-cohomology.tex I read Tag 0G7E, label lemma-pullback-K-flat: importantly its hypothesis includes flat terms as well as K-flatness, and its objects are ringed topoi, not merely ringed topological spaces. There are no new nodes needing a separate source comparison.

Step 1 uses the actual statements of def-weil-l-adic-coefficient-extension, lem-sfb-integers-profinite-tower, lem-sfb-integers-coset-basis and lem-sfb-compact-adic-continuous-identification. The first supplies the nonzero uniformizer and domain, the next two compact Hausdorffness, finite quotients and the quotient-fibre basis. These are precisely the compact-adic identification's hypotheses. That node states the ring isomorphism and also its scalar-normalized projections. Thus the constant-to-limit map agrees with i_Z by the constant sheafification universal property. No exactness of inverse limit is being assumed.

Step 2 uses only the Noetherian part of lem-sfb-admissible-scalar-realization-exact and the full degree-zero flat algebra/quotient conclusions of lem-weil-pbc-completed-constant-algebra-flat-quotients. I checked that its specified presentation S may be R_Z and its map c may be i_Z because step 1 proves the projection requirement. The n+1 indexing is shifted to n-1 for the item's n>=1. The conversion from tensoring with A/pi^n to the module quotient is written with inverse maps, and the generator formula gives exactly the specified quotient projection. This is more than an arbitrary isomorphism of quotient sheaves.

Step 3 uses Cartesian integral coefficients, the exact constant-ring comparison, the scalar-to-continuous map's definition, the constant-sheaf pullback comparison, and the coefficient morphism's definition as a component of a natural isomorphism. Each cited definition actually describes these maps; none is cited as an exactness theorem. Naturality at the discrete-to-adic identity gives the displayed square. The constant comparison is canonical through adjunction and takes constant scalars to the same scalars, agreeing with a_C. This step is elementary naturality of that already specified component, and not an uncited claim that an arbitrary coefficient square is Cartesian. It does not need g^{-1} to commute with completion.

Step 4 uses the tensor formula in sk-def-sfb-module-pushforward-pullback and the unchanged underlying sheaf/action formula in def-pc-sheaf-restrict-scalars. I checked the balancing relation, both inverse compositions, and the compatibility with sheafification. The same calculation applies to C, whose coefficient map is an isomorphism by step 3. Step 5 is then the elementary comparison of the two actions on V: the two written multiplication operators agree by the square in step 3. Its formula for d_H and its inverse are given on tensor generators. Naturality and commutation with differentials are the same written R-linear-map equality; no sign or totalization is inserted, and no new independent lemma is concealed. I changed the differential notation to partial_H^q so it cannot be confused with the comparison d_H.

Step 6 uses the exactness clauses actually present in sk-prop-sfb-cartesian-coefficients and lem-pe-constant-left-module-inverse-image. The latter is a fixed arbitrary-ring statement, hence covers the infinite discrete A. Step 4 identifies its lift with the tensor-defined g_C^*. I did not infer exactness from the mere existence of an adjoint.

Step 7 checks the flat-algebra hypothesis using step 2 and applies exactly the two conclusions of lem-weil-pbc-flat-scalar-restriction-kflat. Its statement explicitly permits possibly unbounded complexes. Step 8 uses lem-weil-pbc-ringed-topos-kflat-pullback twice, whose statement really concerns morphisms of ringed topoi and flat-term K-flat complexes. The inputs are P and r_YP, and step 7 provides the flat terms and K-flatness required for the second application. A topological-space pullback lemma would not suffice and was deliberately not cited.

I checked the small cases n=1 (the shifted index is zero, which the quotient theorem includes), g=id (both multiplication identifications give the usual tensor unit), the zero complex, the empty scheme (the ring and module maps are the unique ones and all exactness assertions remain valid), arbitrary integer degrees and unbounded complexes. The proof uses no finite-length hypothesis on H or P and no derived completeness or constructibility assumption. The field condition and ell!=p are retained, although these particular coefficient tools work more generally. No statement dispute arose. I checked B1–B10: zero new nodes, no duplicate or hollow definition, one-escaped TeX, preserved blueprint and import metadata, genuine logged Mathlib searches and no unsupported attachment. For C1–C8 every non-elementary tool is a node citation with a verbatim statement quote, the proposed dependencies do not lead back to the item, and generic off-unit uses are declared for review. For D1–D5 the proof contains the multiplication and scalar-action arguments rather than new nodes repeating the item. For E1–E7 the applications above have the required hypotheses; the completed coefficient sheaf is kept distinct from the constant sheaf. Every step is under 2000 characters, so none needs the long-step audit exception.

## Unfinished work

No mathematical part remains in this one-level split. Its existing cited nodes retain their current project status; I have not claimed their Lean proofs are finished. Server dry run and direct push are performed after this report is written; their results are recorded below.

## Validation

The required deliver.py --no-push completed with exit 0 and printed OK (not pushed), preflight passed, at cb4ee6170c2. This includes the server's DAG and split-review checks. No local checker, compiler, Lake command or repository git command was run. The only report change after that receipt is this validation paragraph; the delivery tool validates the final report again on push.
