# Stage-1 report: lem-sfb-derived-scalar-mate-composition

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-derived-scalar-mate-composition.json: existing statement, now split into six proof steps; no exact Mathlib match.
- citations.json: verbatim statement excerpts for every cited node in every step.
- report.md: this report. Searches are preserved in searches.jsonl. write_split.py is sandbox-only preparation and is not a project file.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched the live WeilConjectures source for the blueprint tag, scalar/mate/composition terminology, and derived scalar extension. The finite constant-coefficient and étale restriction-of-scalars declarations do not state this arbitrary ring-sheaf, unbounded pro-étale assertion with its balanced representative normalization. The general categorical helpers do not supply that normalization either.

## WANTED

None. The needed blueprint text, Stacks source and Mathlib source are present locally. The proof is explicitly agent-written: the blueprint's paragraph (3) motivates the direct-image composition obligation but does not contain this expanded lemma.

## Corrections and route

The mathematical statement and its hypotheses are unchanged. The imported item had no proof. Its blueprint.from.node was null: blueprint_refs.py ancestor follows created.item as far as lem-sfb-admissible-direct-image and then a stage-3 module name, Sheaf.SixFunctors.CtfStabilityDirectImages, which is not a DAG node. I filled the reference with det-thm-sf-ctf-stability-direct-images, the ancestor explicitly named by the item's source and by lem-sfb-admissible-direct-image's blueprint.from. Its existing via list and precise paragraph (3) place are retained. No other node or ownership metadata was edited.

The recorded dag/units/sk-thm-sf-ctf-stability.json still has the older sec-six-functors/master route, while this node and its source are in the current sec-six-functors-basics unit. I read both the recorded unit and its current main-20261015 _section.md, and the chapter. This split is below the unit and proves only the formal scalar-mate compatibility used with direct-image composition; it changes no unit statement or realization record.

The two generic tool uses are declared in split_report.tool_uses: lem-sfb-kflat-scalar-comparison-normalization and lem-sfb-ringed-derived-monoidal-comparisons. They provide normalization of comparisons and adjunctions, not another finiteness route. The argument never assumes properness, openness, scalar flatness, boundedness, or invertibility of the direct-image scalar mate.

## Searches and existing nodes

Read the inherited searches without deleting them. Ran five new logged searches using the required msearch.py command: grep and Loogle for mateEquiv_hcomp/mateEquiv_square, LeanSearch for scalar-extension/direct-image composition, and two distinct LeanFinder phrasings. Both semantic searches completed and their results are recorded in searches.jsonl; after a provider interruption their former tool sessions no longer existed, so their completed logs were read rather than rerunning them. No delivery command had run at that point.

Read Mathlib/CategoryTheory/Adjunction/Mates.lean, especially mateEquiv_counit and mateEquiv_hcomp (line 209) and mateEquiv_square (line 245). These prove general mate calculus but do not establish the balanced K-flat normalization. The underived SheafOfModules.pullbackComp and pushforward adjunction results likewise do not cover the whole item. The actual proof uses the existing specialized normalization statement and an explicit component calculation; no new Mathlib leaf is needed.

Searched the whole DAG by titles and mate/pasting/composition terms, and blueprint_refs.py search for mate, mate pasting, scalar, composition, scalar mate composition, balanced tensor, and scalar comparison. Read lem-weil-pbc-mate-pasting, lem-sfb-pasted-mates-counit-normalization, and lem-pc-adjunction-square-composition as possible general tools. There is no need to duplicate any of them: steps 3--4 give the short naturality calculation directly. Blueprint matches concerning scalar comparison, supported cup products and purity are not the present assertion.

## Not duplicates

No new nodes were created. In particular neither the pullback normalization clause nor the geometric composition clause was restated as a new node.

## Review by Q55

I read the current blueprint sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3), and det-prop-scalar-six-pullback.proof.md (1), which explicitly describes inverse-image tensor comparison and compatibility with geometric composition. I also read Stacks sites-modules.tex, lemma-tensor-product-pullback (Tag 03EL), and sites-cohomology.tex, lemma-derived-pullback-composition (0D6D), lemma-adjoint (07A6), lemma-derived-pushforward-composition (0D6E), and lemma-adjoints-push-pull-compatibility (0FPI). They support the existing normalization and adjunction infrastructure; the new component calculation is my argument, not a claim that Stacks proves this expanded normalization verbatim. No SGA route is used.

For step 1 I opened the full statement of lem-sfb-kflat-scalar-comparison-normalization. It gives exactly the inverse of Q(chi), equality with theta on K-flat representatives, an isomorphism on the whole derived category, the composition equation for theta, and the identity equation. All its ring hypotheses hold: A and B on the source are inverse images, and the sites use the stipulated small universe. Inverting theta's composition equation reverses the factors, producing lambda_g f_A^* after g_B^* lambda_f. No choice of K-flat resolution or flatness of A -> B is introduced in this step.

For step 2 I read the statement of lem-sfb-ringed-derived-monoidal-comparisons, not just its proof. It explicitly identifies the specified adjunction with the composite under the named pullback and direct-image compositors, gives the composite counit, and normalizes the identity. For geometric order g then f this is epsilon_g after g^*(epsilon_f), as written in step 2. I also opened def-weil-pbc-adjunction-mate: its statement gives the counit-transpose characterization and a bijection of natural transformations. Component injectivity here is the hom bijection in the given adjunction. These are precisely the uses in the step.

For step 3 I checked all domains: X = E U_A V_A K is in D(B_S), beta_f has target U_B F V_A K, and U_B(beta_g) has target U_B V_B G K. Transposition lands in Hom(M_B L_B X, G K). Naturality of the f-counit applies to beta_g: F V_A K -> V_B G K, without an isomorphism hypothesis. The step writes that naturality equation and the f-transpose substitution in full. It is elementary relative to the two cited statements; it does not invoke an unrecorded mate-pasting theorem.

For step 4 I checked that naturality of lambda_g is applied to epsilon_f at V_A K, a morphism L_A U_A V_A K -> V_A K. The written equality therefore has matching source and target. The g-transpose equation, the composite A-counit supplied by the comparison node, and the inverted lambda composition from step 1 give exactly the fg-transpose. Injectivity of the specified adjunction yields the result. Returning to the original endpoints forces kappa_B on the left and E(kappa_A) on the right; neither is reversed. This elementary computation is the content of the composition clause, rather than a new node whose statement repeats it.

For step 5 the normalization node supplies lambda_id = 1, the comparison node supplies the identity adjunction, and the mate definition evaluates its transpose to the identity. For step 6 I applied the proved composition equality separately to j,q and p,j'. Both paths have been explicitly rewritten as kappa_B beta_h T_X(kappa_A^{-1}); identifying each endpoint with the single functor for h proves the asserted square equality. This needs only equality of composite scheme maps and the stipulated canonical ring identifications, not a cartesian square. The comparison node is cited only for these specified composition identifications.

I tested identity maps, the identity ring map, zero rings/modules, the zero complex, and a square with an identity edge. All formulas reduce to the stated identity/counit equations. The argument works with a nonflat ring map (for instance constant Z -> Z/2) because scalar extension remains derived throughout. No cancellation of beta or tensor exactness appears. The ordinary-unbounded coefficient category is used consistently; there is no completed/adic or fixed-constant-coefficient substitution.

Against delivery-errors B--E: there are no new unsplit statements or hidden proof sketches, no elementary/duplicate/clause nodes, and no unsupported tag-only proof step. Every cited node's statement was opened and its used part quoted verbatim in citations.json. Proof dependencies are exactly the union of uses. All six steps are under 2000 characters; the only inline comparisons are inversion of an already cited equation and explicit naturality identities, so there is no long hidden lemma to extract. No source error or statement dispute was found.

## Unfinished work

None in this stage-1 split. No Lean was written or compiled. Independent mathematical review remains with the maintainer.

## Dry-run repairs

The first dry run rejected the phrase “the item's definition” in step 2 as a non-self-contained reference. Replaced it with “the definition of beta_h in the statement”; the definition and all its hypotheses are introduced in this node. No mathematical change.
