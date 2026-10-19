# Q08 stage-1 report

Item: lem-pur-projective-bundle-tautological-geometry.

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-projective-bundle-tautological-geometry.json: statement, split; 14 proof steps using existing DAG nodes. The mathematical statement is unchanged. Added the statement dependencies for module pullback, fibre product and the associated divisor line bundle, which already occur in its text.
- citations.json: verbatim statement evidence for every dependency of every proof step.
- searches.jsonl: actual searches recorded by msearch.py; prior inherited searches in the item are retained.
- report.md: this report. write_split.py is a sandbox-only preparation script and is not delivery content.

New nodes: 0. New Mathlib leaves: 0. The item is not a Mathlib leaf.

## Attachments

None. Searches for the exact blueprint tag, projective bundle, projectiveBundle, ProjectiveBundle and tautological in the project Lean source found no declaration proving the entire item. Existing projective-space declarations concern the trivial bundle, charts or twists and do not prove arbitrary locally free projectivization with all the stated compatibilities. The exact master source was also searched read-only; its declarations are reference material, not proof evidence.

## Literature

No WANTED documents. I read the current main-20261015 blueprint statement and proof of thm-pur-projective-bundle-formula, and unit sk-prop-an and its chapter. The ancestor's Step 1 needs the hyperplane/complement, divisor bundles and reduced intersection; Step 2 needs a global tautological line, properness and base change. The split supplies exactly this elementary scheme geometry without changing the rank-one/compact-support/localization/proper-base-change route.

For the item I read literature/stacks-project/constructions.tex: Tag 01OB (definition-projective-bundle), Tag 01OE (lemma-projective-space-bundle), Tag 01O3 (lemma-relative-proj-base-change, including its separate theta on twists), Tag 01N2 (lemma-base-change-map-proj), Tag 01NR (lemma-glue-relative-proj-twists), Tag 01MS (lemma-when-invertible, including its multiplication/division proof), Tag 01NG (lemma-standard-covering-projective-space) and Tag 01NH (lemma-projective-space-separated). I checked the tags against literature/stacks-project/tags/tags, rather than relying on section numbering. I also read Schemes Tag 01I9 in schemes.tex, the gluing construction of Sites Tag 04TR in sites.tex, Morphisms Tag 01W2 in morphisms.tex, and Divisors Tags 01WR and 01WX in divisors.tex. There are no new nodes needing further source readings, and no SGA source is used.

## Defects and corrections

The input was an unsplit statement with no proof, not a false statement. There is no STATEMENT-DISPUTED change. The quotient convention is important: Proj Sym F has the positive twist, and in rank one that twist is F, not its dual. I checked both in the explicit transition calculations.

I corrected tentative source tags while checking the local Stacks tag table: twist gluing is 01NR; effective Cartier divisors and their associated sheaves are 01WR and 01WX. The draft's base-restriction paragraph also needed to explain why its twist comparison is invertible, not merely a map of fractions: on a principal base restriction it is the identical free module H_i[1/s] T_i on both sides. That explanation is now in step 3. I deliberately do not infer the twist comparison from lemma-nagata-relative-proj-base-change-arbitrary, whose statement gives only the scheme comparison; step 8 supplies the module comparison itself. The inherited target-local properness node has an external pointer to 08J0; I used only its properness statement and checked the actual locality source 01W2, not a projectivity-locality assertion.

## Not duplicates

No new node is created. I searched the whole DAG and blueprint by projective bundle, projectiv, tautological, twisting, homogeneous localization and 01O3, as well as checking the existing symmetric-algebra base-change and polynomial nodes. In particular, lemma-nagata-relative-proj-base-change-arbitrary gives the underlying scheme, lem-nagata-affine-proj-scalar-extension fixes its chart maps, prop-nagata-relative-proj-functoriality gives graded-isomorphism and graded-quotient functoriality, and the standard-charts and dehomogenization nodes already give the coordinate tools. Creating new nodes for these, or for the item's separate clauses, would be duplication. The short extra calculations with a free rank-one chart, a polynomial quotient, a dual ideal, and an evaluation-at-zero ideal remain proof steps.

## Mathlib searches

I read all outputs from the Q08 msearch.py commands. The first LeanFinder phrasing returned affine Proj properness, Proj and chart constructions; the second phrasing returned linear-algebra Projectivization over division rings. Neither states the scheme-theoretic bundle-and-twist assertion. Loogle's "Proj", "baseChange" returned Weierstrass projective-curve base change. Greps for relative projectivization/tautological and for twist/baseChange in ProjectiveSpectrum had no hits. The broader IsProper|toSpecZero|pullback grep returned the actual Proj files; I read Proper.lean, including its terminal finite-type-over-degree-zero IsProper instance, and confirmed that it proves only one kind of affine properness, not this item. LeanSearch was rate-limited, and is recorded as unavailable, not no match. The second semantic phrasing was run before deciding no match. No searches were invented and no local compiler was run.

## Review by Q08

I checked the split against delivery-errors B through E with the cited statements open. The statement remains self-contained, every original clause survives, and the three added statement-dependency nodes define precisely its previously implicit pullback, fibre product and divisor line bundle. No new node hides a proof, restates a clause, or needs a separate Mathlib search. For the item, the recorded service results and the two semantic phrasings are real; unavailable LeanSearch is distinguished from an empty answer.

In step 1 I used def-amb-finite-locally-free-module for a Zariski frame cover and quasi-coherence, lem-weil-pbc-quasi-coherent-symmetric-algebra for affine sections and functoriality, the free-module-polynomial leaf for the algebra isomorphism, and symmetric-algebra-graded for its grading. Neither algebra node asserts graded compatibility by itself; the proof checks it on products in both directions. The rank is n+1, so there is always a homogeneous coordinate, including n=0.

In step 2 prop-nagata-relative-proj-functoriality really states the graded-equivalence and affine-restriction clauses used; def-nagata-relative-proj records the compatible restrictions; def-nagata-relative-projective-space defines exactly the Sym/free-module model used here; prop-nagata-proj-standard-open says the variables' opens cover because they generate the positive-degree ideal. There is no assumption of a frame beyond the chosen open U, and no use of a hypothetical relative projectivization theorem.

In step 3 def-weil-pbc-proj-twisting-sheaf gives the fraction modules and their restriction maps. The maps on them are written explicitly, and their composite applies the composite algebra map to the same numerator and denominator. On a principal base restriction the free generator T_i proves invertibility of the restriction comparison. def-nagata-relative-proj supplies the scheme overlap identifications, and lem-weil-pbc-site-module-sheaf-gluing applies to the set-indexed Zariski cover with ring sheaf O_P and the cocycle just checked. Its statement genuinely gives the glued module and local identifications. Non-affine overlaps are handled by affine refinements, not assumed affine.

Step 4 uses only the shifting/fraction definition, the definition of invertibility and the specified transitions of def-pc-projective-space-twist. Multiplication by T_i and division by T_i are explicit inverse module maps. This is a short calculation, not an uncited invertibility theorem. Matching the local bases proves the claimed pair identification and also fixes the positive sign.

In step 5 the arbitrary relative-Proj base-change statement is applied to the polynomial algebra over Spec Z. Its affine scalar extension is provided by symmetric-algebra-base-change plus step 1. def-nagata-projective-space-base-change identifies the precise base-change interface to which lemma-nagata-projective-space-base-change-proper applies. That lemma allows every base scheme, and lemma-nagata-projective-target-local requires only the open covering and the local properness just obtained. I checked the properness claim against 01W2; I do not use Zariski locality of projectivity.

In step 6 module-pullback-quasi-coherent supplies quasi-coherence; module-pullback-affine-sections allows an affine open W lying over an affine base open, not only a whole inverse image. The symmetric-algebra-base-change node allows arbitrary R to S and gives exactly the generator map written in the proof. Quasi-coherent-symmetric-algebra supplies both affine-section identifications. Symmetric-algebra-graded describes the spans that prove graded compatibility. Agreement on coefficients and degree-one generators proves restriction compatibility, so this is not a flat-only argument.

In step 7 I used only the scheme part of arbitrary relative-Proj base change and the graded-equivalence part of functoriality. The additional affine-proj-scalar-extension citation explicitly states the inverse images of D_+(f), the fraction ring map and uniqueness, under the graded scalar-extension isomorphism furnished in step 6. This is the needed C4 distinction between a canonical scheme isomorphism and a theorem that actually fixes its chart maps.

In step 8 the affine pullback theorem applies to the line module, since step 4 has already made it locally free and hence quasi-coherent. Tensoring the one-element basis computes the map and inverse without any flatness hypothesis. The overlap test is the displayed ratio rule and the degree-one fraction formula; it is a direct calculation from steps 3, 4, 6 and 7 and the twist definition. Maps of sheaves and their inverses glue by the ordinary sheaf axiom on sections. I checked that this proves theta, rather than citing a node whose statement omits theta.

In step 9 def-pc-module-pullback really includes identity and composition isomorphisms. The affine-proj-scalar-extension statement gives uniqueness from fractions; scheme-morphism-gluing gives equality after checking a covering; def-pc-fibre-product gives equality of the maps into the product from their projections. The proof checks the two coefficient composites and the line-bundle generator, so the compatibility is equality of the actual maps, not merely existence of some isomorphisms.

In step 10 the quotient is a surjective graded algebra map with the same degree-zero K, so the closed-immersion clause of prop-nagata-relative-proj-functoriality applies. The relative-projective-space definition identifies its source with P^(n-1). Dehomogenization-polynomial-ring identifies the chart map; expanding in T_0/T_j proves its kernel and hence the scheme-theoretic equation. The step does not infer a scheme identification merely from a point-set description, and the restriction of the twist is checked on its bases.

In step 11 projective-space-standard-charts explicitly gives both the non-vanishing open and its coordinate algebra, for the base-change model already compared in step 5. def-sbc-affine-space identifies Spec K[t_1,...,t_n] with affine space. This requires neither algebraic closure nor a restriction on the characteristic of K.

In step 12 the same standard-charts statement gives the local equations. A polynomial variable is a nonzerodivisor by the coefficient-shift calculation, whereas the equation on U_i is 1. def-nagata-effective-cartier-ideal is exactly this local principal nonzerodivisor condition, and def-pc-divisor-line-bundle defines the associated bundle as the dual ideal. The proof computes the dual transition, rather than importing a curve-only Cartier definition or an unnamed regular-section theorem. The dual basis satisfies h_j=(T_j/T_k)h_k, agreeing with def-pc-projective-space-twist. This checks O(D_i)=O(1), not O(-1).

In step 13 the coordinate-ring and covering clauses of projective-space-standard-charts are sufficient: all other charts have the unit ideal, and the remaining chart quotient is K by explicit evaluation. Thus the intersection is reduced scheme-theoretically. This holds for n=1 and arbitrary fields as well as larger n.

In step 14 standard-open coverage and dehomogenization on the zero-variable chart show that p is locally the identity of the affine base. Scheme-morphism-gluing is used for its inverse, and the twist's generator changes by the same unit as the frame of F. This verifies the potentially misleading rank-one case for a nontrivial line bundle, not just for a trivial line over a field. For the empty base all local assertions and gluing equations are vacuous and the same result holds. Zero rings, nilpotents in a general base, non-flat base changes, and arbitrary non-separated bases introduce no cancellation or division by a coefficient; only homogeneous coordinates on their own standard opens are inverted.

All source claims beyond the displayed computations are supplied by the cited node statements. citations.json contains a verbatim statement for every step/node pair, including the exact clauses just discussed. I checked every elementary label: the marked steps are multiplication/division of a one-element basis, equality on generators or fraction representatives, local dual bases, evaluation of polynomial ideals, or gluing a local inverse. There is no long non-elementary step over 2000 characters: every proof step is below that threshold. A traversal of the prospective dependency edges found no return path to this item. The source-specified unit route remains unchanged; the cross-unit algebra/scheme tools are declared in split_report.tool_uses.

## Unfinished work

None in this one-level split. The reused unsplit/imported dependencies remain their existing separate DAG tasks. No Lean file was written or compiled. Required server validation and delivery results are recorded below after the tool finishes.
