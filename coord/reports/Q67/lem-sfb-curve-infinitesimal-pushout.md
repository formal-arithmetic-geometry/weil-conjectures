## Worker report

Files written: the item `dag/nodes/sec-six-functors-basics/lem-sfb-curve-infinitesimal-pushout.json`, split into six steps, and five new statement-only nodes in that directory:

- `lem-sfb-scheme-affine-thickening-pushout`: statement, unsplit; no Mathlib match.
- `lem-sfb-flat-lfp-space-pushout-gluing`: statement, unsplit; no Mathlib match.
- `lem-sfb-space-thickening-topological-properties`: statement, unsplit; no Mathlib match.
- `lem-sfb-space-proper-base-change`: statement, unsplit; no Mathlib match.
- `lem-sfb-space-fibre-dimension-base-change`: statement, unsplit; no Mathlib match.

Attachments: none. Searching the exact blueprint tag and the concepts infinitesimal pushout, Rim/Schlessinger, algebraic space, flat pushout, and thickening in `lean/WeilConjectures/` found no declaration stating the item or the new algebraic-space assertions. The existing dual-number pushout is a special affine construction, not the arbitrary span here.

WANTED: none. All source texts used are available in `literature/stacks-project/`.

The original item had no proof. Its statement agrees with `quot.tex`, Tag 0D56 (`lemma-curves-RS-star`), with the family category defined in `situation-curves`. I only expanded the finite-presentation convention and the interpretation of geometric fibres for algebraic spaces, using the existing fibre-product node: this does not change a hypothesis or conclusion. The scheme-only fibre-product and geometric-fibre definitions were insufficient on their own to specify an algebraic-space total space, so the item now explicitly supplies that interpretation. No statement dispute is asserted for the item.

All requested searches ran through msearch.py; the original recorded searches remain intact. Each of the six subjects received LeanFinder in two different phrasings, Loogle, grep, and LeanSearch. The raw answers are saved in this sandbox and copied into the node records; searches.jsonl is the command's original log. All services answered. Scheme.GlueData glues opens; Spec of a ring pushout gives a scheme pullback, which is the opposite variance from the new pushout assertion. IsProper.isStableUnderBaseChange in Mathlib/AlgebraicGeometry/Morphisms/Proper.lean (read lines 35-72) quantifies over Scheme, not algebraic spaces. SmoothOfRelativeDimension and its base-change instances (read Smooth.lean lines 120-142) require smoothness and concern schemes. None is a one-line specialization giving the new node. Ring flat-pushout results and metric thickenings likewise do not match.

No stage-1 subtask remains unfinished. The new dependencies are deliberately unsplit, without proof sketches in their statements, for later workers. No Lean was written or compiled. No repository or launcher file was modified and no git command was run by this worker.

## Source citation applicability

The proof of Tag 0D1J (`quot.tex`, `lemma-spaces-RS-star`) cites Tag 09ZZ (`spaces-more-morphisms.tex`, `lemma-thicken-property-morphisms-cartesian`) for properness detection. The latter's statement requires a finite-order source thickening. Neither 0D1J nor 0D56 assumes finite order, so that invocation alone does not justify the required generality. I retain the statements and the flat-gluing route: local finite presentation has already been obtained, and Tag 09ZY (`lemma-thicken-property-morphisms`) parts (3), (4), (6) transfers quasi-compactness, universal closedness and separatedness for arbitrary thickenings. These, with the known local finite presentation, imply properness and finite presentation directly. This repairs applicability of the intermediate citation, rather than restricting the item to nilpotent or first-order thickenings.

## Not duplicates

Whole-DAG tag searches for 07RT, 07SY, 07W3, 09ZY, 04WP and 04NS found no existing node carrying these facts. Whole-DAG title and statement searches for scheme pushouts, flat-space gluing, thickening invariance and fibre-dimension base change found no statement covering these assertions. blueprint_refs.py was used with pushout, thickening, algebraic spaces, relative dimension and the tags; none was an exact match.

`lem-sfb-scheme-affine-thickening-pushout` vs `lem-sc-dual-number-scheme-pushout`: the existing node is the special construction from dual numbers over a field; the new node handles every affine morphism and every scheme thickening and proves the new leg is a thickening and the square cartesian.

`lem-sfb-space-fibre-dimension-base-change` vs `lem-trf-relative-dimension-base-change`: the existing statement concerns schemes and pure fibres of fixed dimension; the new statement allows algebraic-space total spaces and non-equidimensional geometric fibres with an upper bound.

`lem-sfb-space-fibre-dimension-base-change` vs `lem-kun-dimension-extension`: the existing statement concerns a finite-type scheme over a field, whereas the new one concerns a locally finite type algebraic space over an arbitrary scheme and an arbitrary base change.

`lem-sfb-space-fibre-dimension-base-change` vs `base-change-dimension`: the existing statement treats scheme curves and algebraically closed field extensions only.

`lem-sfb-space-thickening-topological-properties` vs `lem-weil-pbc-first-order-thickening-base-change`: the existing node says that a first-order scheme thickening remains first-order after pullback; it says nothing about invariance of the four morphism properties for arbitrary algebraic-space thickenings.

`lem-sfb-flat-lfp-space-pushout-gluing` vs `lem-sfb-curve-infinitesimal-pushout`: the new lemma concerns all flat locally finitely presented spaces, including nonproper spaces of arbitrary dimension, and all morphisms. It does not assert the item's properness, global finite presentation or dimension condition. Steps 4 and 5 prove these extra conditions; step 6 proves that the morphism lift is an isomorphism. No node restates a curve-gluing clause and no target condition is moved wholesale into a new node.

## Review by Q67

I read the statement and entire proof of 0D56 in quot.tex, and the statements and proofs of 0D1J, 07RT, 07SY, 07W3, 09ZY, 09ZZ, 04WP and 04NS, together with the definition of finite presentation of spaces (03XP) and situation-curves. The item remains the category of flat, proper, finitely presented algebraic-space families with geometric fibre dimension at most one. It does not require connectedness, reducedness, nodality, nonemptiness, Noetherian hypotheses or relative dimension exactly one.

For new nodes, I compared the arbitrary-thickening hypothesis and the cartesian conclusion against 07RT; the scheme pushout used by the flat-space gluing node is also an algebraic-space pushout by 07SY. In 07W3 I checked both part (3) (local finite presentation with flatness) and the concluding equivalence on all flat spaces. This gives the new restricted equivalence, not merely an object-level existence assertion. For the four-property node, 09ZY(3),(4),(6) has no finite-order or cartesian hypothesis; these are the clauses actually stated in the node. The proper-base-change node is exactly 04WP for spaces over a scheme. For the dimension node, 04NS(1) preserves relative dimension at each source point for locally finite type morphisms; a bound on every fibre is therefore preserved. The use is an upper bound, not equidimensionality or preservation of local ring dimension at arbitrary points, which would be different statements.

I reopened every statement cited by the six proof steps, including the new nodes and the existing definitions. citations.json copies verbatim each of these statements for every use.

Step 1 takes from the scheme pushout node precisely existence, the new thickening and the cartesian square. Equality of residue fields follows from the explicit quotient calculation, without identifying the ambient rings themselves. Step 2 uses the categorical equivalence actually stated by the flat-lfp gluing node, the properness base-change assertion actually stated by the proper node, and the dimension-bound preservation actually stated by the dimension node. Finiteness of presentation is recovered from its three defining conditions. The separated diagonal is a representable closed immersion, hence quasi-compact by the affine quotient description. Step 3 uses essential surjectivity with the specified compatibility isomorphism, which the gluing node states, not an unstated construction in its proof.

Step 4 uses 09ZY's four stated equivalences, applied to the morphism of thickenings constructed there. I supplied the local nil-ideal argument for pullback of a thickening; finite sums of nilpotents in a commutative ring are nilpotent, so an extended nil ideal remains nil. The remaining deductions are from finite presentation and finite type definitions read in def-sbc-locally-finite-presentation and def-weil-finite-type-morphism. Crucially no locally finite type property is inferred from reduction: local finite presentation is already known from step 3. Step 5 uses the existing algebraic-space fibre-product universal property, which its node states explicitly. The compatible geometric point over S exists because the residue fields agree from step 1. I wrote the fibre isomorphism on test schemes; no dimension theorem or unnamed identification is hidden in this step. Step 6 uses exactly the Hom-set bijection in the gluing node and proves invertibility by lifting the inverse and using faithfulness. This checks the unique compatible isomorphism clause without claiming curves have no automorphisms.

I tested the new statements on the identity thickening, T empty, empty family fibres, zero-dimensional fibres, reducible and nonreduced fibres, and nonproper flat affine spaces in the ambient category. For a genuinely non-finite-order thickening, take Spec(k) into Spec(A) where A=k[x_1,x_2,...]/(x_1^2,x_2^2,...) and the ideal (x_i) is nil but not nilpotent. The proof uses only individual nilpotence, so it does not introduce a uniform exponent. For dimension, d=0 and empty fibres are admitted, and no smoothness is used. All statements introduce their own objects; space topology and properness, finite presentation and the category of triples are defined or have the appropriate dependencies. New files contain no proofs. All proof steps have fewer than 2000 characters; none hides a long auxiliary lemma. The only correction to the initial planned route was replacing the inapplicable finite-order invocation 09ZZ by 09ZY and explicit use of the already known local finite presentation.
