# Worker report

Item: lem-sfb-split-perfect-dual-tor-window. Group: Q29. Stage 1 only.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-split-perfect-dual-tor-window.json: existing statement, now split into seven proof steps; no statement change. Mathlib searches give no match for the complete item.
- citations.json: a verbatim statement quote for each of the eleven step/node citations.
- report.md: this report. searches.jsonl contains the actual search-command records.

New nodes: 0. New Mathlib leaves: 0. The shared repository and its Lean source were read only; no Lean was written or compiled.

## Attachments

None for the item. Searches in lean/WeilConjectures for its exact blueprint tag and the notions split perfect, strict perfect, dual and Tor did not find a declaration stating every clause. StrictlyPerfectOrdinaryEvaluation.lean proves degreewise ordinary evaluation on scheme opens, which neither has this general ringed-site scope nor supplies this item's K-injective comparison and Tor tests.

## Literature

WANTED: none. Read literature/stacks-project/sites-cohomology.tex, lemma-Rhom-strictly-perfect (08JH), the adjacent direct-summand Hom calculation, lemma-dual-perfect-complex (08JJ), section-hom-complexes, section-internal-hom, lemma-bounded-flat-K-flat (06YQ), definition-derived-tor (06YU) with its preceding K-flat construction, and lemma-tor-amplitude (08G1), specifically (2) implies (1). For the elementary tensor argument also read sites-modules.tex, definition-flat and the tensor-product definitions. The proof realizes the current main-20261015 blueprint's internal-Hom stability proof, The formula final sentence and Membership first sentence. It refines the local perfect-factor calculation without replacing the unit route.

## Existing nodes and searches

Whole-DAG searches for 08JH, 08JJ, 08G1, bounded-flat K-flatness, finite-free retracts, exact Hom and total-complex comparison found the reusable nodes cited below. tools/blueprint_refs.py ancestor identifies det-thm-sf-ctf-stability-internal-hom. Whole-blueprint searches for bounded flat, strictly perfect, perfect dual, exact term Hom and 08JJ found no alternative blueprint node stating this conjunction. The existing ringed-site finite-retract-dual-exact and bounded-dual-components nodes already supply the two tempting new sublemmas. The ringed-site-strict-perfect-hom theorem is more bundled than needed, so the proof uses its smaller existing exact-term comparison instead.

Ran LeanFinder twice with distinct descriptions, LeanSearch, Loogle and two grep queries using the required msearch.py command, and read all returned hits. The records are appended to the inherited item searches, which were retained. Module.Flat.of_retract (Mathlib/RingTheory/Flat/Basic.lean:172) and Module.Flat.of_free (:231) concern ordinary modules over a ring. They do not immediately give exact sheaf tensor on a general site. Generic derived support and K-projective results do not assert internal sheaf-Hom exactness. The item is therefore not a Mathlib leaf. The elementary tensor exactness argument is a proof step, rather than a new node.

## Not duplicates

No new nodes. In particular, no duplicates of lem-sfb-ringed-site-finite-retract-dual-exact, lem-sfb-ringed-site-bounded-dual-components, lem-pc-bounded-exact-term-hom-quasi-iso, lem-weil-pbc-independent-bounded-flat-kflat or lem-sf-ringed-kflat-single-tensor-comparison were created.

## Corrections and unfinished work

The imported item was statement-only, with no proof or Lean audit. Its statement is mathematically correct and was retained byte for byte. Added the explicit tensor exactness proof, applications of existing Hom/dual/K-flat results, and the numerical cohomology calculation. No STATEMENT-DISPUTED and no change to chapter or unit records. No part of this stage-1 split remains unfinished; the cited nodes retain their own existing proof obligations. This delivery does not claim to prove Lean declarations.

Three generic tools of other units are declared in split_report.tool_uses: bounded exact-term Hom comparison, bounded-above flat K-flatness, and the K-flat tensor comparison with a single sheaf. They supply homological machinery for the same perfect-dual route. All other theorem uses are in the item's unit. No tool_uses field was written by the worker.

## Review by Q29

I checked the item against Stacks 08JH/08JJ and 08G1, with the definitions of ordinary signed Hom and K-flat tensor open. The hypotheses are a small site, an arbitrary commutative coefficient sheaf, bounded source and degreewise splittings. Exactness here is sheaf exactness, so no enough-points argument and no global projectivity of finite free sheaves is used. No new node requires a source review.

Step 1 uses the actual short-exact-sequence clause of lem-sfb-ringed-site-finite-retract-dual-exact. I read its full statement: it assumes exactly maps i,p with pi=1 and finite rank, and concludes exact internal Hom, not exact global Hom. These data are supplied separately in every degree of E.

Step 2 is elementary from the tensor definition. The basis formulas identify finite free tensor with finite powers as sheaves, the natural inclusion/projection preserve the sequence, and projecting a local lift establishes exactness of the retract. Finite simultaneous lifts need only a common covering refinement, which a site supplies. I wrote these details rather than citing only flatness's definition for preservation of exact sequences. The flat-sheaf definition is used solely to name the exactness just proved. No chain-level splitting of E is assumed or constructed.

Step 3 cites lem-pc-bounded-exact-term-hom-quasi-iso, whose statement explicitly permits arbitrary unbounded target complexes, assumes exact internal Hom in every degree of a finitely supported source, and concludes the induced map is a quasi-isomorphism. Thus every K-injective augmentation is eligible, regardless of its bounds. For the representation assertion I specifically choose the fixed resolution in def-pur-derived-internal-hom, whose statement defines that derived object by the displayed Hom complex. I tightened this wording during self-review to avoid taking an arbitrary-resolution comparison theorem from a definition that fixes one choice.

Step 4 uses the complete signed component and support clauses of lem-sfb-ringed-site-bounded-dual-components. Its assumptions require only boundedness, so our splittings impose no missing hypothesis. The unique surviving factor has source degree -n and target degree zero. The sign is -(-1)^n=(-1)^(n+1). This is the stated cochain convention, not an unsigned dual.

Step 5 uses the actual dual-splitting and coordinate-dual clauses of lem-sfb-ringed-site-finite-retract-dual-exact at T=E^(-n). The composition is precomposition by pi, so it is the identity even when the original degreewise maps do not fit into chain maps. Applying the elementary argument already written in step 2 to this new termwise retract proves D's flatness. No conclusion about all perfect complexes is used as a replacement for this calculation.

Step 6 uses lem-weil-pbc-independent-bounded-flat-kflat, which is stated for essentially small sites, independent coefficient universes and the same sheafified tensor. Our small site and upper bounds b and -a satisfy it. Then lem-sf-ringed-kflat-single-tensor-comparison explicitly permits any sheaf M, with no flatness hypothesis on M, and gives the very termwise complexes and differentials used here. I checked both full statements, including the first lemma's definition of K-flatness and the second lemma's displayed representing isomorphism. The ringed-space-only lem-pc-bounded-above-flat-kflat was deliberately not cited for a general site.

Step 7 is the kernel/image definition from def-weil-derived-cohomology-sheaves applied to a zero degree term. It proves both inequalities outside each interval, using step 6's actual representatives. There is no assertion of sharpness at the endpoints or vanishing inside the interval.

I tested the zero complex, rank N=0 (the retract must then be zero), the zero coefficient sheaf and trivial topos, a single nonzero degree r (the dual is in degree -r), and an interval of width zero. For a two-term complex in degrees -1,0 the dual differential in degree 0 is minus precomposition, whereas for degrees 0,1 the differential in degree -1 is plus precomposition. These verify the reflection and sign independently. A zero term of E may still have a nonzero ambient free rank with i=p=0; the induced dual retract remains valid. The flatness and Tor tests require no constancy, constructibility or enough points, and nonflat M is expressly permitted by the tensor comparison. Every proof step has at most 1140 characters, so no long step conceals an additional lemma.

Against delivery-errors B--E: all imported fields and searches are retained, no statement-only child or duplicate is introduced, every non-elementary input is an existing cited statement, the quoted citations are verbatim, and the naturality needed for the retract calculation is written explicitly. The split carries an argument rather than moving the item into a renamed node. The required server dry run is the final mechanical verification before direct delivery.
