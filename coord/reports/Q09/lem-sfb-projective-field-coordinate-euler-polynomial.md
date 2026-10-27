# Q09 stage-1 report: lem-sfb-projective-field-coordinate-euler-polynomial

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-projective-field-coordinate-euler-polynomial.json`: existing statement node, now split into seven proof steps; Mathlib verdict: no match for the complete theorem. Statement and statement dependencies are unchanged.
- `citations.json`: sixteen entries, one per step/node citation, copying the cited statements verbatim. Full statements are included so the reviewer can check the exact hypotheses as well as the conclusions.
- `report.md`: this report. The required search command also wrote `searches.jsonl` in this sandbox.

New DAG nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint id, coordinate/Euler combinations, numericalPolynomial, hilbertPoly, and projective_field_hilbert found no declaration stating this item. The Euler polynomials under EtaleCohomology/Purity/RealSheaves/EulerRadius concern products of reciprocal-root factors, not coherent Euler characteristics. In particular the similarly named field theorem listed on the parent node is in Sheaf and its recorded proof is sorry, so it is not an attachment.

## WANTED

None. All mathematical sources used here are present locally.

## Corrections and scope

There is no statement dispute. The item was unsplit with an empty proof, and this sandbox initially had no copied item or earlier report/search log. I preserved the existing mathematical statement, citation searches, created record, and inherited blueprint record. I appended five actual Q09 searches with their exact query texts and log results.

The proof avoids three possible gaps: the projective convention includes quasi-compactness, so step 1 obtains it from the finite affine cover before using projective implies proper; step 3 compares negative as well as nonnegative twists explicitly, and identifies ambient transition-function twists with the Proj shifts used in the coordinate lemmas; and the ideal comparison is for every actual homogeneous quotient, not only a saturated ideal. I do not infer full Euler polynomial existence from an eventual Hilbert function.

The imported `lem-pc-projective-proper` bibliography points to 01W5/0BX4, but its statement is the needed general theorem. I read the actual direct source: Morphisms Tag 01WC, `lemma-locally-projective-proper`. No other node was edited. The item has no blueprint_update field. The current main-20261015 unit was read at `blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`, as well as the unit/chapter JSON records. The inherited unit JSON points to an older sec-six-functors source, whereas the current chapter is sec-six-functors-basics; this delivery preserves that inherited metadata and stays on the field-polynomial prerequisite route.

## Not duplicates

No new node is introduced. I searched the whole DAG by the four main Stacks tags and the Hilbert/Euler/graded-section notions, read the existing candidate statements, and reused:

- `lem-sc-snapper-numerical-polynomial`: general coherent sheaf and several invertible sheaves, hence gives all-integer existence here by one specialization.
- `lem-sfb-projective-closed-subscheme-homogeneous-ideal`: arbitrary base ring and explicit ideal giving a closed subscheme, hence gives the existence clause here.
- `lem-sfb-projective-coordinate-ring-euler-polynomial`: eventual equality for an actual homogeneous quotient, including the empty and unsaturated cases.
- `lem-sfb-projective-twist-euler-section-uniqueness`: eventual equality with sections and polynomial uniqueness, for any finitely presented quasi-coherent sheaf.

The whole-blueprint `blueprint_refs.py search` queries `numerical polynomial` and `Hilbert polynomial` each found only the degree/ample Hilbert-polynomial nodes. Those do not state the complete all-integer/any-defining-ideal result of this item. The ancestor command reports None; the existing null ancestor and its exact explanatory place/via chain are retained.

## Mathlib searches

All searches ran through the prescribed msearch.py command for Q09 and this item. The log contains leanfinder with the combined coordinate/Euler statement, loogle `"hilbertPoly"`, grep `hilbertPoly|numericalPolynomial|eulerChar` restricted to AlgebraicGeometry, leansearch with the all-tensor-powers statement, and a second leanfinder phrasing using Snapper and proper schemes. Every service answered successfully. I read the returned hits and Mathlib/RingTheory/Polynomial/HilbertPoly.lean lines 18-44: its polynomial records eventual coefficients of p/(1-X)^d, and its explicit TODO is graded-module Hilbert polynomials. `Polynomial.existsUnique_hilbertPoly` therefore does not supply the geometric/cohomological identification in this item. The Proj properness and section-localization hits do not state the polynomial theorem. The old searches inherited from the live item remain intact.

## Review by Q09

I read Stacks varieties.tex Tag 0BEM, `lemma-numerical-polynomial-from-euler`, with its properness, coherence, and invertible-module hypotheses; Tag 08AE, `lemma-hilbert-polynomial-H0`, which uses eventual vanishing. I also read constructions.tex Tag 03GL, `lemma-closed-in-projective-space`, and coherent.tex Tag 0AG7, `lemma-recover-tail-graded-module`, which applies to finite graded modules over a degree-one-generated ring with Noetherian degree-zero ring. These sources justify the imported field-polynomial route. There are no new nodes requiring separate source validation.

For step 1 I opened the statements of def-pc-proj, def-weil-closed-immersion, def-pc-projective-morphism and lem-pc-projective-proper. The first supplies standard affine charts, the second says closed immersions restrict to affine quotient schemes, the third requires precisely the given projective-space embedding and quasi-compactness, and the fourth supplies properness. Thus no projective-to-proper assertion is being taken from a definition. The finite affine preimage cover proves the quasi-compactness required by the convention before invoking the theorem. The source 01WC was read directly.

For step 2 I opened def-weil-proper-morphism, lem-weil-pbc-finite-type-over-noetherian, pqf-def-coherent and pqf-lem-coherent-ft-locnoeth. Properness supplies finite type; Spec k is Noetherian since the field has only two ideals; 01T6 therefore supplies a Noetherian X. The structure module is visibly quasi-coherent of finite type (on Spec R it is the module R generated by 1), which is exactly the hypothesis of the coherence equivalence. I read morphisms.tex 01T6 and coherent.tex 01XZ, including the explicit structure-sheaf corollary. This verifies rather than assumes the input to Snapper.

For step 3 I opened each of def-pc-projective-space-twist, def-pc-module-pullback, def-sc-invertible-module and def-weil-pbc-proj-twisting-sheaf. Their statements give the transition functions, pullback formula, rank-one meaning of invertibility, and degree-d localization description respectively. The elementary argument sends one displayed local basis to the other: on overlaps the multipliers are the identical powers of z_j/z_l. For d<0, inverse bases give the negative power. For d=0 both bases are 1. This also explicitly checks that the Proj shift convention M(d)_a=M_(a+d) has the required sign. All comparisons are compatible on overlaps because their displayed multipliers agree; no unexplained tensor/pullback theorem or abstract comparison is hidden here. I read constructions.tex 01MN for the shift/twist definition. This 793-character step is a local rank-one calculation, not a new lemma node.

For step 4 I opened lem-sc-snapper-numerical-polynomial: it states the numerical polynomial for a proper scheme, a coherent F and invertible L_i on all integers, not merely eventual equality or the ample case. Steps 1-3 supply each hypothesis with F=O_X and r=1. The tensor unit and the explicit transition calculation identify its values with the requested twists. Integral values are part of its numerical-polynomial conclusion. Thus this step uses the general theorem's statement without reproducing its induction or adding an ampleness hypothesis.

For step 5 I opened lem-sfb-projective-closed-subscheme-homogeneous-ideal. Its conclusion is equality as a closed subscheme of the specified projective space, not merely an abstract isomorphism. Its general ring R may be k, and it explicitly permits empty or nonreduced schemes. This is exactly the presentation used later. I read 03GL's ideal construction and chart proof.

For step 6 I opened lem-sfb-projective-coordinate-ring-euler-polynomial. Its statement says that for each homogeneous J, the actual graded quotient has eventual dimension equal to the Euler characteristic of the pulled-back ambient twist. That supplies precisely the non-elementary comparison used; I take no assertion from its proof. The closed-subsheme identification is over the same P, so its pulled-back twist is the one of this item. Step 4 now substitutes Q_X for the Euler value. Both the cited statement and 0AG7 allow irrelevant torsion: neither imposes saturation. The unit ideal is expressly included.

For step 7 I opened lem-sfb-projective-twist-euler-section-uniqueness. It explicitly contains the uniqueness of polynomials agreeing eventually with the section-dimension function, so this is not a citation of Serre vanishing alone for an unstated root theorem. I checked its input F is quasi-coherent and finitely presented: the structure sheaf has the displayed zero-relations, one-generator presentation. Step 3 identifies E_m with the actual O_X(m). Its vanishing gives Euler=H0 for large m, so each of the two proposed kinds of polynomial agrees with that function after the maximum of the thresholds. Its uniqueness clause then proves both requested uniqueness assertions.

I checked the small cases against the statements, not only the main projective example. For n=0, J=0 gives X=Spec k, Q=1 at every integer; J=(z_0^a), a>0, is unsaturated with empty Proj and quotient pieces eventually zero, giving Q=0; J=(1) gives the zero quotient immediately. For J=0 in general, Q(d)=binomial(d+n,n), including negative d, as expected from the all-integer Euler formula. A nonreduced point in P^1 still has a constant length polynomial; none of the cited lemmas assumes reducedness. On empty X, O_X and all its cohomology groups are zero, Snapper gives the zero function and the existing uniqueness clause gives the zero polynomial. No support-dimension or nonemptiness assumption is introduced.

Against delivery-errors B-E: no new statement-only nodes, no relabelling of the item's clauses, no new definitions needing a missing dependency, and no new uncited non-elementary facts. The only elementary comparison is written locally in full. Every uses entry has its statement copied verbatim into citations.json; proof_deps is their exact union. Every step is below 2000 characters. The four off-unit statement tools are declared in split_report.tool_uses with their purpose; none replaces the direct-image/alteration unit route. Definitions are used only for their defining constructions. The cited dependency statements were read in full; none depends back on this field item through its recorded statement or proof route.

## Unfinished work

None within the one-level stage-1 task. Existing cited unsplit lemmas remain separate items; no Lean was written and no compiler, Lake, local checker, or repository git command was run. The required server dry run and delivery are recorded by the delivery command.
