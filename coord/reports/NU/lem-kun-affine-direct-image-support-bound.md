# Stage-1 report: lem-kun-affine-direct-image-support-bound

Files written under dag/nodes/sec-smooth-purity/:
- lem-kun-affine-direct-image-support-bound.json: original statement retained; five-step split.
- lem-kun-affine-support-vanishing.json: statement, unsplit; no Mathlib match. The separably closed case of 0F0W.
- lem-kun-strict-local-algebraic-residue-models.json: statement, unsplit; no Mathlib match. Geometric approximation with residue control, not a cohomology assertion.
- lem-kun-transcendence-degree-tower.json: statement, Mathlib leaf, trdeg_add_eq (or lift_trdeg_add_eq), trdeg_eq_zero_iff; files and lines read are in mathlib_match.

Attachments: none. Searched the project Lean source for the blueprint tag and support/transcendence-degree terminology, including the Sites/CohomologicalDimension and etale Kunneth files. The existing general cohomological-dimension theorems do not state the support-sensitive affine bound and include sorry declarations. The upstream master was reference material only, not treated as a finished proof.

WANTED: none.

The original node had no proof or proof dependencies. Its statement agrees with 0F0X, including arbitrary torsion abelian etale sheaves and arbitrary fields; no invertibility or constructibility hypothesis was added. The unit and chapter are unchanged. The ancestor is lem-kun-0f10, whose affine-case input is this item. The proof follows the same strict-local/affine-vanishing route, working directly with affine f rather than embedding it into a projection.

## Source error

Stacks etale-cohomology.tex, lemma-interlude-I (0F0X), asks for arbitrary finite-type L-subalgebras of the strict henselization containing the coordinate ring, then infers algebraicity of residue extensions from containment in an ind-etale algebra. That inference is not valid for arbitrary intermediate subalgebras. For example let K be algebraically closed, A=K[x,y], and R the strict henselization at (x,y). The subalgebra A[x/(1+y)] lies in R (1+y is a unit), but is A[t]/((1+y)t-x). Above the prime (x,y+1) its fibre is K[t], so its generic residue field is transcendental over K. Taking K algebraically closed makes L=K available in the b=0 situation. This is an error in the indicated justification, not a counterexample to 0F0X.

The replacement uses compatible etale models, as in the actual proof of 0F0U. The new geometric node is the precise missing input. Here is its intended construction for the next splitter: after shrinking about y choose algebraically independent regular functions t_1,...,t_b whose residues form a transcendence basis. Write P=K[t_1,...,t_b], L=Frac(P)^sep, and R=colim B_j through pointed affine etale neighbourhoods of the affine U. The map L -> R comes from the strict-local map of the generic point of Spec P (the proof of 0F0U). Write L=colim A_i through its pointed etale P-neighbourhoods. Use compatible triples (i,j,A_i -> B_j) and set C_{ij}=B_j tensor_{A_i} L. Finite presentation gives a small filtered system with colimit R. These are finite type over L, map to U, and have algebraic residue extensions over U: B_j is etale over U and Spec L -> Spec A_i has algebraic residue extensions on its image. The tensor construction preserves this algebraicity after further base change. These C_{ij} need not embed in R; arbitrary subalgebras are not used. In the item, step 3 writes out the further base-change residue argument.

For the absolute vanishing node, the proof of 0F0W uses 0F0N to express G as a filtered colimit supported on closed subsets Z inside E_c. The dimension of Z is at most c; apply the affine bound 0F0V over separably closed L, exact closed-immersion pushforward and cohomology continuity. This is a strictly smaller absolute cohomology ingredient, not the relative support estimate restated. Its proof remains for the next splitter, as required for a new unsplit node.

Nothing is left unfinished in the item's argument; the two genuine input lemmas remain statement-only nodes by the one-level split rule.

## Not duplicates

lem-kun-affine-support-vanishing vs lem-per-artin-gabber-affine-curve: the latter states perverse amplitude bounds for Rf_!, with separatedness and fibre-dimension hypotheses; the new lemma states ordinary torsion sheaf cohomology vanishing from a support bound over a separably closed field.
lem-kun-strict-local-algebraic-residue-models vs lem-kun-0f0u: 0F0U's imported node only asserts smaller-dimensional models for positive b. The new lemma requires trdeg_K L=b and algebraic residue extensions at every model point, covers b=0, and asserts no dimension decrease. The existing statement cannot supply these requirements.
lem-kun-strict-local-algebraic-residue-models vs lem-kun-affine-direct-image-support-bound: the new lemma is a geometric inverse-limit presentation with no sheaf or cohomology; the item proves a higher direct-image support bound using this and separate vanishing and continuity inputs.
lem-kun-strict-local-algebraic-residue-models vs lem-kun-0f10: finiteness of cohomological dimension is not a geometric presentation with coefficient-field and residue control.
lem-kun-strict-local-algebraic-residue-models vs lem-per-artin-gabber-affine-curve: the latter states perverse compact-support direct-image amplitude, not strict-local algebraic approximation.

Other near matches read: lem-kun-cp-approximation treats only closed-point support, not E_c for arbitrary c; thm-sc-affine-torsion-cd bounds by the dimension of the whole scheme, not the support. Neither states the new absolute support lemma. The DAG was searched by 0F0W, 0F0U, 030H, support-in-subset, strict-local and transcendence terminology. Blueprint searches were run across all chapters for support, transcendence, strictly henselian, affine torsion, support-in-subset, 0F0W, 0F0U, tower, residue field, 030H and support dimension. No existing statement gives either new lemma or the tower identity. Lean searches by ids and notions found no project attachment. All recorded Mathlib searches were run using msearch.py; LeanSearch failures are recorded as unavailable. Alternative semantic phrasings were tried before declaring absence. The tower match was read in Mathlib, including the unnamespaced theorem names and actual field/scalar-tower hypotheses.

## Review by NU

I read the full statements and proofs of 0F0X (lemma-interlude-I), 0F0W (lemma-interlude-II), 0F0U (lemma-strictly-henselian), and the support approximation 0F0N (lemma-support-in-subset). I also checked 030H (lemma-transcendence-degree-tower) in fields.tex and the actual Mathlib declarations. The two new unsplit nodes contain statements only, with all objects introduced and definition dependencies; neither hides the item as a renamed clause. The source error above was corrected by replacing arbitrary intermediate subalgebras with compatible models, without changing the item statement.

Step 1 uses the affine permanence node's explicit quasi-compact and separated clause and the strict-henselization stalk formula's sheaf clause. Torsion and qcqs are exactly its hypotheses. The support definition identifies the remaining points to test. No proper or smooth base-change theorem is being used.

Step 2 uses the geometric node's exact L, models, maps to U, index smallness and inverse-limit conclusion. Affine permanence supplies affineness of X_U and base changes. The generator argument proves finite type over L; tensor products commute with the ring colimit by the universal property written in the step. No descent of the original sheaf is assumed: every F_i is its actual pullback from X.

Step 3 takes algebraicity precisely from the geometric node statement and proves its preservation for T_i explicitly by tensoring residue fields. The inverse-image stalk node states the stalk equality for arbitrary scheme morphisms and etale sheaves; it supplies the support inclusion and, together with the torsion characterization's stalk clause, proves torsion of F_i. No claim that geometric stalks of arbitrary pro-etale sheaves are conservative occurs.

Step 4 uses exactly the two clauses of the new tower leaf. Additivity and the zero algebraic term give the displayed inequality. For b>a it applies the existing conservativity node to 0 -> F_i. For b<=a, all hypotheses of the absolute support lemma hold: L is separably closed, T_i affine finite type, F_i torsion, c=a-b nonnegative and the support inequality established. The calculation q>a-b is the inequality fixed in step 1. Thus the imported conclusion is obtained by a real argument using separate geometry, absolute vanishing and continuity, not moved into one new node.

Step 5 uses the arbitrary-small-cofiltered continuity node, whose statement includes systems of sheaves with pullback transitions and their colimit on the limit. The system here has canonical compatible pullback isomorphisms, its limit sheaf is F_T, and all schemes are affine qcqs with affine transitions. Hence its cohomology cocone applies exactly. The support definition then gives the final assertion. citations.json contains a verbatim statement quote for each step/node pair; I opened and read each cited statement before choosing it.

Edge cases checked: empty X gives zero stalks; at q=0 the computation still uses H^0 with no positivity assumption; a=0 and b>0 force F_i=0; q>a forces vanishing at all points since b>=0; at a closed point b=0 the model lemma still supplies a separably closed L/K of transcendence degree zero, without asking that K itself be perfect or separably closed. For the new geometry lemma at a generic point, R is a separable algebraic closure of the function field and its L-models can have only algebraic residues; for a closed point, etale models after the algebraic coefficient extension have the required residue control. The tower identity also covers algebraic and infinite extensions (cardinals, with lifts). For the new vanishing lemma c=0 recovers closed-point support acyclicity, and the zero sheaf is vacuous. No invertibility of torsion orders was introduced.

Generic off-unit uses are listed in split_report.tool_uses. No files in the live project or Lean checkouts were edited, no compiler was run, and no agents were started. The required dry run is the only packaging operation; this worker does not push.

Preflight repair: replaced a nonexistent limit-definition citation by the explicit universal-cone definition and the existing filtered-category definition. Added the required numeric line field 546 to the Mathlib match; the second clause remains identified at Transcendental.lean:89 in how.

## Second reading by NU

Step 1 checked against Stacks 0F0X and the cited affine permanence, strict-henselization stalk, and support statements; hypotheses and stalk reduction agree.
Step 2 checked against the strict-local model statement and affine permanence; tensor-colimit, finite-type, affine-transition, and inverse-limit claims use exactly those statements.
Step 3 checked against the model, pullback-stalk, and torsion-characterization statements; the residue-field tensor argument and support/torsion transfer are explicit. It is non-elementary and is marked false accordingly.
Step 4 checked against the tower Mathlib leaf, geometric-stalk conservativity, and absolute vanishing node; both tower applications and the negative-bound case are justified.
Step 5 checked against cofiltered etale continuity and support definition; transition sheaves, affine qcqs hypotheses, and the final stalk criterion match.
The item statement was checked hypothesis by hypothesis against Stacks Tag 0F0X, including arbitrary fields, torsion sheaves, affine morphisms, and all q and a edge cases.
The support-vanishing node was checked against Tag 0F0W: separably closed base, affine finite type scheme, torsion sheaf, support bound, and all r are present.
The strict-local models node was checked against Tags 0F0U and 0F0X: coefficient-field transcendence degree, affine finite-type cofiltered models, universal limit, and algebraic residue extensions are all stated self-containedly.
The transcendence-degree node was checked against Tag 030H and Mathlib `trdeg_add_eq`/`trdeg_eq_zero_iff`; its Mathlib leaf records declaration, files, lines, and searches.
I tested zero and empty schemes, q=0, q>a, a=0, closed and generic points, b>a, c=0, algebraic extensions, and infinite towers. No statement change was needed.
Changes: marked steps 2 and 3 non-elementary because their tensor/residue/support arguments use substantive deductions and multiple cited lemmas; retained all citations and statements. No Lean or compiler tools were run.
