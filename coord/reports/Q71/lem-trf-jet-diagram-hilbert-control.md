# Q71: lem-trf-jet-diagram-hilbert-control

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-jet-diagram-hilbert-control.json`: statement, split in fourteen steps; no Mathlib theorem states the whole package.
- `dag/nodes/sec-trace-formula/lem-trf-dickson-exponent-sequences.json`: statement, Mathlib leaf. `Pi.wellQuasiOrderedLE`, `wellQuasiOrdered_le`, and `WellQuasiOrderedLE.finite_of_isAntichain` specialize to `Fin d → Nat`; file `Mathlib/Order/WellQuasiOrder.lean`, lines 215, 130, 161 respectively.
- `dag/nodes/sec-trace-formula/lem-trf-smooth-rational-point-completion.json`: statement, unsplit; no Mathlib match after two semantic phrasings and the name/source searches. The adic-completion smoothness hits prove lifting/sections, not this completion isomorphism.
- `citations.json`: twenty-one step citations with verbatim statement extracts. `searches.jsonl` retains the actual service queries/results. `report.md`: this report.

## Attachments

None. Searched the live project Lean source by the item's blueprint tag, principal parts, initial diagrams, Taylor, Hilbert--Samuel, smooth local completions and Dickson. No project declaration gives every clause without sorry. Unrelated principal-parts declarations for adelic/Tate objects do not state this item. Mathlib is used as a leaf, not claimed as a project attachment.

## Literature wanted

WANTED: Bierstone--Milman, Canonical desingularization in characteristic zero by blowing up the maximum strata of a local invariant, Invent. Math. 128 (1997), 207--302, Theorem 3.17, Remark 3.18, Corollaries 3.19--3.20, Remarks 9.1 and Lemma 9.3, for lem-trf-jet-diagram-hilbert-control. Read the primary published full PDF online at https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf . The short arXiv version does not contain section 9. No document was downloaded into the repository.

WANTED: Bierstone--Milman--Temkin, arXiv:0905.3580, sections 6.1 and 6.5 (extended Hilbert--Samuel function and arbitrary-point diagrams), for lem-trf-jet-diagram-hilbert-control. Read the primary PDF online at https://arxiv.org/pdf/0905.3580 .

The available ILO document, VIII 2.3.11--2.3.13, printed pp.93--94, points to strong embedded resolution and its invariant; it does not itself prove the entire Taylor/diagram package. Accordingly the split has `proof_origin.by = agent`. The arbitrary-point diagonal calculation, finite-prefix semicontinuity argument, and separate lexicographic Hilbert-function argument are written out rather than attributed verbatim to ILO. No SGA source is used.

## Corrections and route

The input had no complete proof. I made explicit that the Taylor point belongs to X (so its residue evaluation annihilates the defining ideal), and specified the division support partition needed for uniqueness. These clarify the intended objects and unique-division clause; they do not alter any numerical formula or impose closedness/rationality on x. No target statement or definition is changed. There is no statement dispute left unresolved.

For a nonclosed x, completing O_{X,x} alone would give h_x, not the principal-parts fibre. The proof instead uses the local ring at the evaluation point of kappa(x) tensor_k A. Its map from A_x is essentially smooth with equal residue fields and cotangent rank trdeg_k kappa(x). This supplies exactly the missing iterated-sum correction. The existing finite-type-Q tangent-cone lemma cannot supply this for an arbitrary characteristic-zero field k; the new auxiliary lemma has arbitrary Noetherian base and specifies the full completion isomorphism.

The blueprint ancestry is the already present historical local-term-locality/alteration branch through embedded resolution and Hilbert--Samuel presentations. I preserved that ancestry and the unit/chapter; I do not replace the current unit's upper route or claim to realize its whole statement. All off-unit nonleaf generic tools used here are declared in split_report.tool_uses.

## What remains

The rational smooth completion lemma is deliberately statement-only, as required for a one-level split; it is the one new unsplit obligation. Its source is checked and its proof route is described below. No part of the item's argument is deferred to an unstated claim. There is one Mathlib leaf among two new nodes. No Lean file was changed and no compiler or local DAG checker was run.

## Review by Q71

I read ILO VIII 2.3.11--13, the published BM formal-division theorem and its order estimate (pp.238--239), the Taylor-matrix discussion and diagram-variation proof (pp.275--277), and BMT sections 6.1/6.5. The source distinguishes the order on diagrams from the lexicographic order on Hilbert functions. I therefore prove the latter separately; I do not infer it from equality of those orders. I also checked delivery-errors B--E against the completed JSON and opened every cited node's statement. The quotes in citations.json are copied from those statements, not descriptions of what I wanted them to say.

Steps 1--2 explicitly give the finite diagonal generators and the fibre algebra. The finite-type Noetherian theorem is used with a field as base; localization is justified by contracting ideals. The quotient by q^(n+1) has nilpotent evaluation kernel, so inverting elements outside q changes nothing. There are no points to consider for the zero algebra.

Step 3 uses the characteristic-zero separability statement, the separable-extension smooth-subalgebra statement, smooth base change, the two differential formulas, and the separably-generated differential-dimension statement. Each node actually states its indicated operation, rather than merely defining smoothness or differentials. The residue extension is finitely generated, since A is finite type, and hence has finite transcendence degree. Passing from L tensor A to L tensor A_x and then its evaluation localization inverts elements already invertible there. Thus the cited smooth-subalgebra theorem applies, the local map has residue identity L, and its relative cotangent space really is Omega_{L/k}. I corrected an inaccurate source tag for differential dimension to the tags actually carried by that node (031W and 00TV).

Step 4 invokes the new completion/graded theorem with exactly those hypotheses. The length-additivity node states additivity in short exact sequences of finite-length modules. Here each filtration quotient is a finite-dimensional residue vector space, so a vector-space flag gives a finite composition series. This both verifies the finite-length hypothesis and identifies length with dimension before summing. Polynomial monomials then give the iterated-sum formula directly, including rank zero.

Step 5 uses the etale definition for flatness and unramifiedness and the unique-lifting theorem for the actual infinitesimal lifting claim. I expanded the previously terse comparison: maps in both directions between each truncated diagonal and the truncated polynomial algebra are specified, and their compositions are checked by generators and unique lifting. All lifting stages have square-zero kernel, and the residue point is an L-point after scalar extension. Quotienting by I gives precisely the principal-parts fibre of B/I. No coefficient field in the completed local ring of X is presumed.

Step 6 uses only the two actual Dickson conclusions: a coordinatewise antichain is finite, and the minimal-elements argument in a finite box makes their translates cover the diagram. The Mathlib source was read, including the definition of WellQuasiOrdered, the finite-product instance, and the finite-antichain theorem. This new leaf is the general sequence/antichain theorem, not a new restatement of the item's finite-vertex clause. The case d=0 is included.

Steps 7--8 prove supported formal division, rather than citing a node which restates division. The power-series definition supplies coefficient families and finite convolution. The recursion visits finitely many monomials in each bounded degree; subtraction changes only later monomials. Hence its limits and order estimates hold coefficientwise. Leading exponents of distinct supported summands lie in disjoint pieces, proving uniqueness. For a dividend in K its remainder is again in K, and a nonzero remainder would have an initial exponent both inside and outside the diagram. The order estimate proves independence of the truncated standard monomials. This is the substantive argument of the item, not an unexplained appeal to a definition.

Step 9 uses coherence for local finite generators and the exact coordinate-derivative/Taylor sentence of the existing implicit-calculus node. The latter is used with no transverse variables or implicit equations; none of its stronger transverse conclusions is taken. Characteristic zero allows factorial denominators in Taylor coefficients. Finite matrices for each monomial prefix have regular entries, and nonvanishing minors prove openness. I checked that a degree-lex tail is closed under monomial multiplication. The finite prefix through the largest vertex of a fixed comparison diagram decides its sublevel: equality on that prefix forces containment of that comparison diagram. Bounded integer vectors make the lex sublevel a finite union of coordinatewise sublevels, hence open.

Step 10 uses Dickson for the limiting upward-closed set in a hypothetical decreasing diagram sequence. Stabilization of each successive membership bit follows by induction on the degree-lex exponent; finite vertices then contradict the first-difference order. Step 11 uses exactly the finite-type Noetherian theorem and the affine-Noetherian-underlying-space theorem, whose statement really concludes that the spectrum is a Noetherian space. Infinitely many attained values would give strictly descending closed superlevel sets; this is prohibited by Noetherianity.

Step 12 proves Hilbert-function DCC separately. Natural-number values stabilize degree by degree, and the finite set of membership patterns in each degree ball permits nested infinite subsequences. The resulting upward-closed limit has finitely many vertices by Dickson. Containment in late subsequence members gives the pointwise inequality opposite to strict lexicographic descent. This avoids confusing diagram order with the counting-function order.

Step 13 checks etale invariance by the same actual unique-lifting statement used in Step 5. The lift is taken on a nilpotent diagonal thickening over A'; two inverse maps are checked by uniqueness at square-zero stages. Residue field extension preserves every finite matrix rank, so the Taylor truncations and diagrams agree in the fixed coordinate chart. Step 14 expands in the free variables and counts complement monomials, which directly gives each summation operation.

For the new completion lemma I read Stacks morphisms.tex, lemma-smooth-etale-over-affine-space (054L, lines 8543--8558), and more-algebra.tex, lemma-flat-unramified (0AGX, lines 10764--10787). Neither tag is falsely labelled as the whole new statement. Here is the proof route for the future splitter: represent S locally by a smooth finite-type R-algebra, use 054L to choose an etale R-polynomial chart, and lift each coordinate residue from L to R to centre it. The chart then localizes to R[Z]_(m,Z) → S with identical residue fields; etaleness gives flatness and generation of the target maximal ideal by the source one. Tag 0AGX identifies their completions. Comparing quotients by (m,Z)^q identifies the source completion with R-hat[[Z]], and the same total-degree coefficient comparison gives the asserted graded polynomial algebra. The number of coordinates is s by the etale cotangent computation. This is a genuine reusable local-completion theorem, not the item's principal-parts dimension formula with notation changed.

Small-case checks: at the generic point of A=k[z], h_x(n)=1 and t_x=1, so the formula gives n+1, the actual diagonal fibre dimension; at a closed point h_x(n)=n+1 and t_x=0 gives the same answer. For a finite separable field algebra at a point the answer is 1. For d=0 the only diagrams are empty or all of N^0; division and counts are 1 or 0 as appropriate. K=0 and K=(1), n=0, r=0, and the empty X cause no exception. The ideal (T_1^2,T_1T_2,T_2^3) has standard monomials 1,T_1,T_2,T_2^2, matching the division count in every truncation. For the new completion lemma, R=Z_(p), S=R[z]_(p,z) gives Z_p[[z]], showing mixed characteristic is allowed; rank zero gives the equal-residue etale completion theorem. The ramified map k[[t]]→k[[u]], t↦u^2 fails smoothness and is excluded. Unequal residue fields are also explicitly excluded from that lemma.

No proof step exceeds 2000 characters after separating the two DCC arguments and combining each finite-prefix argument with its supporting construction. I checked that no step hides a comparison isomorphism, smallness hypothesis, or uncited flatness/exactness theorem. The new nodes were searched against the whole DAG, whole blueprint, project Lean, and Mathlib before creation. Repeated logged queries are preserved, and the single-file grep's malformed filename output is identified as such; the directory grep supplies the verified file and lines.

## Not duplicates

lem-trf-smooth-rational-point-completion vs def-pur-dnc-section-family: defines a section deformation and its derived family object, not the rational-point completion theorem.

lem-trf-smooth-rational-point-completion vs det-sp-reduction-exceptional: is coefficient extension for exceptional inverse images, not completion of local rings.

lem-trf-smooth-rational-point-completion vs lem-pc-dense-separable-points: asserts density of closed points with separable residue fields, not completion structure at an equal-residue smooth local map.

lem-trf-smooth-rational-point-completion vs lem-pur-dnc-section-geometry: states fibres, charts and base change of a deformation space, not the power series structure of smooth local completions.

lem-trf-smooth-rational-point-completion vs lem-pur-noetherian-etale-section-specialization: compares dualizing complexes under deformation of a closed section; it does not state the local-ring completion theorem.

lem-trf-smooth-rational-point-completion vs lem-pur-regular-immersion-linearization: linearizes a regular immersion in smooth schemes over a perfect field, not an arbitrary-base essentially smooth local completion.

lem-trf-smooth-rational-point-completion vs lem-pur-smooth-closed-coordinate-lift: lifts a chart from a regular closed smooth subscheme, not an essentially smooth local map with identical residue fields.

lem-trf-smooth-rational-point-completion vs lem-sc-regular-ideal-conormal-coordinates: describes a regular ideal and its conormal coordinate monomials, not a completion of an arbitrary essentially smooth local ring map.

lem-trf-smooth-rational-point-completion vs lem-sc-smooth-diagonal-regular-immersion: proves regularity of a diagonal ideal, not the maximal-ideal completion presentation.

lem-trf-smooth-rational-point-completion vs lem-sc-smooth-section-affine-coordinates: has an actual closed section and its regular coordinate ideal, not a rational residue point and completion over a general local base.

lem-trf-smooth-rational-point-completion vs lem-sc-smooth-section-ring-coordinates: assumes an actual smooth section and constructs affine coordinate charts generating its kernel; a rational residue point of a local map need not lift to such a section, and no completed local ring formula is stated.

lem-trf-smooth-rational-point-completion vs lem-sc-standard-smooth-local-relative-dimension: provides standard-smooth affine charts of the relative dimension; no completion or maximal-ideal associated graded algebra is asserted.

lem-trf-smooth-rational-point-completion vs lem-sfb-nodal-log-dualizing-pullback: concerns a morphism of logarithmic dualizing line bundles for nodal families, not complete local algebra.

lem-trf-smooth-rational-point-completion vs lem-sp-smooth-admissible-coordinate-cover: constructs finite charts for separated finite-type schemes in characteristic p, not complete local algebras over arbitrary Noetherian rings.

lem-trf-smooth-rational-point-completion vs lem-trf-curve-centred-valuation-dvr: identifies a valuation with a curve DVR and gives an etale coordinate; it does not give the arbitrary-base completion and graded isomorphisms.

lem-trf-smooth-rational-point-completion vs lem-trf-etale-completed-local-ring-iso: assumes an algebraically closed field and an etale map at a rational point, so covers a special rank-zero field case only.

lem-trf-smooth-rational-point-completion vs lem-trf-finite-ring-section-deformation: concerns normalized dualizing-complex comparison along a smooth section deformation, not the local-ring power series theorem.

lem-trf-smooth-rational-point-completion vs lem-trf-isomorphism-completion-approximation: starts with a completion isomorphism and approximates it by etale neighbourhoods under G-ring assumptions; it does not produce the smooth power series completion isomorphism.

lem-trf-smooth-rational-point-completion vs lem-trf-nodal-point-etale-locality: is invariance of a specified nodal curve singularity over an algebraically closed field, not a completion formula for positive-rank smooth maps.

lem-trf-smooth-rational-point-completion vs lem-trf-section-rees-noetherian-geometry: constructs Rees deformation geometry of a smooth closed section, not an arbitrary smooth local completion.

lem-trf-smooth-rational-point-completion vs lem-trf-semistable-marked-base-change: concerns base change and stability of marked curves, not completion of an essentially smooth local homomorphism.

lem-trf-smooth-rational-point-completion vs lem-trf-smooth-local-tangent-cone-extension: assumes local Q-algebras essentially of finite type over Q and states a tangent-cone extension (also allowing residue extensions); the new theorem permits arbitrary Noetherian bases, requires identical residue fields, and constructs a full complete-local-algebra isomorphism. The existing finite-type-Q restriction cannot be met when the item uses an arbitrary characteristic-zero field k.

lem-trf-smooth-rational-point-completion vs lem-trf-smooth-section-centred-coordinates: computes the graded algebra of a section ideal with an actual section; the new node concerns maximal ideals and requires only a rational residue point, with a full completion isomorphism.

lem-trf-smooth-rational-point-completion vs lem-trf-valued-curve-etale-parameter: constructs a rational parameter for a valued one-dimensional function field, not a power series presentation over an arbitrary completed Noetherian base.

lem-trf-smooth-rational-point-completion vs lem-weil-pbc-flat-local-completion-iso: requires mS=n and gives a completion isomorphism without variables; for positive smooth rank mS is not n and this node applies only after choosing and adjoining polynomial coordinates.

lem-trf-smooth-rational-point-completion vs lem-weil-pbc-flat-local-completion-iso-bijective: assumes maximal-ideal equality for a flat map and proves bijectivity on completions; the new positive-rank smooth case has mS strictly smaller than n in general and produces extra variables.

lem-trf-smooth-rational-point-completion vs lem-weil-pbc-flat-module-completion-flat: asserts flatness of a completed module, not a power series isomorphism of completed rings.

lem-trf-smooth-rational-point-completion vs lem-weil-pbc-g-ring-completion-regular: asserts regularity of a G-ring completion map, not that a given smooth local target has a power series presentation over the completed source.

lem-trf-smooth-rational-point-completion vs lem-weil-pbc-henselization-pair-g-ring: is permanence of the G-ring property under pair henselization, not structure of a smooth rational local completion.

lem-trf-smooth-rational-point-completion vs prop-asd-smooth-base-change: is a derived exceptional base-change isomorphism, not an isomorphism of completed local rings.

lem-trf-smooth-rational-point-completion vs sbc-thm-etale-local-normal-form: provides an etale affine-space chart, not the isomorphism of complete local algebras or the maximal-ideal graded formula.

lem-trf-smooth-rational-point-completion vs sk-thm-smooth-base-change: is an etale sheaf cohomology base-change theorem, not a statement about smooth local ring completions.

No existing DAG/blueprint node states the general finite-product sequence/antichain form of Dickson used by the new Mathlib leaf. Its finite-vertex consequence is proved in the item itself, so no duplicate finite-diagram-generation node is created.

## Dry-run repair

The first delivery dry run rejected two leaf metadata omissions: its statement had no referenced notion and its Mathlib match lacked the required numeric line. I opened and reused def-sfb-finite-infinite-set for the actual finiteness predicate, and reread the pinned Mathlib lines 35--48, 125--134, 156--165 and 204--218 before recording line 215. The existing verbatim citations remain valid substrings. No mathematical statement or proof argument changed in this repair.

## Repair of the landing return (2026-10-22)

The single return point was the stale citation of lem-trf-implicit-taylor-coordinate-calculus. I compared the complete returned item at ed893f29273163d3aed778173b73f91b094bbf17 (parent e6e46ce3698f117f27985571dc76273501c98d9a) with this sandbox: they agree in every field, so the reader's reviewed split is retained. I compared all statement and proof dependencies at that returned head with server main d0e9f54d9d577df07d05d3e17ab03ff561f665d9. Of the existing dependencies, only lem-trf-implicit-taylor-coordinate-calculus changed, including its statement. The two new nodes remain new. The initial required dry run on the retained files passed at 874e9def7c1; it was diagnostic, before the mathematical repair below. The delivery tool rebases the repaired owned fields onto current main rather than reusing the returned commit. The comparison data are retained in sandbox repair-comparison.json.

I reread the entire current implicit-coordinate statement. Its previous clauses are retained verbatim, and it now specifies that B is a smooth k-scheme, that the coordinates give an etale morphism to affine space, and that the Taylor map passes through completion of B_L at the L-rational point b_L for L=kappa(b). This is exactly the scalar-extended diagonal construction of Step 5, not completion of the unextended stalk at a nonclosed point. With r=0, N=U and w=u, its implicit-equation hypotheses are empty, the empty Jacobian has determinant 1, and its derivation/Taylor clause applies at every x. The two maps send each coordinate to u_i(x)+T_i and agree modulo each power by Step 5's unique-lifting argument. Step 9 now writes out this identification and the consequence [T^alpha]tau_x(f)=D^alpha f(x)/alpha!, so the finite matrix entries are the values of actual regular functions. No transverse-variable, faithful-flatness or ideal-descent clause is needed. The expanded verbatim quote in citations.json includes both the derivative clause and the new centered-map definition.

I also reread the other current cited statements and compared them with the returned head: they are unchanged. The field-extension and differential statements still apply to the finitely generated separable extension kappa(x)/k in Step 3; the unique-lifting statement still supplies exactly the square-zero lifts used in Steps 5 and 13; the Noetherian and length statements retain precisely the hypotheses checked in Steps 2, 4 and 11. I reread the new completion statement against Stacks 054L (morphisms.tex, lemma-smooth-etale-over-affine-space) and 0AGX (more-algebra.tex, lemma-flat-unramified), and retained its equal-residue and Noetherian hypotheses. The existing report's source readings, searches, new nodes and other thirteen proof steps are retained. No new node or changed mathematical search question results from the repair, so the recorded searches were read and reused.

For the changed step, the generic point of k[t] gives L=k(t), tau(t)=t+T and tau(t^2)=t^2+2tT+T^2, confirming the new interpretation and the coefficient formula without requiring a rational or closed original point. At a rational point a, tau(t)=a+T gives the ordinary Taylor coefficients. With d=0 the empty multiindex gives just evaluation. I checked the repaired files against delivery-errors B--E: the only new argument is the displayed one-line consequence of the cited derivation statement and the existing unique lifts, not a hidden comparison lemma; every node cited by every step still has a verbatim quote. All fourteen steps remain shorter than 2000 characters. The item's statement, two new statements, numerical formulas and proof route are retained. This is a citation revalidation with an explicit proof adjustment, not an unchanged re-push.
