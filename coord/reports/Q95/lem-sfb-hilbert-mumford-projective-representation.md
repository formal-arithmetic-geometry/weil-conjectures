# Stage 1 delivery: lem-sfb-hilbert-mumford-projective-representation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-hilbert-mumford-projective-representation.json: item, split; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-projective-stability-affine-orbit-proper.json: statement-only supporting theorem, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-properness-formal-arc-test.json: statement-only supporting theorem, unsplit; no Mathlib match.
- citations.json: a verbatim quotation for every citation in all five proof steps.

## Attachments

None. Searches in lean/WeilConjectures for the item's blueprint tag, Hilbert--Mumford, HilbertMumford, GIT stability, affine cone, and proper orbit maps found no declaration of the criterion or either new theorem. PerfectAffineConeModel concerns a cone of complexes, not geometric invariant theory. General affine-cone mentions and topological orbit maps do not cover this item. No compiler or Lake command was run.

## Wanted literature

WANTED: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, third edition, Chapter 2 Section 1, Proposition 2.2 and proof of Theorem 2.1, for the item and both new nodes. The local book is absent. The online PDF found through search contained only the cover/contents, and attempts to read the full book were blocked. I did not treat that as reading the proof.

WANTED: Morrison, GIT Constructions of Moduli Spaces of Stable Curves and Maps, arXiv:0810.2340, Section 2.2, Proposition 1 and its proof, printed pp.6--7, as a local PDF. The online primary text was read. It cites the Hilbert--Mumford theorem before its Pluecker-coordinate specialization; it is not a proof of the general criterion. The item is therefore explicitly proof_origin.by=agent, rather than attributing my reconstruction to that proposition.

## Problems found and scope

The item has a correct sign with the lines convention: the O(1) numerical weight is the negative of the minimum weight of a vector lift. I did not change its statement or characteristic and nilpotent qualifications. Its inline definition of SL is sufficient, but the proof also cites the existing explicit special-linear group-scheme definition.

The inherited blueprint.from.node is null, as tools/blueprint_refs.py ancestor prints; I retained this rather than inventing an ancestor. The exact inherited alteration/Gieseker supporting place and via chain are retained. I read the current latest sk-thm-sf-ctf-stability unit and its direct-images proof (3). That current proof cites constructible direct-image preservation and compactification. This delivery only refines the already seeded supporting GIT prerequisite on its existing branch; it changes neither the unit nor the chapter. This item is not the unit's key node, so no realized record was written.

No source error or statement dispute was found. There were no existing sandbox nodes or reports to preserve at the start; logged searches from this session have been reused after the provider interruptions. No delivery was started before this report.

## Not duplicates

lem-sfb-projective-stability-affine-orbit-proper vs lem-sfb-hilbert-mumford-projective-representation: the new node relates projective stability to properness of an affine orbit morphism, with no cocharacter or weight criterion; the item proves the cocharacter test by the independent formal-arc and Smith calculations.

lem-sfb-projective-stability-affine-orbit-proper vs lem-sfb-hilbert-monomial-numerical-criterion: the existing node specializes to Hilbert points, determinant coordinates and monomial weights; the new node contains no monomial statement and provides the geometric cone reduction before numerical arguments.

lem-sfb-projective-stability-affine-orbit-proper vs lem-sfb-projective-pgl-stable-quotient: the existing node constructs a projective quotient for a closed stable locus under PGL. It does not characterize individual SL orbits in affine vector space as proper morphisms.

lem-sfb-projective-stability-affine-orbit-proper vs lem-sfb-git-orbit-closure-dimension: orbit-dimension and the unique closed orbit in a semistable PGL orbit closure do not supply this vector/projective comparison or properness.

lem-sfb-projective-stability-affine-orbit-proper vs lem-sfb-smooth-group-orbit-geometry: smoothness, local closedness and dimension of orbits do not compare the projective invariant-section definition with affine orbit-map properness.

lem-sfb-affine-properness-formal-arc-test vs lem-sfb-noetherian-dvr-properness: the existing node quantifies over every DVR, potentially with large residue field. The new node proves that, for affine finite-type schemes over algebraically closed k, the single test ring k[[t]] suffices; that is not a one-line specialization of the existing equivalence.

lem-sfb-affine-properness-formal-arc-test vs lem-sfb-noetherian-image-boundary-dvr: the existing boundary lemma gives an unspecified DVR whose residue field need not be k, only at points outside the image. A nonproper orbit map can have closed image (the trivial representation is an example), so this is insufficient for the fixed-field nonextension test. The graph compactification detects such nonproperness.

lem-sfb-affine-properness-formal-arc-test vs lem-sfb-dvr-matrix-smith-powers: one is geometric properness testing, the other diagonalizes a matrix over an arbitrary DVR. The latter is reused, not duplicated.

DAG-wide statement/title searches for affine cone, proper orbit map, formal arcs and curve detection of properness found no equivalent node. Whole-blueprint searches included Hilbert, Hilbert Mumford, proper orbit, affine cone, cone orbit, formal arc, arc, Smith, stability and valuative. None stated either new node. Mathlib leanfinder, leansearch, loogle and grep searches and their exact returned summaries are in searches.jsonl and in the corresponding node records. Both nodes were tried under a second phrasing. The general valuative-criterion hits do not reduce to this fixed-field formal-arc test. The proper orbit grep hit in Topology/Algebra/ProperAction/Basic.lean:291 was opened: it concerns proper topological actions and does not state the algebraic GIT theorem.

## Supporting arguments retained for the new nodes

The new nodes carry statements only. The following explains why they are suitable smaller inputs, and preserves the argument a future worker should split.

For projective-stability-affine-orbit-proper, the two standard cone facts are: projective semistability is exclusion of the cone vertex from the affine orbit closure, and projective polystability corresponds to closedness of the nonzero vector orbit. These use reductive invariant separation (geometric reductivity in positive characteristic), and the correspondence between homogeneous cone functions and sections of powers of O(1). For a closed subscheme Y one can use its full section ring, or sufficiently high degrees of its homogeneous coordinate ring; no projective-normality assumption is appropriate. The nonreduced case requires the invariant power-lifting statement for nilpotent thickenings, rather than assuming exactness of invariants. These are substantive inputs still to be split in that node, not unrecorded assertions used by the item independently.

Once an invariant homogeneous function F of degree d is nonzero on v, the scalar values of elements of the projective stabilizer lie in mu_d: F(cv)=c^d F(v)=F(v). Thus the vector and line stabilizers have the same dimension, without asserting that mu_d is reduced. A closed vector orbit with zero-dimensional stabilizer has a finite (hence proper) orbit morphism: it is the homogeneous-space quotient with finite stabilizer, including the inseparable case. Conversely a proper vector orbit map has closed image and finite affine stabilizer. Combining these with the cone facts gives exactly the new statement. This route has no weights and cannot prove the item by itself.

For affine-properness-formal-arc-test, embed X as a closed subscheme of affine space over k and close its graph in P^N_k x Z. Its graph is open in this closure and the closure is proper over Z. If f is not proper, the graph has a nonempty boundary. Choose a closed boundary point; it is k-rational because k is algebraically closed and the closure is of finite type. An integral curve through that point with generic point in the graph is obtained by curve selection. Normalize this curve and choose a point over the boundary point. The resulting smooth curve local ring has residue field k and completion k[[t]]. Its generic point maps to X and its closed point lies outside the graph, giving the required nonextending formal arc. An extension to X would give a second extension into the separated graph closure, forcing the boundary point into the graph. Conversely a proper f has a unique lift for each such DVR diagram. For nonreduced schemes the boundary construction can be made on the reduction and then mapped into the original graph; a proper map already satisfies the full valuative criterion. The necessary graph, curve-selection, normalization and completed-local-ring facts belong to the future split of this node; the present item only uses its stated equivalence.

## Review by Q95

I read the standing brief, stage-1 rules, GOAL, the three SETUP levels, and delivery-errors B through E. I read the item's whole statement, the chapter and unit records, and the latest blueprint direct-images proof. For the item I read Morrison's online primary text and checked that its reference is the general GIT criterion; I did not claim it supplies the underlying proof. MFK is absent locally, so the proof and the formulations of both supporting nodes are marked as agent reconstructions and explicitly WANTED. I also read the local Stacks 0208 statement and proof (limits.tex, lemma-Noetherian-dvr-valuative-proper), which confirms the all-DVR criterion but does not claim the stronger fixed-field arc reduction. Local Milne Aside 12.58 explicitly warns that reductive is not linearly reductive in positive characteristic; no averaging argument or exactness of reductive invariants is used here.

In step 1 I opened def-sc-general-linear-group and used its actual determinant-one affine quotient, not a generic group-scheme definition for representability. Both finite-type affineness hypotheses of the arc test hold: G has the finitely many matrix coordinates and one equation, and affine vector space has finitely many polynomial coordinates. Any k-morphism between affine finite-type k-schemes is of finite type because generators over k are also generators over the target coordinate algebra. The cone node's statement includes precisely invariant-section semistability, orbit closure inside that locus, and dimension zero for the scheme-theoretic stabilizer. Its properness equivalence is exactly what this step takes, including nonreduced Y and arbitrary characteristic.

In step 2 I opened the formal-power-series and DVR definition statements. The explicit recursive inverse and least-order ideal argument establish the DVR hypothesis, including nonzero maximal ideal and field of fractions, without needing an uncited completeness theorem. This is an elementary calculation, not a new theorem node.

In step 3 I read the existing rectangular DVR Smith node. It gives invertible changes of basis and uniformizer powers, and allows the square full-rank case used here. Clearing denominators makes the input a matrix over A. I checked that determinant order forces the sum of the Laurent exponents to be zero, and the displayed diagonal unit matrix adjusts both outer determinants to one while commuting with the middle diagonal. The original GL Smith form alone would not give an SL factorization; that missing adjustment is now explicit. No new Smith node is needed.

In step 4 I reread the arc node's equivalence and the entire weight-basis statement. Failure of properness gives an actual K-point of G with no A-extension and integral vector image; it does not merely give a point of the orbit over an unspecified finite extension. The existing G_m weight node works over every field and gives a basis whose formula is valid over every commutative k-algebra. Consequently it applies to A and K, makes P' and Q' act integrally, and makes each negative-weight coordinate divisible by the required positive power of t. The constant term q of Q' lies in SL(k), w(0) is nonzero, and conjugation by q^-1 gives the weight inequality for the original v. This verifies the potentially delicate constant-term/conjugation step, rather than using an undefined word such as 'transport'.

In step 5 the same two cited equivalences apply. A nonnegative minimum gives an integral vector arc, so properness forces the matrix cocharacter itself to extend. I checked the defining representation on E, rather than V: V may be trivial or nonfaithful. Its determinant-one weights sum to zero, and a nontrivial homomorphism has a negative defining weight. This precludes integral matrix entries. That argument works also for inseparable cocharacters in characteristic p; zero differential does not imply a trivial group-scheme homomorphism.

Small cases checked: a trivial representation has nu=0 for every cocharacter and is not stable (its line stabilizer has dimension dim SL); its orbit map is constant and nonproper, so both reductions agree. The standard SL2 representation on k^2 has no stable projective point, agreeing with a cocharacter having positive weight on any chosen vector after conjugation. For SL2 acting on pairs of standard vectors, the invertible pair has closed affine orbit det=c and finite line stabilizer mu_2, so its projective point is stable; in characteristic 2 mu_2 is nonreduced, which is allowed and detected by dimension, not by tangent-space dimension. For the arc lemma, the open immersion G_m into A^1 fails on x=t, while the constant map from positive-dimensional affine space fails on x=t^-1 even though its image is closed. Empty schemes, finite morphisms and nilpotent thickenings introduce no counterexample. These also show why the boundary-of-image DVR node does not suffice.

Every non-elementary fact used by the item is cited as a node, all quoted parts were copied verbatim from their statements, and proof_deps is exactly the union of uses. The off-unit Smith theorem is declared as a generic tool in split_report.tool_uses. Neither new node merely restates the numerical conclusion, neither is elementary from the existing nodes, and neither was given proof steps. No proof step exceeds 2000 characters. I retained the statement's full hypotheses and conclusions and found no cycle in the intended dependency directions. No SGA source is used. All writes were confined to the sandbox.

## Unfinished work

No part of this one-level split is intentionally left incomplete. The two supporting statements are queued unsplit as required. The maintainer's independent mathematical review and later splitting of those supporting inputs remain the next project stages; no claim of a completed Lean proof is made.
