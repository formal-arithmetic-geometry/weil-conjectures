# Q36: lem-sfb-strict-dominant-flag-line-ample

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-strict-dominant-flag-line-ample.json`: statement, split; preserved the statement and all statement dependencies. Existing searches retained; fresh recorded searches give no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-fundamental-flag-boundary-sections.json`: new statement-only node, unsplit, no Mathlib match. It asserts fundamental sections and their individual boundary supports, without asserting ampleness.
- `citations.json`: ten exact statement excerpts for all ten step citations. The independent citation check is also performed by deliver.py.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the blueprint id, strict dominance, flag ampleness, Borel quotients and fundamental boundary sections. No project declaration stating the item or the new node was found. Lie/ordinary representation declarations do not give the group-scheme flag result.

## WANTED

WANTED: Birger Iversen, The geometry of algebraic groups, Advances in Mathematics 20 (1976), 57--85, Theorem 5.3, for `lem-sfb-fundamental-flag-boundary-sections` (also cited by Milne Remark 22.49).

WANTED: Michel Brion and Shrawan Kumar, Frobenius Splitting Methods in Geometry and Representation Theory (2005), section 2.1, printed pp.61--64, and Exercises 2.2.E(2)--(3), printed pp.70--71, for `lem-sfb-fundamental-flag-boundary-sections`. Primary author-hosted PDF read online at https://www-fourier.univ-grenoble-alpes.fr/~mbrion/fbook.pdf; no download or repository write was made. Exercise heading explicitly allows arbitrary characteristic, including zero. The introduction's standing characteristic-p assumption is not used to restrict the exercises.

The seed's Jantzen Part II section 4 ampleness location was unchecked. I did not cite that location as an established theorem; the assembly is marked agent-written and uses the local Milne and Stacks documents plus the explicitly exposed boundary-sections input.

## Corrections and route

The statement is unchanged and is true with its specified sign. There is no statement dispute. The seed had no proof and only an unchecked ampleness pointer. I supplied the tensor-section and translation argument instead of replacing the item by a new ampleness theorem.

Read GOAL.md, the stage-1 brief, stages/1-dag.md, the three blueprint levels in SETUP.md, the role, the chapter and unit records, and delivery-errors B--E. Read the latest blueprint unit and `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). This split is below the inherited moduli/alteration/Kempf chain; it does not change the unit's direct-image argument. `blueprint_refs.py ancestor` returned None for this item; this existing null ancestor is retained in both blueprint records, with the inherited exact dependency-chain place extended for the new input. All via entries are retained. Blueprint searches for flag, ample, fundamental, fundamental weight, Bruhat, divisor, boundary and Schubert supplied no imported statement of the new result (the exact fundamental weight and Schubert searches both returned zero).

The existing general-flag linear-system node does not assert a closed immersion for the bundle of this item; I did not use it to claim one. Nor did I use the highest-weight line existence node to infer a reduced scheme-theoretic stabilizer in positive characteristic. Such an inference would be unsafe for simple modules at weights divisible by the characteristic. Instead ampleness follows directly from affine nonvanishing opens and the definition.

## Not duplicates

lem-sfb-fundamental-flag-boundary-sections vs lem-sfb-flag-effective-picard-generators: the latter gives some effective generators of Pic(Q), without associating them to fundamental characters or identifying individual zero loci with Bruhat boundary components. The new node identifies the fundamental homogeneous bundles and their individual supports; no Picard freeness theorem or ampleness assertion is duplicated.

lem-sfb-fundamental-flag-boundary-sections vs lem-sfb-fundamental-ray-regular-power: the latter supplies regular functions for positive multiples on the group and their value on the cell; it gives neither individual boundary zero loci nor fundamental-weight sections without that unspecified power.

lem-sfb-fundamental-flag-boundary-sections vs lem-sfb-double-flag-invariant-boundary: the latter concerns an invariant section on Q times Q for the rho bundle, with the double-flag open orbit and torus torsor. It neither specifies sections of the individual fundamental bundles on Q nor their individual boundary components.

lem-sfb-fundamental-flag-boundary-sections vs lem-sfb-bruhat-longest-cell-charts: charts and their coverage do not identify any fundamental line bundle section or its zeros.

lem-sfb-fundamental-flag-boundary-sections vs lem-sfb-strict-dominant-flag-line-ample: a fundamental weight in rank greater than one has zero pairing with other simple coroots and its bundle is generally not ample. The new lemma is a genuine smaller divisor input, not the item's strict-dominance assertion or its geometric clause.

## Review by Q36

I read local Milne printed pp.479--480 in full, including Remark 22.49's divisor formula and Theorem 22.48's quotient-action convention; the earlier quotient and chart statements were checked through their full DAG statements and the local Milne text. The Stacks definition is the project's `def-weil-pbc-ample-invertible-module`, sourced at properties.tex Definition 01PS. I also read the local properties.tex ampleness discussion. The exact boundary input is backed by Milne's Iversen citation and by the online Brion--Kumar section 2.1 and Exercises 2.2.E(2)--(3). These describe actual eigenvector divisors, not merely numerical equivalence. The new node deliberately asks only for zero supports and permits a permutation of the component indexing: for positive roots in Lie(B), Milne's coefficient for L(-omega_i) involves -w_0 omega_i, so claiming that a fixed boundary ordering matches omega_i would have introduced an unnecessary sign/permutation error.

Step 1 uses the final sentence of the reductive Borel structure statement to pass from semisimple to reductive. The flag torus-fixed geometry statement really says smooth and projective, without needing anything from its proof; Bruhat charts really say geometrically integral and give the finite translating affine cover. The projective definition includes quasi-compactness, so the ampleness definition's compactness hypothesis is discharged. Every cited node was opened and its complete statement read, not just its title.

Step 2 uses the simply connected character lattice statement, which identifies the actual integral character lattice with the free group on fundamental weights in every characteristic. Pairing with each simple coroot computes the coefficient a_i, so the strict inequalities imply positive integers. This is an elementary coordinate calculation; no new lattice lemma is hidden there.

Step 3 takes only the sections and their boundary supports from the new statement. The new statement introduces F, S, T, B, U, p, the root convention, the character lattice, the fundamental characters, Q, n_0, C, the bundle action and the zero loci. The cited existing nodes define these notions or are explicitly expanded inline. It has empty proof and proof_deps and carries the exact searches run, with actual output in search-boundary*.txt and query log in searches.jsonl. I read all returned types: they concern topological vector bundles, ordinary Proj functions, meromorphic analysis divisors, abstract induction, residue-field nonvanishing and unrelated Lie weights. None specializes to this algebraic-group statement. Two independent semantic phrasings and both Loogle and source grep were tried. No unavailable service was represented as absence.

Step 4 uses the characteristic Picard map's homomorphism assertion, whose action is precisely (g,z)b=(gb,chi(b)^(-1)z). Substitution chi=-nu composed with p gives the item's M_nu, so addition of weights gives the required tensor isomorphism. The tensor-product definition supplies the tensor of global sections. In a local free frame a product of coefficients is a unit exactly when all factors are units. Positive exponents therefore make its nonvanishing locus exactly the complement of all boundary components, C. This local-ring argument is elementary and written in the step; no tensor-exactness, vanishing, projective embedding, or numerical criterion is being assumed.

Step 5 uses the homogeneous line-bundle action stated by the sections node. I checked the action descends on the displayed quotient, wrote the translating section explicitly, and checked fibrewise invertibility. Thus the finite affine translating cover in step 1 is a cover by nonvanishing opens of sections of the SAME M_mu, not of unrelated pullbacks. The ampleness definition applies with exponent one. All hypotheses, including algebraic closedness, reductivity after the semisimple passage, simply connectedness for integral fundamental weights, and positivity of every a_i, occur before use.

Small cases: for SL2 with B upper triangular and the positive root in Lie(B), M_omega is O(1) on P1, the section has one zero point, and its open is A1. M_(a omega) has multiplicity a at that point; positive a has the same open, while a=0 gives no affine chart on P1, explaining why strict positivity matters. For SL2 times SL2, the two fundamental bundles pull back O(1) from the two factors; individual sections have the two boundary components, and their positive tensor has open A1 times A1. The fundamental bundles themselves are not ample, so the new input does not restate the item. For the trivial group the root and character lattices vanish, C=Q=Spec F, the empty tensor is 1, and O is ample directly. In characteristic p, even a_i divisible by p is a positive exponent and preserves the unit locus; the argument makes no separability or simple-module embedding claim.

Checked B1--B10: one self-contained statement-only new node, inline notions and genuine definition citations, single-escaped TeX in decoded strings, precise literature places, no fictitious Stacks tag for the representation theorem, all genuine searches, no Mathlib leaf without an exact declaration, and explicit blueprint provenance. Checked C1--C8: every substantive input is cited, every quote is verbatim, no proof-of-a-node used as a stronger statement, and all six existing geometric/characteristic nodes have been checked for paths back to the item (none). The proof introduces no off-unit tool: all statement inputs have the item's unit; the other inputs are definitions. Checked D1--D5: the item itself constructs the tensor section and affine translating cover, and its single new node is a smaller fundamental-divisor fact. Checked E1--E7 as detailed above: signs, zero supports, positive characteristic, rank zero, and action on the correct bundle. All proof steps are below 2000 characters (467, 291, 279, 702, 806), and the potentially non-elementary divisor calculation has been exposed as the new node rather than concealed in an elementary step.

## Unfinished work

None for this one-level split. The new statement-only divisor input remains for a later worker, as required. Awaiting the required server dry run and delivery below.
