# Q133: lem-sfb-block-gauss-scheme-chart

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-block-gauss-scheme-chart.json: item, statement, split; full scheme statement retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-two-block-schur-identities.json: new statement, Mathlib leaf. Matrix.fromBlocks_eq_of_invertible₁₁ (SchurComplement.lean:50–58) and Matrix.det_fromBlocks₁₁ (:370–375) give its two clauses.
- citations.json: one verbatim statement quotation for every node cited by each numbered item step.

The sandbox also holds the actual search log, a text extraction of the source, and the local JSON-writing helper; these are working material, not DAG deliveries. No repository or launcher file was written. No Lean source was written and no compiler, Lake or build tool was run.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag and Gauss, Schur, unitriangular and leading-minor terminology found no declaration giving the entire item. The Schur-complement extension file deals with a vanishing Schur complement, not this scheme chart. Mathlib's two-block identities are a leaf, not an attachment of the full item.

## WANTED

None. Milne's book, the Stacks sources, and the pinned Mathlib sources used here are present.

## Findings and corrections

The item is explicitly an agent-stated general matrix prerequisite. I read Milne §23h, equation (153), Theorem 23.72 and its proof and Notes, printed pp.510–511. These motivate the immersion calculation but do not state this Gauss chart: Milne says that the remaining details are omitted. The delivery therefore records proof_origin.by = agent and does not claim that Milne proves the displayed scheme isomorphism.

The inherited item had no proof and no Lean audit record, and its recorded Mathlib searches belong to its creator. I retained them and performed and logged Q133 searches in all four required modes. The second conceptual phrasing also gives only block determinant, pivot and LDL results. The actual Schur identities are exact matches for the new leaf; they are not exact matches for the all-algebras many-block scheme chart.

The live item's blueprint.from.node is null. tools/blueprint_refs.py ancestor lem-sfb-block-gauss-scheme-chart prints None. I retained that inherited value and the via chain, and the new leaf inherits that result. The explicit place still identifies det-thm-sf-ctf-stability-direct-images, proof (3), and the supporting Milne calculation. The latest blueprint (COMMITS.txt: main-20261024 ef6f9619) has no Gauss-chart or Schur-complement node. I read its sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md; the descendant calculation does not change the alteration route. The unit and chapter records are unchanged.

No mathematical statement correction or STATEMENT-DISPUTED issue was needed. The scheme statement is valid over arbitrary commutative test algebras, not just fields. The proof preserves the unit condition on every leading determinant and checks equivariance as morphisms, not just on geometric points.

## Not duplicates

lem-sfb-two-block-schur-identities vs lem-sfb-unit-pivot-schur-formula: that node normalizes a scalar unit pivot of a continuous rectangular family; the new leaf allows an arbitrary invertible square pivot block and also states the Schur determinant formula over every commutative ring.

lem-sfb-two-block-schur-identities vs lem-pur-coordinate-graph-localized-jacobian: the latter computes a Jacobian over a residue field in a standard-smooth presentation; it does not state either universal block identity over arbitrary commutative rings.

lem-sfb-two-block-schur-identities vs lem-pc-constant-rank-map-local-normal-form: that is a local normal form for maps of module sheaves on a reduced scheme with constant fibre rank, not the arbitrary-ring block identities.

lem-sfb-two-block-schur-identities vs lem-pc-complementary-block-residue-vanishes: that node deduces zero residue coefficients of a complementary block from a rank bound, not the Schur identities without rank hypotheses.

lem-sfb-two-block-schur-identities vs new-residue-kernel-unit-minor-pivot: that node finds coordinate equivalences from a one-dimensional residue kernel over a local ring; it neither states the factorization nor the determinant identity.

lem-sfb-two-block-schur-identities vs lem-sfb-matrix-cramer-determinant-identities: that leaf states determinant multiplication, adjugate determinant and Cramer's formula. Its statement contains no Schur complement or two-block factorization. It is reused for its determinant-multiplication clause.

The full DAG search included the Schur, Gauss, leading-principal-minor, unitriangular, adjugate and determinant keywords and the two exact Mathlib declaration names. All nodes whose statements mention a Schur complement were read or inspected as candidates: the continuous-integral-pivot, continuous-field-elimination, integral-lfp-resolution, condensed-lfp and row-minor-invariance nodes have topological, sheaf or determinantal-ideal conclusions, not these identities. Blueprint searches for Schur, Schur complement, Gauss, block triangular, principal open and determinant found no duplicate of the new leaf. No new Stacks-tagged node is being introduced; the existing adjugate and localization nodes are reused.

## Review by Q133

I reviewed delivery-errors B–E against the two JSON files and the actual sources. For the item I read Milne §23h, equation (153), Theorem 23.72 and Notes, pp.510–511. For the new leaf I read Mathlib/LinearAlgebra/Matrix/SchurComplement.lean:37–58 and :368–375: both clauses have only CommRing and finite decidable indices; there is no field, nontriviality, nonempty-index, or invertibility condition on the Schur complement. Instantiating the two index sets with Fin a and Fin b gives exactly the displayed statement. An arbitrary specified two-sided inverse supplies the Invertible instance and equals invOf by multiplying the two inverse equations. Empty blocks and the zero ring are therefore genuinely covered. Its statement introduces all four matrix sizes and every symbol; it has no proof sketch, proof steps or proof dependencies.

Step 1 uses def-sc-general-linear-group for its actual localized-polynomial presentation and all-algebra point description; def-weil-pbc-mv-polynomial-ring for evaluation and uniqueness; and def-weil-affine-spectrum for spectra, contravariant maps and their uniqueness. I opened these statements: they say these things explicitly. It uses lem-weil-pbc-affine-open-section-vanishing-prime only for clause (b), that a principal open of an affine open is affine and its section ring is the indicated localization. I checked its Stacks inputs 01I3 (schemes-lemma-standard-open-affine) and 01HV (schemes-lemma-spec-sheaves). It uses lem-weil-pbc-ring-localization-universal-property exactly for maps to rings in which f is a unit; I read Stacks 00CP (algebra-proposition-universal-property-localization) and its proof. The argument for each factor of a product being a unit is written explicitly. The nilpotent triangular inverse is a finite geometric sum, and the proof explains why N^s = 0. Thus representability of L and U is constructed, not silently assumed from a theorem about smooth groups.

Step 2 cites the new leaf for the determinant of a triangular block matrix (pivot I) and a block diagonal matrix (zero off-diagonal blocks). The source identity gives precisely these special cases, including the trailing empty block. It cites lem-sfb-matrix-cramer-determinant-identities only for det(AB) = det(A)det(B), which I read in its statement and in Matrix.det_mul, Determinant/Basic.lean:138. In positive-dimensional leading blocks the node's n >= 1 hypothesis holds since every E_i is nonzero; s = 0 is already separate. The product-restriction index argument is written, so there is no false claim that an arbitrary leading submatrix of a product is a product of leading submatrices. Polynomial evaluation and localization then give a morphism into the open, using the actual unit just computed.

Step 3 cites lem-weil-pbc-matrix-adjugate-identity, whose statement gives BOTH M adj(M) = det(M)I and adj(M) M = det(M)I, not just a right inverse. I read the adjugate sentence in the proof of Stacks 07DQ (algebra-lemma-matrix-left-inverse). This supplies the inverse of P and later of S when their determinants are units. The new leaf is applied to each leading submatrix with that same first invertible pivot P. The equality Delta_(k+1)(g) = det(P) Delta_k(S) gives all required units for the smaller induction; the full determinant makes S invertible, so no unjustified induction on a possibly singular matrix occurs. The induction hypothesis quantifies over EVERY commutative F-algebra, not just F, and the assembled three factors are displayed with the correct multiplication order. This is the item's own block induction, not a new node repeating its conclusion.

Step 4 is elementary and cites no node: all four block equations are written, so they recover p, x, y, and the smaller product. The induction base s = 0 or 1 is explicit. Functoriality follows by uniqueness because an algebra map takes a specified two-sided inverse to a two-sided inverse. No continuity or algebraic-closure assertion is used.

Step 5 uses the three coordinate/universal-property statements from step 1, reread for this use. It applies the previously established algebra argument to the universal matrix over H_f, constructing an inverse morphism using entries and actual units in H_f. It then compares the two composites on coordinate generators and inverse determinants; the cited polynomial and localization uniqueness statements really say that suffices. I specifically checked that this does not use a generic Yoneda lemma on the wrong category, and does not infer scheme equality from field-valued points. Both source and target are the affine schemes explicitly constructed in step 1. Equality is checked in their universal coordinate rings.

Step 6 uses the determinant-multiplication clause of the existing Cramer leaf and the affine-spectrum correspondence. The entrywise conjugation formula preserves the triangular shapes and identity blocks. The restriction of a block diagonal conjugation is the conjugation of the leading block, so its determinant is unchanged. Multiplication equivariance is associativity; inverse equivariance is uniqueness. Taking the universal test algebra for D times the respective source proves equality of the action morphisms, including varying h, rather than only equivariance for F-valued diagonal elements. These are elementary consequences of the displayed equations and cited statements.

For B1–B10 I checked that the new node is statement-only, self-contained, has the correct determinant and matrix notions, ordinary TeX escapes, pinned declaration names, file and read line numbers, genuine searches and a complete blueprint record. For C1–C8 I opened every cited statement; citations.json quotes it verbatim. All external theorems are either existing Mathlib leaves or the new Mathlib leaf, so no off-route statement tool declaration is required. There is no new Yoneda or principal-open node, and no node that restates the item or one of its output clauses. The single new leaf is the two-block calculation the many-block induction uses. All six proof steps are shorter than 2000 characters; there is no long step hiding a separate scheme comparison.

I tested the small cases directly. For s = 0 all objects and maps are terminal and the empty product is 1; for s = 1 the open is GL(E_1) itself and the inverse is (I,g,I). For two one-dimensional blocks the formulas give d = diag(p,w-t p^(-1)q), l_(21) = t p^(-1), u_(12) = p^(-1)q, and the determinant identity is det(g) = p(w-t p^(-1)q). Over F_2[e]/(e^2), the matrix [[1,e],[e,1]] has factors l = [[1,0],[e,1]], d = I, u = [[1,e],[0,1]], so the nonreduced case uses the same formulas. In characteristic 2 the signs become plus, but the cancellation equations still hold. Over F_2 times F_2, the nonunit (1,0) is excluded as a pivot even though it is nonzero, matching the use of units. The invertible swap matrix [[0,1],[1,0]] has zero first minor and is correctly outside the chart. The zero algebra has one matrix of each size, all unit equations hold, and the formulas remain defined. For the new leaf a = 0 gives det W = 1 det W and b = 0 gives det P = det P times 1. I also checked a non-scalar pivot on two coordinates: P = [[1,z],[0,1]] has inverse [[1,-z],[0,1]], and multiplying the displayed three factors yields the four blocks P,Q,T,W without requiring any entries to commute beyond commutativity of the coefficient ring; the block matrices themselves are multiplied in the stated order.

I corrected the proof approach before writing: a pointwise bijection on fields would not establish the scheme chart, so step 5 uses universal coordinate rings. I also kept the Schur algebra lemma as a Mathlib leaf instead of introducing another unsplit many-block LDU statement. No statement weakening, added hypothesis or source-route replacement was made.

## Unfinished work

None within this stage-1 split. The new algebra lemma is already a Mathlib leaf. Independent maintainer review remains the project's delivery review, as specified by the direct-delivery brief.

## Dry-run repair

The first full preflight treated TeX matrix row separators immediately followed by T or x as doubled command escapes (B4). I added a space after these legitimate row separators in the new leaf and steps 3–4, and refreshed the leaf quotations in citations.json. The formulas and mathematical statements are unchanged.
