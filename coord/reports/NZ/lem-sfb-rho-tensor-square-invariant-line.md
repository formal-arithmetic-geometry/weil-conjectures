## Worker report

Files written:

- dag/nodes/sec-six-functors-basics/lem-sfb-rho-tensor-square-invariant-line.json: item split into four steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-rational-induction-character-reciprocity.json: new statement-only node, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-induced-module-primitive-line.json: new statement-only node, unsplit; no Mathlib match.
- citations.json: verbatim statement quotes for all three cited nodes.

Attachments: none. Searched lean/WeilConjectures for the exact blueprint tag, rho tensor-square terminology, Steinberg, Borel--Weil, highest weight, primitive vectors and rational induction. The Lang--Steinberg semilinear declarations found concern a different theorem. No matching project proof was found.

WANTED: Jarod Alper, Adequate moduli spaces and geometrically reductive group schemes, arXiv:1005.2398, local PDF, Lemma 9.7.2(1) and Remark 9.7.3. Read the online primary source https://arxiv.org/html/1005.2398v3#S9.SS7; the designated local PDF is absent. The present proof is agent-written from locally available Milne, not a claimed local-PDF transcription of Alper.

The imported assertion is correct. Alper's field formulation in Remark 9.7.3 agrees with it. The original positive right-semi-invariance convention means W_m=E_B(-m rho), rather than E_B(m rho) in Milne's convention; getting this sign wrong would give the wrong Borel weight. No statement correction or source-error assertion is needed. The primitive-vector theorem gives invariants under the unipotent group, not Lie algebra invariants. No simplicity, semisimplicity or self-duality of W_m for general m in positive characteristic is used.

Nothing mathematical remains unfinished at the item's level. The two supporting results are deliberately left statement-only for subsequent workers, with sources and genuine searches. No Lean was written and no compiler or Lake command was run.

## Search record

All new-node searches were run with the mandated msearch.py and retained in searches.jsonl. Each node records the actual query, logged hit names and verdict. Each has LeanFinder, LeanSearch, Loogle and Mathlib grep, including a second semantic phrasing. Existing imported searches of the item were preserved and fresh item searches added.

For reciprocity I read Mathlib/RepresentationTheory/Coinduced.lean:275--307 and FiniteIndex.lean:173--206. Rep.resCoindHomEquiv concerns arbitrary functions on abstract monoids; it does not give the regular-function rational induction module without a substantive algebraicity argument. Rep.resIndAdjunction additionally assumes finite index. Neither is a leaf for the new statement. For the primitive line, returned LieModule and RootPairing weight-space results do not assert unipotent-group fixed vectors in regular-function induction. A targeted RepresentationTheory grep returned no hits. For the item, FDRep.finrank_hom_simple_simple requires simple representations and cannot apply uniformly to W_m in characteristic p.

Searched the whole DAG by source numbers 22.22, 22.29, 22.30, primitive line, highest weight, Bruhat, unipotent fixed vectors, Seshadri and Frobenius reciprocity. Searched imported blueprint nodes with blueprint_refs.py for highest weight, Bruhat, primitive, semi-invariant, induced representation, unipotent, Frobenius reciprocity, 22.22 and rho. No exact or more general duplicate was found. ancestor prints None; the new nodes retain that null ancestor and the exact existing lineage, adding the item at the front of via. The current latest blueprint's direct-images proof (3) and current chapter/unit text were read; this is the same supporting representation-theoretic route as the item's parent, not a change to the unit.

## Not duplicates

lem-sfb-induced-module-primitive-line vs lem-sfb-unipotent-rational-representation-fixed-vector: the existing node only asserts existence of a nonzero vector fixed by the F-points of a smooth unipotent group in a nonzero representation. It gives neither uniqueness of a line in an induced module nor its T-weight, the longest Weyl element, or the Borel multiplication isomorphism.

lem-sfb-induced-module-primitive-line vs lem-sfb-rho-section-modules: the existing node constructs the Borel pair and rho section modules and states nonzero finite dimension, without computing their unipotent invariants or their torus weights.

lem-sfb-rational-induction-character-reciprocity vs lem-sfb-condensed-tensor-induction-adjunction: that node is about sheafified group-ring tensor induction for condensed/internal module sheaves and a left adjoint. The new node is regular-function rational algebraic-group induction, a right adjoint expressed by evaluation at the identity. Coefficient categories, constructions and adjunction direction differ.

lem-sfb-rational-induction-character-reciprocity vs lem-sfb-rho-tensor-square-invariant-line: reciprocity does not calculate a dimension, require a semisimple group, or mention rho or tensor squares. The item still needs tensor duality and the primitive-line calculation.

lem-sfb-induced-module-primitive-line vs lem-sfb-rho-tensor-square-invariant-line: a primitive line in any nonzero Borel-character induction is not the invariant space of a tensor square. The item must identify the tensor invariants with the correct Borel-character subspace, including its sign, using reciprocity and finite duality.

## Review by NZ

I read locally Milne Definition 22.21, Proposition 22.22 and its proof (printed pp.468--469), 22.29(a),(b) and 22.30 (pp.470--471), Definition 21.72, Theorem 21.73(b), Remark 21.74 (p.448), and the proof of Proposition 21.29 (pp.433--434). I also read Alper's online Lemma 9.7.2 and Remark 9.7.3. The latter asserts the field invariant-line conclusion, while Milne supplies a proof independent of any problematic reduction of invariants modulo a maximal ideal. All new-node statements have complete hypotheses and explain their function convention and group-scheme meaning. They contain no proof sketch or proof dependencies.

Step 1 uses the actual statement of lem-sfb-rho-section-modules: W_m is nonzero finite-dimensional and has the displayed regular-function identity with positive exponent. I checked the identity against Milne's inverse-character convention, obtaining chi=-m rho. I spelled out why the finite dual carries a rational action, by inverse and transpose matrix coefficients. This step is elementary from that statement and definitions.

Step 2 uses no black box: I checked the tensor-to-Hom formula and its explicit dual-basis inverse, and the conjugation calculation on a pure tensor. The formulas are over any commutative extension algebra and yield group-scheme equivariance. Finite dimensionality from Step 1 is precisely what makes the inverse available. This routine linear-algebra calculation is elementary and is not made into a redundant node.

Step 3 cites exactly the evaluation-at-identity linear isomorphism in the new reciprocity statement. I checked its hypotheses: S is affine of finite type, B is closed, W dual is finite-dimensional rational, and the target regular-function module is exactly W. For the subsequent dual-evaluation identification, h( b ell )=chi(b)h(ell) becomes ell(b inverse w)=chi(b)ell(w), so the resulting B-weight is chi inverse=m rho. That inverse is essential. This finite-dual calculation is written explicitly rather than hidden in a transport assertion.

Step 4 cites exactly the new primitive-line statement, including its Borel multiplication isomorphism. Applying it to E_B(chi) is legal because W is nonzero. The result is a U-fixed line of weight w0 chi. Since w0 permutes positive roots onto negative roots, it sends rho to -rho. This is an integral character-lattice equality; it does not divide by 2 in the field, so characteristic 2 causes no exception. The full B-character follows from B=T semidirect U. I corrected my first draft by putting that structural assertion explicitly in the supporting node, with Milne sources, instead of assuming it from a definition node. Conversely every B-eigenvector of that character is U-fixed, giving equality with the line, not merely an injection into it. The prior linear isomorphisms therefore give dimension exactly one, including existence.

For edge cases I checked S=1 (then T=B=U=1, rho=0, W=F and all spaces are F), SL2 with its upper triangular Borel (W_m is degree-m polynomials in the first column, and the U-fixed polynomial is c^m, of torus weight m rho), m=1, characteristic 2, and weights m at or beyond the characteristic. The argument never uses simple W_m, a nondegenerate invariant form or Schur's lemma. For reciprocity I checked H=1 (regular coaction coefficients) and H=G (E_G(chi) is the line spanned by chi inverse), as well as V=0. For the primitive node the implication explicitly excludes zero E_B(lambda); the trivial character gives constant functions and weight zero. Thus no false nonvanishing assertion is made for arbitrary characters.

Against delivery-errors B--E: the two new nodes are self-contained, statement-only, cite the notions they use or define them inline, and use ordinary TeX with one decoded backslash. The sources are Milne propositions, so no fabricated Stacks tag is substituted. Each created node was searched in the DAG, blueprint and Lean before writing. Neither node is an elementary rewrite, nor a clause restating the tensor-square item. Every non-elementary input has a cited statement and a verbatim quote in citations.json; proof_deps is the exact union of uses. There is no use of a dependency's proof or an uncited source theorem. The item has four steps, none longer than 2000 characters. No off-unit proof tool or SGA source is used. The item statement, its hypotheses and conclusion were preserved exactly.
