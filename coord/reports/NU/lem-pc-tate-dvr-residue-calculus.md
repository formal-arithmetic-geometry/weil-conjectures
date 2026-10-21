# NU: lem-pc-tate-dvr-residue-calculus

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-tate-dvr-residue-calculus.json`: mathematical statement unchanged; statement dependencies completed for ordinary trace, finite-dimensionality and completion; eleven proof steps; status split.
- `dag/nodes/sec-picard-framework/lem-pc-finite-potent-trace-calculus.json`: new statement-only node, unsplit; no Mathlib match. General invariant-subspace, exact-sequence, cyclicity and restricted additivity rules for finite-potent traces.
- `dag/nodes/sec-picard-framework/lem-pc-tate-endomorphism-ideals.json`: new statement-only node, unsplit; no Mathlib match. Tate's operator ideals and vanishing traces of mixed commutators.

`citations.json` contains a verbatim quotation for every step/node pair. `searches.jsonl` and `research/` preserve the actual searches and their answers. No repository, launcher, literature, Lean or unit file was modified.

## Attachments

No project declaration states the entire item. Searching the exact blueprint tag and the concepts in live `lean/WeilConjectures/` found the TateResidue modules, which contain much of the abstract construction, but not this item's complete DVR and separable Laurent comparison package. In particular this is not an ATTACH claim for the item.

The maintainer can reuse the following source declarations for the new trace node: `Module.End.tateTrace_eq_trace_restrict` (FinitePotent.lean:143), `Module.End.tateTrace_eq_trace` (:163), `Module.End.tateTrace_eq_zero_of_pow_eq_zero` (:174), `Module.End.tateTrace_smul` (:184), `Module.End.tateTrace_sum` (:213), `Module.End.tateTrace_comp_comm` (:267), and `Module.End.tateTrace_eq_add_of_exact` (:299), in `WeilConjectures.RingTheory.TateResidue.FinitePotent`. I read their signatures and proofs, including the restriction/quotient argument at lines 299–360. The file imports Mathlib and has no sorry. The node includes the finite-potence assertions on both sides of restriction and cyclicity as well as the trace equalities, so this is a list of source components rather than an asserted single exact declaration attachment.

For the ideals node the corresponding source is `WeilConjectures.RingTheory.TateResidue.TateIdeals`: `TateResidue.fg_range_mul` (:248), `TateResidue.isFinitePotent_of_mem` (:254), `TateResidue.tateTrace_add_of_mem` (:258), `TateResidue.tateTrace_commutator_eq_zero` (:268), and `TateResidue.tateTrace_commutator_eq_zero'` (:278), together with its E/E₁/E₂ definitions and closure lemmas. This file has no sorry either. Neither source inspection is represented as a compiler or transitive axiom audit.

## WANTED

None. Tate's paper and the supporting Stacks sources are present.

## Corrections and scope

The imported statement is mathematically consistent and was retained verbatim. There was no imported proof to repair. I supplied the completion argument for an arbitrary DVR with finite separable residue extension, rather than assuming that the DVR comes from a finite-type curve. The original projection is an arbitrary k-linear projection; the proof never assumes it continuous or coefficient-linear. After proving projection independence, the Laurent calculation may choose the coefficient-linear nonnegative-power projection.

The two new tools do not relabel the residue theorem: neither constructs a residue or mentions a DVR, a uniformizer or a Laurent series. The first supplies trace rules for arbitrary infinite-dimensional vector spaces and arbitrary invariant exact sequences, beyond the item's trace definition. The second concerns an arbitrary subspace of an arbitrary vector space. The item's proof carries the bilinear descent, uniformizer normalization, finite quotient, coefficient-field construction and Laurent calculation itself. No new node was made for the elementary fractional-ideal filtration or for multiplying a residue-field basis by powers of a uniformizer.

## Not duplicates

- lem-pc-finite-potent-trace-calculus vs lem-pc-tate-dvr-residue-calculus: the new tool is invariant-exact-sequence and cyclic trace calculus on arbitrary vector spaces, not a residue construction; the original definition of trace is recovered from it, while the residue arguments remain in the item.
- lem-pc-tate-endomorphism-ideals vs lem-pc-finite-potent-trace-calculus: ideals attached to a chosen subspace, their finite-rank products and mixed commutator vanishing, rather than the trace calculus without a chosen subspace.
- Both new nodes vs sk-thm-picard-duality and lem-pc-tate-adelic-reciprocity: those concern respectively curve duality and global reciprocity, not the general linear algebra. Searches for finite-potent, finite potent, endomorphism ideals and Tate residue found no existing blueprint tool for these statements. The only relevant whole-DAG hits are the item and its consumers.

No new source carries a Stacks tag, so there are no same-tag duplicate pairs. Existing completion, DVR factorization, and residue-section tools were reused. Their off-unit applications are individually declared in `split_report.tool_uses`; they provide generic algebra without replacing the unit's Tate-residue route.

## Review by NU

I read Tate, *Residues of differentials on curves*, printed pp.149–157: §1 T1–T5 and Propositions 1–2 for both new nodes; §2 Theorem 1, formula (*), R2 and R4 for the item; §3 the local definition, Theorem 2 and Theorem 4 for comparison with classical residues. I also read the current main-20261015 Picard-duality unit and proof, and the statements of every cited DAG node. The route remains its local Tate residue construction. The new nodes are deliberately left statement-only, with all objects defined inside them.

Step 1 uses the DVR definition and exactly the unit-times-uniformizer-power assertion of `lem-weil-pbc-dvr-unit-times-uniformizer-power`. A DVR is Noetherian, its maximal ideal is generated by the chosen nonzero uniformizer, and its fraction field is K, so the lemma applies to numerator and denominator. The successive quotients are explicitly identified with the given finite extension κ/k; this verifies the finiteness needed everywhere later.

Step 2 uses precisely the ideal closure and finite-potence conclusions of the ideals node, and stable-subspace trace independence from the trace node. I verified that the lifts differ from multiplication by maps finite on O; this uses the finite quotient from Step 1, rather than any continuity. Step 3 uses the two distinct mixed-commutator clauses of the ideals node, in the correct order, and its linearity only on E₀. There is no claim that arbitrary finite-potent traces are additive. Step 4 uses these same clauses and the actual generator-and-relation presentation in the Kähler node. Expanding the displayed operator identity gives the double commutator on the right; its trace vanishes by [E₀,E]. It is not incorrectly asserted to be an identity with zero on the right before taking trace.

Step 5 uses invariant-subspace exact additivity and zero trace of zero operators from the trace node. I checked both hypotheses explicitly: the image lies in B, and C is killed. Its regular-differential conclusion uses the Kähler node's presentation. Step 6 uses the same trace clause twice, now with tO⊂O⊂K. Its map on O/tO really is multiplication by the residue of u, so the field trace is the one in the statement, with a positive sign.

For Step 7 I read Stacks algebra.tex, lemma-hathat-finitely-generated (Tag 05GG), and more-algebra.tex, lemma-complete-henselian (Tag 0ALJ). The two existing completion nodes state exactly completeness and the compatible kernels/quotients used here. The ideal (t) is principal, hence finitely generated. The inverse construction proves R local with maximal ideal tR before the henselian residue-section lemma is applied. The latter's statement was opened, and its live Lean signature in `lean/Sheaf/RingTheory/HenselianSeparablyGeneratedResidueSection.lean` was inspected: the residue map is surjective, its kernel is the maximal ideal, the algebra structures agree, and the empty separating family leaves a separable algebraic extension κ/k. No perfectness of k is required.

Step 8 uses the completion statements, plus factorization already cited, to construct the power-series coordinates by successive residues and prove injectivity, surjectivity and the intersection K∩R=O. I marked it non-elementary and wrote the construction rather than saying 'by Cohen structure'. Step 9 uses the exact compatible quotient assertion of the mod-power node and the trace clause of the trace node. I checked that the extended projection is well-defined on K+R, and that the finite quotients and induced commutators are actually identified. Thus the comparison does not assume that a projection extends continuously.

Step 10 uses the ordinary finite-dimensional trace supplied by the trace node, applied to the finite quotient already proved in Step 5. The diagonal coefficient is written explicitly, and the signed finite interval counts to j, including negative integers and positive characteristic. It does not take a trace of an infinite sum. Step 11 uses exactly the Kähler presentation to pass from f dg to a finite sum of generators; the separable-minimal-polynomial calculation explains why coefficient differentials vanish. The continuous Laurent image is therefore the one claimed in the item.

I checked small cases: f=0 or g=0; f,g regular; u=0; κ=k; finite inseparable κ/k in the normalization clause; and monomials t^i d(t^j), with i+j=0 and i+j≠0, including characteristic p with j divisible by p. The separable coefficient section is used only after that hypothesis is introduced. For the new trace tools I checked zero and finite-dimensional spaces, infinite-dimensional square-zero maps, and A=0 or A=V in the ideals theorem. The pairwise-product hypothesis includes all products, including squares. As an arithmetic sign check, 200 finite Laurent examples over characteristics 0,2,3,5 matched the diagonal-strip trace and the coefficient formula; the result is recorded in research/coefficient-check.txt and is not substituted for the proof.

Finally I checked delivery-errors B–E against the actual files: both new statements are self-contained TeX with no proof sketches, sources are the actual Tate propositions, searches were run and their real outputs retained, and no finite-dimensional Mathlib trace hit was mistaken for Tate's infinite-dimensional trace. Each proof use has a verbatim statement quotation in citations.json. The steps give the actual arguments, with no restatement children or hidden use of a consumer of the item. No proof step exceeds 2000 characters. No SGA source is used.

## Unfinished work

No part of the item's natural-language split is left unfinished. The two new nodes remain unsplit as required for one-level delivery; the existing project source components listed above should help their subsequent attachment or split. Server dry run and direct push are performed after this report is written.

## Dry-run repair

The first required dry run rejected the trace tool because it had no bracketed definition dependency. I opened `def-weil-finite-dimensional-subspace` and `def-weil-endomorphism-trace`, verified that they define exactly the finite span condition and ordinary matrix trace used, and cited both in the new trace statement. I also completed the item’s statement dependencies for these notions and adic completion, and explicitly cited the ordinary trace definition in the diagonal-matrix calculation (Step 10). The mathematical statement and search questions did not change. The quotation ledger was regenerated from the amended statements.
