# Stage-1 report: lem-sfb-triangular-reflection-orbits

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-triangular-reflection-orbits.json: item, statement; complete ten-step split, no Mathlib match.
- citations.json: a verbatim statement quote for each dependency of every proof step.
- report.md: this report. searches.jsonl contains actual search-command output records; milne.txt and write_split.py are sandbox research aids, not delivery nodes.

No new nodes; no Mathlib leaves. The statement and statement dependencies are unchanged, and all inherited provenance, searches and import fields are retained. No repository, launcher or Lean files were changed and no compiler was run.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id and triangular/reflection/root-subgroup concepts. No declaration states this algebraic-group assertion. Existing RootPairing declarations in Mathlib require a root pairing or base as input and do not establish this item.

## WANTED

WANTED: Robert Steinberg, Lectures on Chevalley Groups (1999), section 5, especially 5.14--5.17 cited in the imported source, for comparison with lem-sfb-triangular-reflection-orbits. This document is absent from the literature available here. The delivered proof does not invoke those assertions. It is explicitly marked agent-written and uses only the existing cited results and the elementary arguments written in the steps.

## What was wrong and what changed

The imported item had no proof. Its source is a supporting assertion for Milne 23.31, rather than the text of 23.31 itself. Milne 23.31 concludes reductivity under rank-one generation assumptions; using that theorem here would make the parent rank-one generation split circular. The delivered proof does not use that conclusion or assume that the orbit contains every adjoint weight. Its only group-structure theorem is the existing normalizer-component theorem, valid without reductivity.

No statement dispute or statement correction was necessary. In particular the coroots need not span the whole torus cocharacter lattice, and roots need span only their rational span. Some hypotheses (the retraction kernels and their reflection invariance, and the big cell) are stronger than the proof needs: the assumed extension for every dominant integral cocharacter and the fixed-subgroup identities already suffice. They were retained, not altered.

The blueprint ancestor command returns None for this imported supporting chain. I retained its inherited from.node=null, exact from.place and via chain and filled the split_report description. The current blueprint is literature/blueprint/latest -> main-20261024. I read its direct-images proof (3); this supporting algebraic-group argument is below the alteration/moduli/PGL branch already recorded in the item. No unit or chapter route changed.

## Review by O1

I read coord/brief-stage1.md, stages/1-dag.md, the three levels of SETUP.md, GOAL.md, the chapter and unit records, and both copies of delivery-errors.md sections B through E. For the source I read Milne's printed p.494 (23.31 and 23.33) and Appendix C.1--C.22 (pp.607--612), including the finite-reflection and chamber formulations. For reused group inputs I checked Milne's cited places through their existing node statements: normalizer components (12.40 and 13.10--13.11) and split character antiduality (12.8--12.9). No SGA source is used. There are no new nodes needing separate source or duplicate reviews.

Step 1 cites lem-sfb-torus-normalizer-components for exactly its finite quotient N(F)/C(F). Its statement explicitly assumes only smoothness, connectedness, affineness and finite type, all present here. It does not require reductivity. Factoring conjugation through this quotient is the elementary kernel observation written in the step.

Step 2 cites lem-sfb-multiplicative-character-antiduality for the contravariant equivalence and split character identifications, not for an unsupported cocharacter theorem. Taking F as its own separable closure makes the Galois action trivial. Applied to D_F(Z^r) and D_F(Z), full faithfulness identifies cocharacters with Hom(Z^r,Z). The remaining extension of a rational coefficient functional, multiplication by a positive integer denominator, preservation of L, and s_alpha^2=1 are explicit finite-matrix calculations. Independence is used in L, not by asserting that D extends to an integral basis of X.

Steps 3 and 4 cite def-sc-gm-ga for the additive and multiplicative coordinate algebras. The parameter formula holds after every scalar extension. A zero lambda pairing would give a closed additive line inside T; units of F[z] are constants, so the map is identically the identity and cannot be a closed immersion. For positive pairing the limit is exactly a(0)=1, giving inclusion in U by the assumed subgroup-functor equality. In step 4 I checked the stronger regularity argument rather than asserting that a positive group has positive weights: lift the line coordinate along the surjection O(U) -> F[z], pull back the actual assumed A^1 action, and compare the polynomial with t^k z in the Laurent algebra. This excludes negative k without requiring that the monoid action preserves the line at zero. Applying the specially constructed cocharacters isolates each D coefficient. Negating a root is realized by the word w s_alpha, so the negative case is equally justified.

Step 5 is an explicit two-coordinate argument: both q and q^{-1} must be integers since inverse words preserve L. This rules out multiple roots even when a simple root is not primitive in the larger torus character lattice X. It does not use a root-system theorem that already assumes reducedness.

Step 6 writes the finite average and verifies invariance and positivity. Its reflection calculation supplies the formula 2B(x,rho)/B(rho,rho), proving independence of the reflection functional without an uncited uniqueness theorem. Step 7 then checks all the root-system axioms as defined inline in the item: root permutation, integral pairings, spanning, nonzero vectors and reducedness. The coefficient signs were proved earlier. These are computations with the already defined reflections, not a new general lemma or a theorem hidden behind the word standard.

Step 8 uses only the given equality C_U(eta_alpha)=U_alpha and the preceding parameter formula to factor a simple-character line. I wrote the closed-immersion polynomial argument, including surjectivity and degrees, to exclude a proper inseparable image in positive characteristic. It proves equality of subgroup schemes, not equality of tangent spaces or merely rational points. Conjugating two candidate lines back to a simple character then proves word independence without assuming normalizer lifts differ by T.

Step 9 cites lem-sfb-root-chamber-simple-transitivity for both transitivity and the equivariant injective correspondence between bases and chambers. I checked every hypothesis against steps 1--7, including the real invariant positive form and reducedness. The reflection-group equality is established by generators and conjugation before taking a word lift; faithfulness on the unused central torus directions is unnecessary. Step 10 uses only the generation hypotheses and uniqueness from step 8, explicitly also handling the conjugates of V_alpha. Thus both conjugations U -> V and V -> U are established; neither is inferred just from the other.

I tested rank one (eta_alpha may be zero), nonprimitive simple characters in X, products of rank-one systems, an unused central torus, and characteristic p including pairings divisible by p. All weights and pairings remain integral characters, not differentials, so no characteristic-zero argument about the algebraic group is smuggled in. The averaging happens in a real vector space of lattice characters, independently of the field characteristic. No emptiness exception is needed because D is assumed nonempty.

Checklist B: no new nodes, no duplicated definitions, correct single-backslash TeX, and only real searches recorded. Checklist C: each used statement was opened and the quote in citations.json is literal; no result is taken from another node's proof, no dependency on the parent or downstream reductivity, and all theorem dependencies are existing nodes in this unit. Checklist D: the proof actually supplies signs, reducedness and subgroup uniqueness rather than renaming those clauses as new nodes. Checklist E: scheme-theoretic inclusions, signs, scalar extensions and the real versus base-field vector spaces are kept distinct. All ten steps are shorter than 2000 characters; none hides a separate non-elementary lemma. I deliberately kept the elementary arguments in the item instead of creating nodes for polynomial identities or lattice-coordinate calculations.

## Not duplicates

No new nodes are introduced. The existing normalizer, character-antiduality and chamber results were reused. Whole-DAG concept searches and blueprint_refs searches for reflection, chamber, signed and reflection orbit found no existing blueprint statement of this item. The root-system and reductive-group nodes examined either assume reductivity or assume a root pairing and therefore cannot replace the argument above.

## Unfinished work

No mathematical part of this one-level split remains. Delivery checks and the push are recorded below when completed.
