## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-torus-commuting-point-common-borel.json — statement, split into six steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-borel-conjugation-cover.json — new statement-only lemma, unsplit; no Mathlib match.
- citations.json — eleven records, one for each step/node pair; quotes copied verbatim from the actual statements.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, Borel, torus, common Borel, and commuting-torus terminology found no project declaration asserting this item. The matrix centralizer equations in GroupScheme/GeneralLinear/ClosedSubgroup/LieSubalgebra.lean do not give Borel containment. No Lean was written or compiled.

## WANTED

None. All mathematical sources used are present in literature/.

## Corrections and route

The statement is unchanged. There was no earlier sandbox split or report to preserve. The item has no repair-note file. The imported blueprint ancestry has from.node = null, with an explicit via chain and a precise place; blueprint_refs.py ancestor confirms null, and that inherited chain is retained. I read the latest blueprint (main-20261024), especially sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3), and the recorded chapter and unit. The lower algebraic-group input is part of the inherited alteration/moduli prerequisite, not a replacement of a unit step. This item is not the unit's key theorem, so no unit record was changed.

I deliberately did not cite lem-sfb-general-borel-flag-variety. Its proof uses lem-sfb-borel-scheme-normalizer, which uses lem-sfb-torus-centralizer-smooth-connected, whose proof cites this item. This would create a real cycle. Instead the split uses the independent represented quotient G/B and its kernel pair, which suffice without identifying a point stabilizer on the variety of Borel subgroups. The selected existing dependencies have no return path to the item.

## Not duplicates

lem-sfb-borel-conjugation-cover vs lem-sfb-general-borel-flag-variety: the latter constructs the flag variety with its scheme-theoretic stabilizers and torus-fixed points; it does not state that every rational element fixes a flag or belongs to a conjugate of a prescribed Borel. It also depends on the item through the normalizer theorem and cannot serve as its prerequisite.

lem-sfb-borel-conjugation-cover vs lem-sfb-borel-quotient-proper-geometry: properness and smoothness of G/B do not assert surjectivity of the conjugation map G(k) times B(k) to G(k). This is the independent density theorem of Milne 17.33(b).

lem-sfb-borel-conjugation-cover vs lem-sfb-borel-maximal-torus-conjugacy: the existing lemma concerns conjugacy of maximal tori and their occurrence in Borels, not conjugation coverage of arbitrary rational elements, including unipotent elements.

lem-sfb-borel-conjugation-cover vs lem-sfb-torus-commuting-point-common-borel: the auxiliary lemma concerns an arbitrary prescribed Borel and conjugation coverage, with no torus supplied. It does not produce a Borel containing a given torus. The substance of the item remains in constructing the c-fixed proper scheme, restricting the commuting torus action, applying the fixed point theorem, and checking subgroup-scheme containment on every algebra. The new node is the independent density-theorem input explicitly cited by the source, not the common-Borel conclusion renamed.

Before creating it I searched the whole DAG by Borel/conjugacy/coverage and by Milne 17.33 and 17.34, and searched the whole blueprint with blueprint_refs.py search Borel, 'Borel subgroup', 'conjugat', and '17.33'. No blueprint node states the new lemma. The broad numeric searches also return unrelated places; their statements were distinguished by their group-scheme hypotheses. No Stacks tag is used for the new lemma: its source is the explicitly located Milne theorem, not a changing section number.

## Mathlib searches

The actual search-command results are in searches.jsonl and are transcribed, without changing query text, into the appropriate mathlib_searches records. The item was searched by both natural-language services, Loogle and grep. The new conjugation-covering lemma was searched with two distinct semantic phrasings, LeanSearch, Loogle and whole-Mathlib grep. All these calls succeeded; none is recorded as unavailable. I read the returned signatures. Group.conjugatesOfSet, Group.subset_conjugatesOfSet and Group.conjugatesOfSet_mono only define conjugation saturation and elementary monotonicity; the source at Algebra/Group/Subgroup/Basic.lean:561–575 confirms that they do not say the saturation of a Borel is the whole group. LieAlgebra.Basis.borelUpper and borelLower at Algebra/Lie/Basis/Basic.lean:147,154 are Lie submodules. ConjClasses.mk_surjective maps to conjugacy classes rather than to an algebraic group from a Borel. Other hits concern arithmetic matrix conjugation, abstract centralizers, Galois categories and measurable Borel spaces. None states either node.

## Review by Q43

I read Milne, Algebraic Groups (2017), Lemma 17.37 and its full proof on printed p.363 for the item. For the one new lemma I read Definition 17.6 and the following existence sentence on pp.353–354, Theorem 17.33(b), its proof, and Corollary 17.34 on p.362. The eventual split of the new lemma should retain the density proof: conjugates of the identity centralizer of a maximal torus contain a nonempty open subset by 17.33(a); that centralizer lies in a suitable Borel, and 17.32(a) plus properness of G/B makes the union of Borel conjugates closed; density makes it all of G. This is material for that node's later worker, not an extra proof hidden in its statement. Borel existence is the maximal-dimension argument immediately following 17.6. I also read 5.20–5.28 on pp.104–105, 7.11–7.15 on pp.141–142, 17.9 on p.354, 17.3 on p.353, and 12.14 and its following paragraph on p.236 to check the existing tools against the source.

For step 1 I opened lem-sfb-homogeneous-orbit-quotient-geometry and lem-sfb-borel-quotient-proper-geometry. The former states representability, faithful flatness, the all-algebra kernel-pair formula, and rational lifting; the latter applies to precisely that quotient with smooth connected closed H, and asserts properness when H is a Borel. B_0 satisfies all its hypotheses by the new lemma and the definition in the item. Left multiplication preserves right cosets, so descent of that explicit rule supplies the action from the represented fppf quotient; no normalizer theorem is being smuggled in.

For step 2 the new lemma states coverage for any prescribed B_0, rather than merely existence of some Borel containing c. Its formula c=g_0 b_0 g_0^{-1} gives the displayed fixed point q(g_0) immediately. This is the source's first nonemptiness argument, with the reference replaced by a cited node and the coset calculation written out.

For step 3 I opened def-weil-proper-morphism, lem-weil-pbc-closed-immersion-base-change, and lem-weil-pbc-closed-immersion-proper. The first defines separatedness by a closed diagonal and includes finite type in properness, the second makes its pullback closed, and the third explicitly states that a closed subscheme of a proper scheme is proper over the same base. Thus the constructed equalizer is proper and finite type. The equalizer definition works also for nonreduced test schemes. Nonemptiness comes from step 2; no fixed-locus representability theorem or reducedness assumption is omitted.

Step 4 has no black box: the explicit equality c_A(t y)=t(c_A y)=t y on every test algebra proves that the action factors through the equalizer. This verifies scheme-theoretic stability, including nilpotent test algebras. It is an elementary factorization through a fibre product, not a separate lemma.

For step 5 I opened lem-sfb-multiplicative-type-largest-subtorus and used exactly its sentence 'Every torus is smooth and connected.' I do not use any of its stronger subtorus conclusions. Commutativity follows from the given product-of-G_m presentation on every algebra, and its derived subgroup is therefore trivial. I opened lem-sfb-solvable-proper-fixed-point: it allows a nonempty proper finite-type scheme that need not be reduced or connected, exactly our Y, and returns a rational point fixed after every algebra extension. The acting group T is affine finite type, smooth, connected and solvable; maximality is never used. Rational lifting is explicitly a clause of lem-sfb-homogeneous-orbit-quotient-geometry, not an inference that arbitrary quotient points lift over the original field.

For step 6 the same kernel-pair formula converts equality q(tg_A)=q(g_A) to g_A^{-1}tg_A in B_0(A) on arbitrary k-algebras. This proves actual subgroup-scheme containment, not just an inclusion of k-points. The c-equation needs only k-points. Conjugation preserves the Borel property because it is a group-scheme isomorphism and transports every putative larger smooth connected solvable subgroup back to one containing B_0. This elementary verification supplies the maximality clause explicitly.

I checked B–E of delivery-errors against each written node and step: the new node is self-contained, statement-only, has all definition dependencies, precise source, genuine logged searches and filled blueprint fields. Every non-elementary input in the six-step proof is a cited statement, read above; citations.json gives the exact text used. Foundational proper/closed-immersion tools from other units are declared in split_report.tool_uses. Each step is below 600 characters, so no long step conceals a separate comparison lemma. I checked the selected dependency closures for a return path and checked all citation quotations against the actual node statements.

Small cases: G=1, T=1, and G a torus give a one-point quotient or a trivial torus action and require no positive rank. For G=GL_2 with scalar T, arbitrary c (including a nontrivial Jordan unipotent) is covered by the new conjugation lemma and the torus action is trivial on the quotient. For a diagonal maximal torus the final calculation still works. Positive characteristic is unrestricted; the fixed scheme may be nonreduced, which the existing fixed point theorem permits. The new covering assertion holds also when G itself is solvable (then B=G and choose g=1), and says nothing false about every element lying in a fixed torus.

## Source error inherited, with no new statement change

Milne 17.37 calls the union over Borels containing T finite. For T=1 and G=GL_2 over an algebraically closed field there are infinitely many Borels (one for each line). The live item's statement already correctly omits that parenthesis and asks only for a common Borel for each c. I retain that correction and use neither finiteness nor maximality of T. No target or definition was changed.

## Unfinished work

The auxiliary Borel conjugation-covering lemma remains statement-only for a later stage-1 split, as required. No mathematical part of the item's assembly proof remains unwritten. Required server dry run and direct push are the final validation and delivery steps.
