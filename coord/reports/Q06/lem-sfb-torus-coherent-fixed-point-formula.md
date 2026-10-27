# Q06: lem-sfb-torus-coherent-fixed-point-formula

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-torus-coherent-fixed-point-formula.json: item, split, statement unchanged; six assembly steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-coherent-proper-pushforward.json: statement, unsplit, no Mathlib match. Proper pushforward on coherent equivariant Grothendieck groups, including rational linearizations, composition and subgroup restriction.
- dag/nodes/sec-six-functors-basics/lem-sfb-torus-coherent-concentration.json: statement, unsplit, no Mathlib match. Integral concentration for smooth projective torus schemes; not the Euler-character formula.
- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-regular-self-intersection.json: statement, unsplit, no Mathlib match. General regular-immersion alternating Tor operation and self-intersection; no fixed-point hypothesis or numerical Euler-character conclusion.
- citations.json: verbatim statement quotations for each citation in each numbered proof step.

The three new nodes contain statements only, no proof or proof dependencies. No Lean was written or compiled. All files were written in the assigned sandbox; the shared repository and launcher were read only. There was no earlier split or search log to recover.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and coherent fixed-point, torus, equivariant Grothendieck, concentration and self-intersection terminology. Its existing fixed-point declarations concern Frobenius, finite-group representations or invariant rings, not the item. Mathlib's Algebra.GrothendieckGroup is commutative-monoid group completion, not the coherent-sheaf exact-sequence group: read Mathlib/GroupTheory/MonoidLocalization/GrothendieckGroup.lean, lines 11--20 and 30--47. FDRep.character is a field-valued trace character, not the integral formal weight character. None supplies an attachment or a Mathlib leaf here.

## WANTED

WANTED: Nielsen (1974), general algebraic fixed-point theorem, and Iversen (1976), section 9.4, for the general fixed-point input cited by Milne Theorem 22.50.

WANTED: R. W. Thomason, Une formule de Lefschetz en K-theorie equivariante algebrique, Duke Math. J. 53 (1986), concentration theorem, equivariant coherent proper pushforward and regular-immersion self-intersection, for the three new nodes. This work is not in literature/; it has not been downloaded. The source fields explicitly distinguish the available Milne pointer from these missing proofs.

## What was wrong or incomplete

The item was a statement-only generalization supplied by an earlier agent, rather than an actual split of Milne's one-sentence fixed-point reference. Milne Theorem 22.50 states the flag line-bundle alternating character formula and refers to Nielsen and Iversen; it does not prove the general integral formula. Example 22.36 does explicitly identify the torus representation Grothendieck group with the integral character ring. I retained the item statement, supplied an agent-written assembly proof and isolated the three genuine equivariant coherent-theory prerequisites. No claim is made that Milne proves concentration or self-intersection.

A proof by evaluation on ordinary torus elements would lose integral information in positive characteristic. A dense cyclic subgroup also need not exist over the algebraic closure of a finite field. The delivered proof uses neither argument: concentration is over the integer representation ring, and the scheme-theoretic fixed functor is used for tangent spaces.

## Not duplicates

lem-sfb-equivariant-coherent-proper-pushforward vs lem-sfb-flag-cohomology-finite-exact: the latter is about homogeneous bundles on a semisimple simply connected flag variety in positive characteristic; it supplies neither general equivariant proper pushforward nor its composition law.

lem-sfb-equivariant-coherent-proper-pushforward vs lem-pc-coherent-hi: ordinary coherent higher-image finiteness does not assert rational group-scheme linearizations, equivariant Grothendieck maps, or compatibility with restriction of the group.

lem-sfb-equivariant-coherent-proper-pushforward vs lem-pc-euler-characteristic-well-defined: the latter gives finite-dimensional bounded ordinary cohomology over a field, without equivariant higher images or their pushforward laws.

lem-sfb-torus-coherent-concentration vs lem-sfb-torus-coherent-fixed-point-formula: concentration is an isomorphism between coherent Grothendieck modules, even with positive-dimensional fixed schemes, and has no cohomological character formula. The item still computes the inverse on a vector bundle using the independent self-intersection identity and then pushes to a point.

lem-sfb-equivariant-regular-self-intersection vs lem-sfb-smooth-section-regular-immersion: the latter supplies regular local equations for a smooth section, not Tor operations or a coherent self-intersection identity.

lem-sfb-equivariant-regular-self-intersection vs lem-pur-smooth-pair-regular-immersion: smooth-pair regular equations are geometric input, not the equivariant alternating Tor computation.

lem-sfb-equivariant-regular-self-intersection vs lem-per-regular-lci-geometric-calculus: this supplies regular-immersion permanence and dimension calculus; it contains no equivariant coherent Grothendieck statement.

DAG/blueprint searches included equivariant, equivariant coherent, Grothendieck group, self-intersection, concentration, formal character, linearized, conormal and weight decomposition. Opened and read the likely existing statements listed above, as well as torus-fixed-local-ideal-jets and torus-fixed-scheme-smooth: neither applies to the needed general projective conormal calculation directly, so neither is cited for it. The existing G_m weight-basis statement is reused, not recreated. The three new ids were searched throughout DAG, latest blueprint and project Lean source before writing. The ancestor command returns None, consistent with the imported supporting chain; the new nodes retain that null ancestor and extend the via list through the item.

## Review by Q06

I read Milne Example 22.36 (printed pp.473--474) and the paragraph and proof of Theorem 22.50 (p.480), using a text extraction in the sandbox. Example 22.36 uses integer multiplicities; the proof of 22.50 really is only a pointer to the absent general fixed-point theorem. For each new node I read that available source pointer and explicitly marked the unavailable Thomason input rather than pretending to have read it. For ordinary background to the pushforward prerequisite I also read Stacks coherent.tex, lemma-flat-base-change-cohomology (02KH), and lemma-proper-over-affine-cohomology-finite (02O6). Those prove the ordinary base-change and finiteness ingredients only; the new statement is the equivariant construction and functoriality. For the self-intersection input the intended local calculation is the Koszul resolution of a regular sequence: after tensoring with a module on the closed subscheme the differentials vanish, leaving its tensors with exterior powers of I/I^2. The Tor operation is needed because ordinary restriction is not exact. These descriptions are guidance for future workers, not proofs smuggled into the statement-only nodes.

Step 1 cites lem-pc-projective-proper for exactly projective implies proper, then the new equivariant proper-pushforward statement for rational finite-dimensional H-actions, boundedness, its alternating class, and restriction to T. I checked its separated finite-type hypotheses: projectivity over a field gives them, the given bundle has finite local rank, and the structure morphism is H-equivariant to the trivial action on the point. The group H may be nonreduced: the new input is formulated for affine finite-type group schemes and uses coactions, not only H(F)-actions. This is the one off-unit tool use (projective implies proper), declared in split_report, not added to maintainer-owned tool_uses.

Step 2 cites the existing G_m weight-basis lemma. Its statement explicitly gives the coaction weight decomposition over every field, with finite support, and includes dimension zero. Applying it to successive commuting factors preserves all earlier weight spaces. The Laurent-coefficient calculation identifies all group-scheme characters, exact sequences are exact weight by weight, and tensor products add weights. This proves the integral R(T)=Z[X] identification, rather than using field trace characters. The finite disjoint-union decomposition of sheaves proves the tuple description on P directly. It is not delegated to a new node.

Step 3 proves the tangent fixed-subspace identification directly from the dual-number definition and the universal fixed-functor quantifier. The hypothesis P is reduced and zero-dimensional is essential: without it T_pP could be nonzero. The weight-zero subspace is the invariant subspace by step 2, and dualizing reverses weights. There is no reliance on an affine invariant neighbourhood or on smoothness of fixed schemes.

Step 4 cites the existing smooth-section regular-immersion lemma. Every p is a section of Z over F. Its local regular equations remain equations for the union P after removing the other finitely many closed points; the ranks are bounded because P is finite. The conormal at p is m_p/m_p^2 by definition, with action dual to the geometric derivative (pullback of local functions by the inverse group element). This is the cotangent convention of the item, not its negative. Wedges in a weight basis give the product D_p by a finite subset expansion. This is elementary from steps 2--3 and the cited regular-equation statement; it does not conceal an equivariant localization assertion.

Step 5 cites the new concentration statement only for existence of a preimage beta, then the new regular self-intersection statement for i^!i_* beta and i^![E]=[i^*E]. Both clauses are explicitly in its statement. The immersion is regular by step 4, of bounded length, and E is locally free, so these hypotheses match. The maps are representation-linear, so extend to the same localization. Taking components gives an ordinary scalar equation D_p beta_p=ch(E_p); invertibility was proved in step 4, so division is valid. Concentration alone is not being used as the final formula.

Step 6 uses the proper-pushforward composition law stated by the new node, and its formula at a point. On P the structure map is the finite sum of identity maps of Spec F, explaining the summation with no omitted degree factors. The item is thus assembled from three independent structural inputs; no new node restates its conclusion or one of its numerical clauses.

I checked empty Z, empty P, rank-zero bundles, rank-zero torus, and dimension zero. For r=0 the fixed scheme is all of Z, so the hypotheses force Z=P and every conormal has rank zero: all denominators are 1. For empty P concentration yields zero after localization, agreeing with the empty sum. On P^1 with t acting as [x:y] -> [tx:y] and E=O, cotangent weights are -1 and +1, and 1/(1-e^{-1})+1/(1-e)=1, so the denominator sign gives the expected H^0 character. Affine A^1 with scalar action tests the self-intersection input: at 0 it gives the factor 1-e^{-1}, without any properness requirement. A fixed component of positive dimension is allowed in concentration but deliberately not in the item. Characteristic p changes none of the Laurent monomial or integer multiplicity calculations.

Every proof-step citation has its actual cited statement in citations.json; no proof text is quoted instead. Every non-elementary step is marked false and cites the relevant theorem statement. The elementary dual-number and wedge calculations are written out. No step is longer than 2000 characters. Every new statement introduces its own objects, defines its equivariant group and representation-ring conventions inline, cites all bracketed definition ids, has no proof sketch in the statement, and is not split recursively. Searches were run only with msearch.py, read before recording, and include a second semantic phrasing for each of the three new nodes. All returned signatures concern abstract representations, scalar invariants, ordinary pushforwards or exterior powers; none asserts the needed scheme-equivariant coherent result. There is no statement dispute, no weakened hypothesis/conclusion, and no prohibited SGA citation.

## Unfinished work

No part of this stage-1 split remains unfinished. The three named statement-only prerequisites remain for later stage-1 splitting, as required. Missing literature is recorded above; the assembly proof is explicitly agent-written. Independent maintainer review remains necessary.
