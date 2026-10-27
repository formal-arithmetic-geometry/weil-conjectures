# Q95 stage-1 report: lem-sfb-rational-fixed-section-jets

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-rational-fixed-section-jets.json: statement split into eight explicit steps; Mathlib searches found no exact declaration or one-line specialization.
- citations.json: one verbatim statement quotation for every citation in every step.
- report.md: this report. No new DAG nodes, no Mathlib leaves.

## Attachments

None. Searched the live project's WeilConjectures source for the blueprint id and rational actions, jet actions, fixed sections, and truncated local rings. The matches concern unrelated cohomology comparisons or Frobenius; none proves this item. Upstream sorry declarations were not used as completed proofs. No Lean was written or compiled.

## WANTED

WANTED: Milne (2013), arXiv:1311.6060v2, Proposition 4.1, final paragraph, for lem-sfb-rational-fixed-section-jets. The 2017 book's Proposition 8.25 explicitly refers to this argument but does not provide it. The existing item's source already records this missing article. No download or repository literature edit was made; the missing details are supplied by the agent and the proof_origin is marked accordingly.

## Corrections and source scope

No mathematical assertion or hypothesis was changed. Inherited TeX contained doubled backslashes in the decoded statement; these were normalized to single TeX escapes. The source field and every other maintainer-owned field were retained.

Read Milne, Algebraic Groups (2017), Chapter 8, printed pp.148–155, particularly Proposition 8.9 (p.150) and Proposition 8.25 and its rational-action discussion (p.154). The former assumes a global action, so it cannot simply be applied to the present item. Its errata also require reducedness in the later kernel-detection argument. Here X is integral and we use only the finite-jet construction, not its faithfulness conclusion. Steps 2–6 explicitly supply the local-to-section extension and the open isomorphism; they are agent arguments, not claims quoted from the book. No SGA source is used.

Read the chapter and unit records and the current latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and proof. This created auxiliary algebraic-group item has no blueprint ancestor: the ancestor command returns None. Its existing provenance to the Milne argument and same_as=[] were retained. Blueprint searches for rational action and fixed point found no equivalent item. No chapter/unit route was changed.

## Review by Q95

I read delivery-errors B–E in both copies of the document and checked the proof against their content requirements. There are no new statement-only nodes to audit, no new duplicate pairs, and no hidden transfer of a clause into a new node. The only substantial new work is carried directly by steps 2–6. Each step is shorter than 2000 characters. Existing general statements suffice; their proofs or private constructions are never used as interfaces.

Step 1 uses lem-sfb-rational-point-thickenings-base-change: its statement gives exactly the closed section, nonzero finite-dimensional quotients, ideal-power description, arbitrary scheme base change, and surjective transition maps needed here. Its hypotheses do not require smoothness of X. I also read Stacks more-morphisms.tex, Tags 04EY and 04EZ, in particular the n-th-order universal property and the proof's ideal-power factorization. This avoids confusing set-theoretic support with factorization through a closed subscheme.

Step 2 uses the integral-scheme definition to obtain the domains A on affine charts, and lemma-nagata-ext-scheme-theoretically-dominant-separated for equality of maps to separated X. The requisite scheme-theoretic density is proved in the step, not assumed from topological density: tensoring A -> A_f with a k-vector space is a direct sum of injective maps. This calculation works for arbitrary B, including nilpotents. It also proves agreement on overlaps of rational representatives and makes G x Y a domain of the maximal representative. I read Stacks morphisms.tex, lemma-rational-map-from-reduced-to-separated (0A1Y), its equalizer proof, and schemes.tex, lemma-where-are-they-equal (01KM). The proof uses the stronger schematic-density interface of the cited existing node, rather than asserting products are reduced without justification.

Step 3 uses the actual statements of lem-weil-pbc-smooth-scheme-over-field-regular and lem-sc-regular-connected-integral. G is smooth, connected, and nonempty because of its identity, so both apply. Only G, not X, is made regular. lem-pc-rational-points-dense applies to the nonempty smooth open V intersect gV^{-1}; k algebraically closed implies separably closed. Translations and inversion are morphisms and inverse isomorphisms directly from the group definition. Thus the chosen factorization g=uv exists without assuming G affine.

Step 4 is the explicit continuation argument. The composite f_u(alpha(u^{-1}h,x)) is defined on an open containing (g,P), since both u and v lie in V and both send P to P. It agrees with the original action on Y; step 2 and the cited separated-equality statement justify its gluing as a representative. This proves regularity at every rational section point, but rational density alone would not show V=G. I therefore cited lem-sc-lft-over-field-jacobson-space, whose statement gives closed points dense in every closed subset, and lem-kun-closed-point-field, whose clause (a) makes their residue fields finite over k. Algebraic closedness makes such a residue field k. These statements justify the closed-complement argument. Once V=G, the stipulated fixed-section morphism equality itself supplies the scheme equality, so no unsupported deduction from pointwise equality on nonreduced bases is involved.

Step 5 constructs both open domains N and M and their mutually inverse maps, rather than merely saying the local action is invertible. The separated-equality node applies over base G and the same schematic-density calculation proves the inverse equations. The ideal-sheaf definition says the section ideal is the kernel of restriction, so the isomorphism fixing the section identifies this ideal and all powers by def-sbc-ideal-sheaf-powers. This is a direct kernel calculation, not a theorem about formal smoothness or a smoothness assumption on X.

Step 6 uses the thickening node again for support, powers, and the schemes G x X_n. Topological support is used only to enter open domains. Factorization through X_n uses the ideal-power preservation proved in step 5. The multiplication identity is compared on its actual open domain containing G x G x {P}, where both composites are defined. It therefore restricts to the whole thickening. Closed immersion uniqueness follows on affines from quotient surjectivity. There is no unsupported restriction of a rational identity to a nilpotent thickening.

Step 7 uses the affine-adjunction statement, the explicit GL coordinate-ring definition (which requires positive dimension, provided by the nonzero quotient), and precisely the fully faithful form of Yoneda: both functors are representable, so no general Hom(h_A,F)=F(A) assertion is taken from that citation. The construction is on all k-schemes T; on affine charts its pullbacks are algebra automorphisms and give invertible matrices, and the charts glue. I checked the inversion convention explicitly: contravariance reverses c_{h'^{-1}} c_{h^{-1}}, giving T_{hh'}=T_h T_{h'}. Arbitrary B-point algebra automorphisms follow from actual scheme automorphisms over B, not only k-point linearity.

Step 8 uses the thickening node's compatible surjections and lem-sc-kernel-subgroup's closed subgroup and algebra-point kernel assertions. The target GL is separated and affine. Finite type of the closed kernel is proved on affine charts by quotienting finitely generated k-algebras. Inclusion of kernels is tested on every B, then on the universal affine-chart points of K_{n+1}; this yields a scheme factorization, not just an inclusion of k-points. The statement of lem-weil-pbc-closed-immersion-factor-ideal-inclusion expressly says that such a factorization is a closed immersion. All quoted statements were opened and read; citations.json quotes them verbatim in full so the intended scope is reviewable.

Edge cases: for X=Spec k with the trivial action, every Q_n=k, every representation is trivial, and every K_n=G. The same argument allows singular integral X and trivial or nonfaithful actions. No step needs the maximal ideal to be nonzero. For the trivial smooth connected group the factorization argument and every jet still work. The n=1 quotient and every transition use n+1 exactly as stated. Nonreduced coefficient algebras B are covered by the tensor-injection argument and the ideal-kernel calculations. The proof never assumes smoothness of a kernel, X, or GL-equivariant quotients beyond what is stated.

Generic off-unit inputs are declared as tool_uses in split_report. They provide local algebraic geometry and representability, not a replacement for a step of the six-functor unit.

## Not duplicates

No new nodes were created. In particular the existing global-action theorem lem-sfb-fixed-point-action-finite-jets was read but not applied: it requires smooth X and a global action, unlike this item. Its separate finite-thickening input was reused directly.

## Unfinished work

None in this one-level split. All dependencies are existing DAG nodes. Server dry-run and delivery results follow from the required delivery tool.
