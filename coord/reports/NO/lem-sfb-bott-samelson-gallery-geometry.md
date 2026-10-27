# Stage-1 delivery: lem-sfb-bott-samelson-gallery-geometry

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-bott-samelson-gallery-geometry.json — item, statement, split in six steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-minimal-parabolic-flag-projection.json — new statement-only input, unsplit; no Mathlib match. It describes the rank-one partial-flag projection and its coordinates, rather than an iterated gallery.
- citations.json — exact statement quotations for every proof-step citation.
- searches.jsonl — actual search-command output records. Existing item searches were retained; new searches and their results were read and recorded without changing their query text.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag, Bott–Samelson, galleries, minimal parabolics and partial flags found no declaration for this item. The corresponding notion searches in lean/Sheaf also found no finished result. No Lean was written and no compiler was run.

## Literature wanted

WANTED: Brion–Kumar, Frobenius Splitting Methods in Geometry and Representation Theory, Section 2.1, printed pp.62–63, and Section 2.2.1, printed pp.64–67, for the item and lem-sfb-minimal-parabolic-flag-projection. The author-hosted PDF https://www-fourier.univ-grenoble-alpes.fr/~mbrion/fbook.pdf was read online, including equations (1)–(8), diagram (D), the open-cell paragraph and the reduced-word paragraph, and the opening of 2.2 explicitly allowing characteristic zero in 2.2.1–2.2.2. No file was downloaded or added to literature. Because that PDF is absent locally, proof_origin.by is agent, with the current local blueprint route identified and the online source specified in the steps.

The Stacks source was read locally for Tags 01WE (morphisms-lemma-H-projective-composition), 01WF (morphisms-lemma-H-projective-base-change) and 01VA (morphisms-lemma-composition-smooth). Each fact is carried by its cited existing node. No SGA source is used.

## Corrections and scope

The imported statement had doubled TeX backslashes. These were normalized. The phrase “its image” immediately after the open-locus sentence was clarified to “the image of this open locus under mu_i”. This is Brion–Kumar's statement: the open gallery maps to the Bruhat cell for a reduced word. Reading that phrase as referring to all of Z would be false already for SL_2 and the one-letter word: Z is P^1 and its whole image is P^1, whereas the cell is A^1. The clarification preserves the intended clause and adds or removes no hypothesis.

The current latest blueprint's direct-images proof (3) was read, together with the chapter and unit records. The inherited chain serves its alteration/moduli/reductivity prerequisite, and the present split remains below that chain. The ancestor command returns None; the inherited null from.node and complete via chain were retained for the new node. Whole-blueprint searches for Bott Samelson, Bruhat, parabolic, minimal parabolic, rank-one projection, projective line fibration and flag found no equivalent imported node.

The general parabolic node lem-sfb-standard-parabolic-levi-charts was located and read. Its represented quotient and torsor are reused directly in steps 1 and 2, and in the new input's statement. The new node does not re-prove that general construction. The existing simple Bruhat double-coset product is reused for the reduced-word image; no new root-product, Coxeter or reduced-word lemma is introduced.

## Not duplicates

lem-sfb-minimal-parabolic-flag-projection vs lem-sfb-standard-parabolic-levi-charts: the existing statement supplies P_I, its Levi decomposition and the quotient torsor G to G/P_I for every I; it does not state that G/B to G/P_alpha is a smooth projective locally trivial P^1-fibration, nor its affine coordinate and coordinate action. The new statement explicitly takes the existing quotient/torsor as input.

lem-sfb-minimal-parabolic-flag-projection vs lem-sfb-minimal-parabolic-line-cohomology: the existing node concerns homogeneous line cohomology, uses the opposite Borel and assumes positive characteristic. The new input is the geometric partial-flag projection and its regular rank-one coordinates in every characteristic, including zero.

lem-sfb-minimal-parabolic-flag-projection vs lem-sfb-homogeneous-line-schubert-curve-degree: the existing statement identifies the reduced simple Schubert curve with SL_2/B_2 and computes the restriction of homogeneous line bundles. It does not provide the partial-flag projection or its local trivializations and quotient coordinate statements. No line-bundle degree is used here.

lem-sfb-minimal-parabolic-flag-projection vs lem-sfb-bott-samelson-gallery-geometry: the new input is the one-step homogeneous projection, a morphism with base G/P_alpha absent from the item. The item's proof constructs all iterates, checks the twisted B^m quotient by inverse formulas, proves integrality/projectivity, normalizes the open chart, computes its reduced-word image and proves the fixed-point recursion. None of those iterated arguments was moved into the new statement.

## Mathlib searches

For the new input I ran LeanFinder with two descriptions of the minimal-parabolic projection, LeanSearch with descriptions of its projective-line fibre and its invariant flags, Loogle for Parabolic and jointly for Smooth/IsProjective, and two source greps (the whole Mathlib tree for minimalParabolic/parabolicSubgroup/BorelSubgroup/flagVariety, and AlgebraicGeometry for flag/quotient/parabolic/Borel). The greps returned no corresponding scheme definitions. Semantic hits were topological trivializations, abstract projectivizations, root-pairing lemmas and order-theoretic Flag constructors. Loogle's parabolic hits were two-by-two matrices classified by their discriminant. None has the required group-scheme or quotient hypotheses/conclusion.

For the item I additionally searched its gallery and Bott–Samelson descriptions with LeanFinder and LeanSearch, Loogle Samelson, and a whole-source grep including Bruhat and Schubert. The two grep hits were a Bruhat–Tits-tree comment and the art-gallery problem, and the semantic hits were simplicial classifying spaces, topological bundles, Coxeter words and elementary quotient-group constructions. They do not construct gallery schemes or enumerate their torus-fixed points. The original item's recorded searches were also read and retained. There is no Mathlib leaf.

## Review by NO

I read Brion–Kumar 2.1 and 2.2.1 at the author-hosted source, checking the quotient action and cumulative-product map against (2)–(6), the affine normalization against the open-cell paragraph, and the forgetful projection against (8) and diagram (D). The new node isolates the preceding rank-one homogeneous input. Its hypotheses specify the same algebraically closed field, semisimple simply connected group, Borel and maximal torus, positive roots in B and simple negative root used to generate P. Its conclusions are valid without a reduced-word assumption and without a characteristic assumption. The character action uses characters as morphisms of group schemes, not their differentials.

Step 1 cites the existing standard-parabolic statement with I={alpha_i}; it really gives the generated subgroup and represented quotient. The new node gives precisely the smooth projective map and its local P^1 trivializations. The fibre-product definition states both existence and the universal property used to represent tuples of successive flags. The induction begins with Spec F and B, so no zero-length quotient is being tacitly discarded.

Step 2 takes the regular local sections of G to Q from the actual statement of lem-sfb-bruhat-longest-cell-charts. The equality of two images in G/P forces their quotient into P by the torsor identity explicitly stated in lem-sfb-standard-parabolic-levi-charts. The formulas p_j=g_(j-1)^(-1)g_j and p'_j=b_(j-1)^(-1)p_jb_j check both inverses and the exact twisting in the right action. They are valid over test schemes and compatible with refinements, so this is a quotient of fppf sheaves rather than only a bijection on rational points. B equivariance is checked on every cumulative flag, with the first flag based at B.

Step 3 uses exactly the smooth base-change clause of lem-pc-proper-base-change, the smooth-composition statement of lem-trf-smooth-composition, the full projective-base-change statement of lem-pc-projective-base-change and the H-projective-composition statement of lem-trf-h-projective-composition. These are generic tools; their role is declared in split_report.tool_uses. Quasi-compactness follows from the resulting projective-space embedding. Integrality is checked on actual affine trivializations: domains A[t] and their nonempty common open, and intersecting inverse images of nonempty base opens. The properness of Z comes from the projective-proper statement, Q is separated because the Borel-pair statement says it is proper, and the proper-to-separated-target triangle statement applies with base Spec F. This supplies the hypotheses of every cited general result without assuming projectivity of a Zariski P^1-fibration solely from local triviality.

Step 4 uses the new statement's scheme isomorphism A^1 times B onto the open double coset, including its regular inverse. Gauging from the first factor to the last is unique and regular and works for repeated letters. Openness follows on the explicit local quotient lifts. Nonemptiness and the integrality proved in step 3 give density. This is an elementary coordinate normalization once the stated rank-one chart is available, rather than an extra associated-bundle existence assertion hidden in the proof.

Step 5 cites the existing simple-double-coset statement, which explicitly includes the product formula for any nonempty reduced word, over every algebraically closed extension. I use its statement, not a stronger scheme isomorphism that it does not assert. The Bruhat-chart statement gives the reduced locally closed cells. Thus the asserted image is exactly the open-cell image; no birationality or isomorphism onto the cell is added. The empty reduced word is checked separately.

Step 6 uses the new rank-one chart statement and computes, rather than citing an unstated fixed-gallery theorem. A fixed prefix has a representative h normalizing T. Conjugation by h changes the root character by an automorphism, so it remains nontrivial. In the torus coordinate ring the nonzero Laurent polynomial chi-1 times a nonzero scalar cannot vanish. Consequently the chart contributes exactly its origin, and its complement contributes B. Distinct prefixes and the two distinct flags in one fibre prove the count by induction even when several galleries have the same endpoint. Fixedness is after arbitrary algebra extension as required; nothing is inferred about reducedness of the fixed subscheme.

I checked B1–B10, C1–C7, D1–D5 and E1–E7 against the actual node files and the source. In particular: the new node has a complete statement and no proof sketch or proof dependencies; all its non-inline notions have the stated definition dependencies; all Mathlib entries come from the actual command logs; every item citation has a verbatim statement quote; the general parabolic and double-coset inputs are reused; and generic off-unit tools are declared. No proof step exceeds 2000 characters, and none contains an unlabelled non-elementary comparison. The substantive new rank-one input remains an unsplit node, not an unsupported claim inside a proof step.

Small cases checked: m=0 (one gallery, one endpoint, A^0); SL_2 and m=1 (P^1, one affine open, two fixed flags); the nonreduced word (s,s) (four fixed galleries, with repeated endpoints allowed); rank zero (only the empty word); characteristic two (root character may have zero differential but remains a nontrivial Laurent monomial). The new input is vacuous in rank zero because it requires a simple root. All smooth/projective and fixed-point assertions use group-scheme rather than Lie-algebra characters, so no separability assumption was introduced.

## Unfinished work

The new rank-one projection input remains statement-only, as required for a one-level split. There is no unfinished step of the item relative to its cited statements. The local Brion–Kumar PDF remains wanted. The independent maintainer review is still required after delivery.
