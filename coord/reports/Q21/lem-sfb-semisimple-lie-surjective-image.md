# Stage-1 report: lem-sfb-semisimple-lie-surjective-image

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semisimple-lie-surjective-image.json: item, statement, split; its statement and stmt_deps are unchanged. Preserved the original source, creation record, blueprint provenance and historical searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-semisimple-lie-ideal-complement.json: new statement, Mathlib leaf. Every ideal in a finite-dimensional characteristic-zero Lie algebra with no nonzero solvable ideals has a complementary Lie ideal.
- citations.json: one verbatim statement quotation for each node cited in each of the four proof steps.
- report.md: this report. searches.jsonl is the search command's untouched log.

## Attachments

None. Searched lean/WeilConjectures by the item tag and by semisimplicity, HasTrivialRadical, surjectivity, and Lie-ideal complements. The existing project declarations on radicals, Cartan's criterion and the quotient by the centre do not state this general image result. In particular, the internal use of isCompl_killingCompl inside centre_sup_derivedSeries_eq_top is not an exported project complement theorem. Mathlib itself supplies the new leaf, not an ATTACH for the item.

## WANTED

None. Milne's Algebraic Groups (2017) is already present; no source was downloaded and no SGA source is used.

## What needed repair

The item was statement-only, with no proof. Its statement is true as written: the zero-radical notion of semisimplicity is the one in the source and in def-wf-semisimple-lie-algebra. No statement correction or dispute was necessary. The sentence in Milne about a kernel's complementary semisimple subalgebra is not by itself a fully cited split. I exposed the stronger precise ideal-complement input and supplied the remaining ideal and derived-series argument instead of leaving 'semisimplicity transports' unexplained.

The nearest-blueprint-ancestor command reports null, matching the live item's existing blueprint.from.node. I retained that null and the entire via chain, and supplied the new node's via by prepending this item. I read the latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The Lie-algebra result is an existing supporting prerequisite below the alteration/reductivity/Casimir chain in from.place, not a new route for a unit step. The current blueprint contains no additional node asserting the ideal-complement result. No chapter or unit file changed.

## Not duplicates

lem-sfb-semisimple-lie-ideal-complement vs lem-sfb-semisimple-lie-surjective-image: the new leaf constructs a complement to an arbitrary ideal; it neither mentions a surjection nor concludes absence of solvable ideals in its codomain. The item uses it and carries the inverse-image ideal argument itself.

lem-sfb-semisimple-lie-ideal-complement vs lem-ag-killing-nondegenerate: that node asserts nondegeneracy of the Killing form over Qbar_l, not complementary ideals over every characteristic-zero field. Its statement cannot supply this item as written over arbitrary F.

lem-sfb-semisimple-lie-ideal-complement vs sk-lem-walg-killing: that blueprint node supplies nondegeneracy/perfectness, not the ideal complement assertion.

lem-sfb-semisimple-lie-ideal-complement vs lem-ag-central-radical-quotient: that node concerns L/Z(L) and the sum Z(L)+[L,L] under central radical over Qbar_l. It gives no complement for a general ideal.

lem-sfb-semisimple-lie-ideal-complement vs lem-ag-faithful-semisimple-lie-central-radical: that node gives a central radical and a centre/derived-subalgebra sum for a faithful semisimple representation. It does not complement arbitrary ideals in zero-radical Lie algebras.

The whole-DAG searches examined statement fields, not just filenames or proof text; whole-blueprint searches included 'semisimple Lie', 'ideal complement', 'complement', 'Killing', and 'solvability'. No Stacks tag is applicable to the Lie-theoretic source, so there is no shared-tag pair to distinguish.

## Mathlib evidence

The item's executed semantic searches returned descent of solvability/nilpotence and associative-module semisimplicity, not Lie zero-radical descent; Loogle for HasTrivialRadical returned definitions and zero-solvable-ideal criteria. These were read and not misclassified as matches. Its historical searches were retained, with fresh searches appended.

For the new leaf the first semantic phrasing found atomic-ideal orthogonality results; the second phrasing found killingCompl and its membership API. I did not treat atomic-ideal results as applying to arbitrary ideals. Loogle for LieIdeal.isCompl_killingCompl gave the exact arbitrary-ideal theorem. The logged source grep located Killing.lean:142-143, CartanCriterion.lean:258-259 and Semisimple/Basic.lean:63-69. I read these sources and their surrounding variable hypotheses, notably CartanCriterion.lean:49 and :198. The required IsKilling instance is HasTrivialRadical.instIsKilling. Over a field, finite dimensionality supplies the required freeness and Noetherian hypotheses. def-wf-semisimple-lie-algebra already identifies the source predicate with HasTrivialRadical by the precise no-solvable-ideals criterion. Thus choosing J=I.killingCompl is a one-line specialization with inferred instances, as allowed for Mathlib leaves; no comparison theorem or extra mathematical hypothesis is hidden in the match. LeanSearch and both LeanFinder phrasings were available; all records describe actual returned hits. The new leaf has no proof, proof dependencies, or proof sketch in its statement.

## Review by Q21

I read Milne §22c, printed p.475 (PDF p.487), including the characteristic-zero and finite-dimensional conventions at the section opening and the last paragraph under The Casimir operator. That paragraph supplies the ideal-decomposition route for the item and its new prerequisite. I also read the exact Mathlib sources above for the new leaf, rather than relying on the semantic-search descriptions. I read the complete statements of def-wf-lie-algebra and def-wf-semisimple-lie-algebra and the new complement node while checking each use. The former explicitly defines ideals, brackets of subspaces and the derived series; the latter explicitly defines the no-solvable-ideals predicate. These are the verbatim portions entered in citations.json.

Step 1 uses the Lie-algebra definition to check directly that ker(q) is an ideal, then the complementary-ideal leaf. F is a characteristic-zero field and L is finite-dimensional and has no nonzero solvable ideal, so every hypothesis of the leaf is present. It returns an ideal J, not merely a vector-space complement; that distinction is needed later.

Step 2 uses only the ideal and bracket definitions. I checked injectivity using J intersect ker(q)=0 and surjectivity by decomposing a lift in ker(q)+J. The commuting assertion is justified because each [i,j] lies in both ideals, using skew-symmetry in the membership in I. No assertion that an arbitrary ideal in an ideal remains an ambient ideal is assumed.

Step 3 uses the same definitions to check the ambient-ideal condition for B explicitly. Its vector-space closure follows from linearity and A being a subspace. Its bracket closure in L uses both q preserving brackets and J being an ambient ideal; the decomposition and [I,J]=0 from step 2 give the displayed formula. Thus B really is an ideal of L, where the hypothesis can be applied.

Step 4 uses the derived-series definition from def-wf-lie-algebra and the final definition of semisimplicity. I wrote the base and successor of the inclusion q(D^r B) subset D^r A. The successor is just linearity on bracket spans. Vanishing in A implies vanishing in B because the restriction to J is injective. Hence the item hypothesis kills B. Surjectivity of the restriction then kills every element of A. These elementary span calculations are part of the proof, not additional helper nodes. Every step is below 2000 characters; the whole proof is below 3000 characters.

I tested L=H=0, the zero codomain with I=L and J=0, the identity map with I=0 and J=L, and the projection sl_2(F) direct-sum sl_2(F) onto a factor. All ideal and solvability claims work without assuming a nonzero algebra or an algebraically closed field. An abelian nonzero L does not meet the zero-solvable-ideal hypothesis, so it is not an omitted counterexample. Positive characteristic is excluded, as required by the inferred Cartan-criterion instance. I checked B1-B9 (self-contained statement-only new leaf, definitions, TeX, real search records, match lines, blueprint provenance), C1-C8 (precise citations, no hidden external theorem or new cycle, leaf tool), D1-D5 (the child is a genuine ideal-splitting tool and the item retains its argument), and E1-E7 (all hypotheses and objects, explicit derived-series calculation). No source error was found. No unfinished proof obligation remains in this one-level split.

## Unfinished work

None for this stage-1 item. The first dry run required an explicit mathlib_match.line field in addition to the lines already recorded in how. Added line 142, verified in the pinned source. The next dry run and direct delivery follow this review.
