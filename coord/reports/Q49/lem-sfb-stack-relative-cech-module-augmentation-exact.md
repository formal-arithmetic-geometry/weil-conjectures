# Q49: lem-sfb-stack-relative-cech-module-augmentation-exact

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stack-relative-cech-module-augmentation-exact.json: item, statement unchanged, five-step split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-cech-base-change.json: new statement-only lemma, Stacks 06XC; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-split-fibred-cech-contraction.json: new statement-only lemma, Stacks 06XA and 06X6; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-fibred-cover-detects-exactness.json: new statement-only lemma, Stacks 06XD; no Mathlib match.
- citations.json: seven verbatim citation entries covering all node uses of the five steps.

## Attachments

None. Searched the project WeilConjectures source for the exact blueprint tag, relative Cech terms, Cech augmentation and fibred-groupoid terms. PresheafCechSheafAugmentationExact.lean:311 proves a free-abelian presheaf-nerve chain resolution at the augmentation. It is not this sheaf-valued cochain resolution of arbitrary structure modules on arbitrary fibred groupoids. The other injective/alternating Cech declarations concern scheme covers or injective coefficients, so none supplies every clause of this item.

## Wanted

None. Read literature/stacks-project/stacks-sheaves.tex, section-modules and the relative Cech section, specifically 06X6, 06XA, 06XB, 06XC, 06XD and 06XE. Confirmed tag-to-label mappings against tags/tags. Read the latest blueprint sk-thm-sf-ctf-stability-direct-images.proof.md, especially paragraph (3), alongside the chapter and unit records. The inherited blueprint ancestor is null: blueprint_refs.py ancestor reports None. This is retained rather than inventing a blueprint id.

## Problems found and changes

The imported item had a statement and searches but no proof. Its scope is correct: arbitrary categories fibred in groupoids, their big etale sites and arbitrary module sheaves. The phrase pullback means precomposition, not tensor pullback to a small etale site. I retained all hypotheses, statement dependencies and the original search records. No STATEMENT-DISPUTED correction is needed.

The proof follows the three separate inputs cited in 06XE, rather than introducing a new node which restates 06XE or its module conclusion. Base change identifies whole augmented complexes and their face maps, and also explicitly gives the induced derived isomorphism; it is not a collection of unsupported cohomology-degree identifications. The contraction is the strictly easier split-morphism result, without local covering, and exactness detection is a general result for three arbitrary sheaves, independent of Cech complexes.

## Not duplicates

lem-sfb-relative-cech-base-change vs lem-sfb-stack-relative-cech-module-augmentation-exact: base change needs no covering and identifies two augmented abelian-sheaf complexes; the item asserts exactness of one module complex under a covering hypothesis.
lem-sfb-split-fibred-cech-contraction vs lem-weil-pbc-set-cech-nerve-free-resolution: the existing node resolves free modules on sets; the new node contracts a sheaf-valued cochain complex from a 2-section of a fibred-groupoid functor.
lem-sfb-split-fibred-cech-contraction vs lem-sfb-stack-relative-cech-module-augmentation-exact: the new lemma requires a global 2-section and produces an explicit chain homotopy; the item assumes only local essential surjectivity and proves exactness.
lem-sfb-fibred-cover-detects-exactness vs lem-sfb-stack-qcoh-flat-atlas-exactness: the existing node requires algebraic stacks, flat scheme tests and quasi-coherent modules on fppf sites; the new lemma concerns arbitrary abelian sheaves on arbitrary fibred-groupoid etale sites.
lem-sfb-fibred-cover-detects-exactness vs lem-sfb-stack-smooth-qcoh-exact: smooth tensor pullback of quasi-coherent modules is different from reflection of exactness by precomposition on big fibred-groupoid sites.

Whole-DAG searches for 06XA, 06X6, 06XC, 06XD and the source labels found no pre-existing versions of the three supporting lemmas. Blueprint searches for those tags and relative Cech, 2-isomorphic, homotopy and contracting found no duplicate. A search for exactness and section also checked the broader imported blueprint. No same-tag existing-node pair was found. The project source likewise has no declaration for these supporting facts.

## Mathlib searches

All new recorded searches are exact queries run through the required msearch.py command, and their actual results are in searches.jsonl. Each new lemma has LeanSearch, LeanFinder (including a second phrasing), Loogle and grep records. The item has fresh semantic exactness searches in addition to its inherited records. No service outage was reported.

Read ExtraDegeneracy.lean:329-442, CechNerve.lean:77-92 and Abelian/Exact.lean:195-231. The most plausible hits are Arrow.AugmentedCechNerve.extraDegeneracy and SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv. They assume an ordinary categorical split epi and its ordinary wide-pullback nerve. Our statement requires a 2-section of a fibred-groupoid functor, its 2-fibre-product nerve and sheaf-valued section functors; comparing those models is additional work, not a one-line specialization. Similarly Functor.reflects_exact_of_faithful does not prove that this particular precomposition functor is faithful; that is precisely where the local covering condition is needed. TopCat.Sheaf.exact_iff_stalkFunctor_map_exact concerns a topological-space site. Ordinary Cech nerve map functoriality does not supply arbitrary 2-cartesian relative base change.

## Review by Q49

I checked delivery-errors B through E against all four node files and the sources, not just the schema. Each new node introduces its scheme, universes, categories, topology, coefficient sheaf, functors and extra hypotheses. They contain no proof steps or hidden proof sketches. Their only content beyond definitions is their own lemma. Their sources are the correct Stacks labels and tags, and no SGA source is used.

For step 1 I read def-weil-sheaf-of-modules-category in full. It gives the semilinear restriction rule and the linearity of module morphisms. The base-change node defines E and the global-section formula, so the named complex is unambiguous. The step spells out the module action and why compatible families glue, rather than assuming an algebraic-stack direct-image comparison or quasi-coherence. The covering pulls back on underlying schemes, and all coefficients come by restriction from T; thus no cartesian-module property is needed. Its elementary label concerns only this direct compatible-family construction.

For step 2 the base-change statement supplies an isomorphism of the augmented complexes, with the degree -1 identity, every face and naturality, exactly the clauses the step uses. The substitution is e=u and g the first projection of U x_X U; it is 2-cartesian by construction. I wrote the cancellation of the two-face terms and the augmented zero composite explicitly.

For step 3 the moduli-groupoids definition genuinely includes general fibred categories and the objects and arrow equation of a 2-fibre product; it is not being used for any theorem about stable curves. That equation proves the diagonal is a functor and g composed with it is the identity. The contraction node states the h^0 identity as well as dh+hd=1, so it covers injectivity at the augmentation and all positive positions. A cycle is d(h(c)) and an augmented element killed by d is zero; the argument is written in the step. No claim that u itself has a global section is made.

For step 4 the exactness-detection node states reflection at the middle term for any three sheaves, expressly permitting a zero first term. Its hypothesis is precisely the local lifting assumption of the item, with etale rather than fppf coverings. Applying it to each triple uses no faithful-functor assumption. In particular the initial monomorphism is covered; exactness is in sheaves, not a claim of global sectionwise exactness on X.

For step 5 the module-category definition states kernels are sectionwise and cokernels are sheafifications of sectionwise cokernels. The quotient action and its restrictions show why forgetting the module action gives the same abelian kernel and cokernel. This is a few-line construction from that cited statement, so it is elementary and has no separate node. Naturality is checked entry by entry on compatible families, hence on each face and the signed differential. The citation quotes are literal substrings of these statements; I corrected the step-1 quote to cover the definition of E as well as the base-change theorem.

Small cases: u=id gives the standard augmented constant cosimplicial complex (alternating differentials 0,1,0,1); p=0 uses exactly two faces, and the initial triple is 0,F,E^0. M=0 gives zero terms. Empty sites and schemes with empty covering families force zero sheaf sections where appropriate, and the argument still applies. Nonfaithful groupoid functors retain all isomorphisms in their 2-fibre products, so the diagonal section exists even with automorphisms; replacing the fibres by sets would be incorrect. The new contraction lemma has the identity and empty cases, the base-change lemma allows e=id and arbitrary e, and detection needs local covering, not global essential surjectivity. All five proof steps are below 2000 characters. The only cross-unit proof dependency is the generic module-category definition, declared as a tool in split_report.

## Unfinished work

No stage-1 argument is left unresolved. The three supporting statement-only lemmas join the normal queue; they are intentionally not split in this delivery. No Lean file was written and no compiler, Lake or build command was run.
