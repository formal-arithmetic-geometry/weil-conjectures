# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-relative-tensor-localized-resolution-comparison.json: statement, split; no Mathlib match for the whole item. Its statement and statement dependencies are unchanged.
- citations.json: one exact statement quotation for every step/node pair.
- No new nodes, no new Mathlib leaves, no unit file changes. searches.jsonl records the searches run for this item. write_split.py is sandbox-only working material.

## Attachments

None. Searched the live lean/WeilConjectures tree for the exact blueprint tag, K-flat terminology, and tensor/localization terminology. Read KFlatModuleBaseChange.lean and KFlatLocalizedTensorComparisonNatural.lean; the former proves the existing scalar-extension dependency, while the latter concerns coefficient comparison on K-flat inputs. Neither states this item's simultaneous prime localization, augmentation, and two explicit chain formulas. The TorLocalizationDenominators results concern denominator control for Tor classes, not this chain isomorphism. No compiler was invoked.

## WANTED

None. The sources used are present under literature/stacks-project/.

## Corrections and scope

The item had an empty proof. There is no statement dispute and no correction to its mathematical statement. The proof now expands the localization identity in Stacks 0B67 (more-algebra-lemma-tor-amplitude-localization), with base ring renamed R and algebra renamed A. It does not infer chain formulas or a K-flat augmentation from a cohomology-only comparison.

Read the current literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md and its proof, and the chapter and unit records. This is a lower-level algebra tool on the recorded relative-duality branch of that ancestor; it neither reproves nor changes the contracting-correspondence step of the unit. The inherited blueprint.from chain and precise place are retained. Whole-blueprint searches for K-flat, localization tensor, simultaneous, and localized resolution found no blueprint node stating this item.

The generic off-unit input lem-pc-kflat-extension-of-scalars is declared in split_report.tool_uses: it supplies scalar extension of K-flatness for R to R_p; it does not replace a geometric unit step. Other proof theorems used here are already Mathlib leaves. I did not set the maintainer's tool_uses field.

## Mathlib and DAG searches

Reused the inherited search history without changing its queries or verdicts. Also ran the required msearch.py commands for Q138, all logged in searches.jsonl: LeanFinder with two phrasings, Loogle `IsLocalization, CochainComplex`, LeanSearch on localization of unbounded total tensor complexes, and grep in Algebra/Homology and Algebra/Homology/Monoidal. All services answered. Flat-module/local-ring and generic total-tensor hits do not state the item. Read the pertinent types in Mathlib/RingTheory/Localization/BaseChange.lean (localized modules, rTensor, moduleTensorEquiv), RingTheory/Flat/Localization.lean, Algebra/Module/LocalizedModule/Exact.lean, and Algebra/Homology/Monoidal.lean. Their module assertions are reused through existing DAG nodes, not recreated.

Searched the entire DAG by source tags 0B67 and 06Y1, the label base-change-K-flat, titles involving localization/K-flatness/exactness/tensor, and the module-localization and cohomology node filenames. Opened all cited statements. In particular lem-weil-pbc-localization-module-tensor and lem-weil-pbc-localization-tensor concern principal localization only, so are not cited as arbitrary-prime localization facts. The proof instead gives the general fraction/tensor identification directly and uses the arbitrary-subset tensor-over-base node.

## Not duplicates

No new nodes were created. Existing exactness, cohomology, K-flat extension, and tensor-localization statements are cited in their existing locations.

## Review by Q138

I read more-algebra.tex at lemma-tor-amplitude-localization (0B67), including its displayed cohomological localization identity, and lemma-base-change-K-flat (06Y1), including its no-flatness base-change proof. I also read algebra.tex at proposition-localization-exact (00CS), lemma-tensor-localization (00DK), and lemma-tensor-with-bimodule (00D2), and homology.tex at lemma-exact-functor (010N). The latter is the exact-functor criterion; I use the separately stated DAG cohomology consequence, not an assertion that the source itself prints that consequence. No SGA source is used. The statement's arbitrary unbounded complexes, base K-flat test resolution, and A-action through K agree with this application of 0B67. The chain-level details are my expansion and are marked proof_origin.by=agent.

Step 1 uses the actual fraction equivalence in def-weil-pbc-module-localization and the universal property and generating pure tensors in def-weil-pbc-module-tensor-product. The inverse tensor/fraction formulas are written, with the annihilating denominator that checks independence. This also identifies the augmentation, rather than just the complex objects. The only prime fact needed is the immediate implication t outside p implies phi(t) outside q.

Step 2 uses exactly the statement of lem-pc-kflat-extension-of-scalars: its universal acyclic-test conclusion is K-flatness of the extension, with no flatness of the ring map. The localization-module-exact node states exactness for any multiplicative subset. Fractions make the functor additive; applying exactness also at the zero ends makes it exact as a functor of module categories. The exact-functor-complex-cohomology node states a natural isomorphism in every integer degree, with no boundedness. Applied to epsilon it makes the localized augmentation a quasi-isomorphism. The definition of a K-flat resolution is quoted from def-pc-module-kflat-complex. Thus I do not cite a definition as if it supplied preservation of exactness.

Step 3 uses precisely lem-weil-pbc-localization-tensor-over-base, with the A-module K^i and R-module P^j, and T=A minus q. The source node states the fraction formula and naturality in the second module. Naturality in the first module and A_q-linearity follow directly from that displayed formula and are written out. It does not require K^i or P^j to be flat.

Step 4 cites only the fraction definition and the tensor universal property. It proves the change from tensor over R to tensor over R_p inline: phi(t) is invertible on X=K_q, equality of u/t fractions gives an annihilator v, and cancellation of phi(vtt') proves independence. The text writes the R_p-balancing equation and both inverse identities. This is an elementary calculation on modules, not a new theorem copied from another proof or a restatement-only dependency. In particular the inverse denominator is s phi(t), in A, rather than an ill-typed product st.

Step 5 uses the direct-sum total convention in def-pc-tensor-complex-sheaves and the fraction zero criterion in the localization definition. It explicitly proves the needed localization/direct-sum interchange: finitely many denominators give surjectivity and finitely many annihilators give injectivity. Applying the already constructed summand maps then assembles the degree maps. It uses finite support, not a boundedness assumption or an interchange of products. This short finite-support argument does not create a separate elementary node.

Step 6 uses the signed differential from the tensor-complex definition. Its displayed equality checks both differential contributions and the unchanged (-1)^i sign. Naturality is checked on the pure localized generators for both chain maps, and the augmented-resolution equation epsilon' g = h epsilon is explicitly localized. Finally the abstract-derived-category node actually defines a functor Q from cochain complexes; a functor preserves inverse arrows and commuting squares. No exactness of tensoring K is assumed here.

Every uses entry has a verbatim quotation in citations.json. The proof_deps list is their union. No new-node B1--B9 obligations arise. The split has no new placeholder, no cycle through the parent, no lemma that restates an item clause, and no step over 2000 characters. The explicit fraction calculations are the content of the elementary steps, not omitted comparisons. The substantial inputs are cited by their statements as required by C1/C4.

For edge cases I checked K=0, N=0, zero terms of P, and R=A with q=p, when the maps reduce to ordinary localization tensor formulas. An unbounded complex still has finite support in each individual total element, which is all Step 5 uses. For a genuinely nonflat map, R=Z to A=Z/2 and q=(0), p=(2), all denominators used remain units on A_q; no tensor exactness of A over R was used. If A is the zero ring it has no prime q, so the assertion indexed by q is vacuous, while the K-flat scalar-extension tool also permits the zero ring. Localizations may kill torsion: the annihilator checks in Steps 1, 4 and 5 explicitly allow that and never cancel a denominator in an unlocalized module.

## Unfinished work

None in the stage-1 split. Independent maintainer review remains part of the delivery process.
