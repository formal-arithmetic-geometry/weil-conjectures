## Files written

- dag/nodes/sec-trace-formula/lem-trf-two-term-kernel-normalization.json: statement, split in seven steps; no complete Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-line-module-duality.json: statement-only, unsplit; no Mathlib match under its local-rank-one hypothesis. This is the only new node; no new Mathlib leaves.
- citations.json: a verbatim statement quotation for each dependency of each item proof step.
- searches.jsonl: unmodified search-command output log; searches were run through msearch.py and the returned hits read.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, kernel normalization, determinantLine and determinant-line terminology. The representation determinant declarations, split-exterior calculations and shifted sheaf determinant duality cover different objects or only fragments; none states this item. No Lean was written or compiled.

## Literature wanted

None. Sources used are present locally.

## Findings and changes

The item was unsplit, with an empty proof. Its statement is retained verbatim. Added explicit definition dependencies for the projective determinant module and ordinary module tensor product. The existing source's determinant convention agrees with the kernel-first convention, and tensor permutations here are ordinary, without Koszul signs. No STATEMENT-DISPUTED correction was necessary.

Read more-algebra.tex, Tag 0FJI (section-determinants-complexes), from the two-term determinant definition through the diagram immediately before Tag 0FJJ. Read Tag 0FJB (lemma-det-ses) and its two constructions, the determinant-module description in Tag 0FJ9, and the full evaluation proof of Tag 0B8I (lemma-invertible). The new node is the ordinary ring-module rank-one evaluation/scalar-endomorphism fact appearing in those places. It is not an assertion about complexes, acyclicity, or the kernel-normalized map.

The current blueprint is literature/blueprint/latest (COMMITS.txt: main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345). Read the latest sk-i-curve-zero/_section.md and lem-trf-local-term-locality.proof.md; this algebra lemma is a descendant through the already recorded marked-dualizing/Temkin auxiliary chain, not a replacement of the contracting-correspondence argument. The ancestor search returned lem-trf-local-term-locality. Retained the recorded ancestry and made the new node's intervening via chain start with the item.

## Searches and reuse

Searched the entire DAG for 0FJB, 0FJI, 0FJJ, 0B8I and 0FJ9, projective lifting/splitting, determinant, invertible-module evaluation, scalar endomorphisms, and finite-projective tensor-Hom. Used blueprint_refs.py search for determinant, invertible module, rank-one, evaluation, 0B8I and scalar endomorphism. None of the imported blueprint statements states the item or the new ordinary rank-one module fact. The existing scheme/sheaf line-evaluation statements introduce a scheme or curve and are not statements for ordinary modules over an arbitrary ring. In particular the derived pro-etale finite-projective tensor-Hom node is not used for ordinary modules.

Reused lem-pc-finite-projective-module-tensor-hom, already a Mathlib leaf, instead of creating dual-tensor-Hom or tensor-dual nodes. Its statement explicitly allows a finite projective source and arbitrary target factors. Reused the Mathlib leaf lem-sf-finite-projective-dual for finite projectivity of duals and biduality. Mathlib Contraction.lean:281--283 has dualTensorHomEquiv with finite/projective hypotheses, even though its docstring says finite free. The checked PicardGroup.lean:77 defines Module.Invertible by invertibility of dual evaluation; :83 constructs that equivalence and :257 proves toModuleEnd_bijective assuming this class. These do not supply the local-rank-one-to-evaluation implication. The file's TODO at :55--59 expressly leaves the local-rank-one characterization unfinished. Accordingly the new node stays unsplit, with these candidates explained in its recorded search verdicts. Dimension.Free results require globally free modules, which the new node does not assume. Two different semantic phrasings, Loogle and Mathlib grep were used; the exact query texts and returned digests are recorded, including the initially unsuccessful grep in RingTheory/Invertible and the subsequent successful search in RingTheory.

## Not duplicates

lem-trf-line-module-duality vs lem-trf-k0-class-trivial-invertible: the existing statement trivializes a line assuming an equality in K_0; the new statement gives canonical evaluation and scalar endomorphisms without assuming triviality or any K_0 equality.

lem-trf-line-module-duality vs lem-trf-k0-determinant-map: the existing statement constructs a homomorphism from K_0 to Pic; the new statement is a module-level duality assertion and constructs no K-group map.

lem-trf-line-module-duality vs lem-trf-regular-local-pic-zero: the existing statement trivializes lines over a principal localization of a regular local ring; the new statement applies over every commutative ring, including rings with nontrivial Picard group, and does not trivialize the line itself.

lem-trf-line-module-duality vs lem-pur-pid-invertible-module-trivial: the existing statement assumes dual evaluation is bijective and a principal ideal domain to prove freeness; the new statement proves evaluation and scalar-endomorphism isomorphisms from finite projectivity and local rank one, without a domain or PID assumption.

lem-trf-line-module-duality vs lem-trf-projective-determinant-chart-descent: the existing statement constructs exterior determinant modules by chart descent and descends compatible tensor maps between such determinants; the new statement gives evaluation and scalar endomorphisms for an arbitrary rank-one finite projective module and has no exterior algebra or gluing datum.

lem-trf-line-module-duality vs lem-trf-projective-exterior-scalar-comparisons: the existing statement compares exterior powers, duals and determinant maps under scalar extension; the new statement identifies dual evaluation and scalar endomorphisms over a fixed ring, with no scalar-extension morphism.

## Review by Q137

I checked the item against the actual construction in Tag 0FJI rather than using its acyclicity sentence as a black box. Step 1 uses the lifting clause of def-weil-pbc-projective-module, whose statement explicitly says that every map from a projective module lifts along a surjection. Taking that map to be the identity of Q^i gives the required section. The displayed inverse formulas prove the splitting and composing retractions proves finite projectivity without invoking an uncited closure lemma. The finite free hypothesis is used here; no noetherian or field hypothesis is introduced.

Steps 2 and 3 use the cohomology formula in def-weil-abstract-derived-category. I checked that the absence of degree -2 makes H^{-1} literal cycles, so equality of degree -1 classes is equality of elements. Injectivity of H^{-1}(a) proves kernel injectivity; injectivity of H^0(a) provides p, and surjectivity of H^{-1}(a) provides the correcting cycle z. Their difference is genuinely in ker(a^{-1}), and its differential is exactly the original n. This is the elementary two-term chase, not an uncited long exact sequence or general kernel-acyclicity theorem.

Step 4 uses the statement of lem-trf-projective-determinant-exact-sequence, which I opened: it asserts the canonical kernel-first map, its explicit wedge order, and finite projective locally rank-one determinant modules. Both exact sequences meet its hypotheses by step 1. It is the existing same-unit input from Tag 0FJB, not a new copy of that fact.

Step 5 uses the full statement of the ordinary module tensor-Hom Mathlib leaf, not the similarly named sheaf/derived node. With Q=R it yields the stated Hom comparison after a unitor. Currying is the universal property of the ordinary tensor node, and applying the same comparison to W-dual yields the tensor-dual map, with its explicit pure-tensor functional written in the step. The finite projective dual node states both finite projectivity and the evaluation bidual isomorphism. Thus inverse dualization of gamma^{-1} has the correct direction. Reassociation and permutation are elementary maps on pure tensors, with inverses supplied by the reverse permutation; no signed complex symmetry is used.

Step 6 additionally cites lem-weil-pbc-finite-projective-standard-free-cover for the covers and lem-trf-projective-determinant-chart-descent for the identification between the chart-defined lines used by gamma and the exterior-annihilator model. I opened both statements: the latter explicitly supplies that identification, induced by exterior localization and top exterior inclusion. This repairs a model-identification omission found on my last reading, after the first dry run passed. Step 6 uses the exterior-algebra functor and annihilator definition in def-trf-projective-determinant-module, which I opened and quoted. The displayed generator argument checks restriction of the exterior map on every annihilated vector, using surjectivity of d_N; applying its inverse checks invertibility on the determinant module. It does not assume a determinant functor on the derived category. The new line-duality node supplies exactly the scalar map R to End(L), not a freeness claim about L. Composing it with postcomposition by the determinant isomorphism u and the tensor-Hom comparison gives t with t(1)=delta_N, so delta_N is a basis element. Its evaluation clause also gives actual tensor inverses of the determinant lines. I expanded this step to distinguish determinant-module functoriality from the ordinary scalar determinant of an endomorphism.

Step 7 uses the ordinary tensor node's identity/composition laws. The inverse is written explicitly and both inverse equations reduce to those already proved. The uniqueness equation S=SFT_a=T_a has the correct domain and codomain. Every cited statement is quoted verbatim in citations.json; none of the steps relies on a cited node's proof. No step is longer than 2000 characters.

I tested the item on a=identity (zero kernel, empty-wedge determinant 1), on a map to the zero complex (P must have invertible differential), and on a split projection from Q plus a contractible two-term summand. These give the expected evaluation normalization and the required inverse. Zero modules and the zero ring require no nonzero basis or prime; all relevant maps there are the unique maps. Disconnected rings allow variable ranks for P and Q, while the differential identifies the ranks of the two kernel terms. Characteristic two introduces no issue because all permutations are ordinary tensor permutations and no sign is added.

For the new node I read the local evaluation proof in Tag 0B8I and the End(L)=R sentence in Tag 0FJ9. Over a free rank-one chart evaluation is multiplication of coefficients and scalar endomorphisms are coefficients; these are isomorphisms. Finite projectivity gives the usual localization comparisons for duals/Hom, and local isomorphism detection gives the asserted global maps. This proof sketch is left here for its later splitter; the node itself has statement only, empty proof and proof_deps, a source, definitions, recorded real searches, blueprint origin and status unsplit. The tests L=R, the zero ring and nonfree invertible modules show why it asserts evaluation/endomorphisms rather than L being globally free. It is a genuine general duality input, not one clause of the complex-normalization item moved into a child. The new node has no proof or statement path back to the item, and existing inputs do not depend on the item.

## Unfinished work

No unfinished part of the item's split. The new rank-one duality statement is intentionally unsplit for the next stage-1 item, as required by one-level splitting. No attachments, wanted sources, Lean files or builds.
