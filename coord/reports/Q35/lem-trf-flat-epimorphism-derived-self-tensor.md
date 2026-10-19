## Files written

- dag/nodes/sec-trace-formula/lem-trf-flat-epimorphism-derived-self-tensor.json: split the item in four steps; full derived assertion has no Mathlib match.
- citations.json: verbatim statement quotations for all five step/node citations.
- No new DAG nodes, no Mathlib leaves, no unit changes.

## Attachments

None. Searched the designated read-only slopmaster2 WeilConjectures source by the full item tag and by flat epimorphism, self tensor, derived tensor, B tensor B and multiplication terminology. No project declaration states every clause. The ordinary-tensor Mathlib lemma is not a project attachment.

## WANTED

None. All mathematical sources used are present locally.

## Findings and corrections

The item's surjective-flat statement is correct and was preserved. The id says epimorphism, but the statement actually assumes surjectivity; the proof uses that hypothesis and makes no identification of surjections with all ring epimorphisms. Stacks 08R2 (cotangent.tex, lemma-when-zero) states cotangent-complex vanishing, not the derived self-tensor assertion verbatim. Its proof applies the derived-diagonal lemma to a surjective flat multiplication map. I retained the item's original source and supplied the supporting tensor argument with proof_origin.by = agent, referencing the actual K-flat construction in more-algebra.tex.

The seeded item had no proof. I added the missing ordinary-module tensor and derived-scalar-extension statement dependencies. Step 1 uses a theorem on exact tensor, rather than treating the injective-map definition of flatness as already giving preservation of whole exact complexes. Step 2 uses the ordinary-module mixed derived tensor theorem, retaining the B-action on the second factor and identifying the canonical multiplication itself. No comparison between condensed modules and ordinary modules is needed: these are ordinary commutative rings throughout.

Read the chapter and sk-i-curve-zero unit and the current main-20261015 local-term-locality blueprint node. This item is a generic ring input in a long created.item ancestry, not the unit's key statement. It does not replace the unit's contracting-correspondence proof. The only off-unit theorem tool is lem-pc-derived-tensor-second-factor-functor, declared in split_report.tool_uses: it constructs derived tensor, which this trace-formula unit does not supply.

## Mathlib and duplicate searches

Read all five msearch outputs in searches.jsonl. Both semantic phrasings, Loogle, LeanSearch and grep were run through the required command; the item retains its inherited searches as well. The first semantic query returned faithful-flat descent, Kaehler differentials and ordinary kernels; the second returned exact tensor facts. Loogle returned zero hits. LeanSearch returned ordinary flatness/descent. Grep found LinearMap.mul'_bijective_of_surjective in Mathlib/RingTheory/TensorProduct/Maps.lean:887. I read lines 883-890: it proves ordinary multiplication bijective under surjectivity, not the derived comparison. I also read Mathlib/CategoryTheory/Monoidal/Tor.lean:41-56: these declarations define homology-valued derived functors, not this total derived tensor morphism. Consequently the item is split, not a Mathlib leaf.

Whole-DAG concept searches and blueprint_refs searches for self-tensor, epimorphism and derived tensor flat found no equal blueprint statement. Existing flat tensor exactness, ordinary-module K-flatness, derived tensor second-factor construction, tensor-product definition and derived-category definition supply every input; no nodes were created.

## Not duplicates

No new nodes and hence no new/existing same-tag pairs.

## Unfinished work

None for this one-level split. Existing cited nodes retain their own independent proof/frontier status.

## Review by Q35

I read Stacks cotangent.tex Tag 08R2 (lemma-when-zero), including its proof, and more-algebra.tex Tag 06XZ (definition-K-flat), the construction and definition of derived tensor (definition-derived-tor), and Tag 06Y6 (lemma-derived-base-change) with the immediately preceding identity-resolution formula. I also read algebra.tex Tag 00HD (lemma-flat) and the tensor universal-property material Tag 00CX. There are no new nodes requiring further source reviews. The original statement has no counterexample and needs no STATEMENT-DISPUTED correction; only the imprecise source attribution needed explanation.

For step 1 I opened lem-weil-pbc-flat-tensor-exact and def-pc-module-kflat-complex. The former explicitly preserves an exact three-term sequence with a flat tensor factor. Apply it at every integer degree of an arbitrary acyclic complex; total tensor with B in degree zero has exactly those terms and differentials. The latter explicitly defines ordinary-module K-flatness by this test. Thus this is a short elementary specialization, with no boundedness assumption or uncited resolution-existence argument.

For step 2 I opened lem-pc-derived-tensor-second-factor-functor and checked its entire clause (2), not just its title. It gives a canonical computation in the target-ring derived category for every K-flat resolution, and permits any complex N. Substitute base A, target B, and both complexes B[0]; step 1 permits the identity resolution. The comparison is then the identity-resolution computation, so multiplication is represented by mu[0]. The second-factor action is essential: both mu and c maps to 1 tensor c are B-linear for precisely that action.

For step 3 I opened def-weil-pbc-module-tensor-product: it states the bilinear universal property, the balanced construction, and pure-tensor generation. The proof gives the explicit inverse; a lift of b is used only to prove b tensor c = 1 tensor bc, never to define an inverse depending on choices. Both composites are verified, and pure-tensor generation justifies extending the second identity to the whole module. This is elementary and does not need a new node for ordinary surjective multiplication.

For step 4 I opened def-weil-abstract-derived-category. It states the localization functor, which preserves identities and compositions, so the chain inverse equations remain inverse equations in D(B). The canonical model in step 2 then proves the requested actual map is invertible. Restriction of these chain inverse equations also proves it in D(A), resolving any ambient-category ambiguity without an additional derived comparison theorem.

I tested the identity A to A, arbitrary A to the zero ring, and the projection k times k to k (a nontrivial flat surjection). All formulas remain valid, including the zero ring. Dropping flatness would fail for Z to Z/2 because of higher Tor; dropping surjectivity would fail for a nontrivial flat field extension. These checks confirm the two hypotheses have distinct uses and neither was silently dropped. I checked B-E point by point: every non-elementary input is a cited statement, quotations are literal substrings, no new lemma restates the item, no SGA route occurs, and every step is shorter than 2000 characters.
