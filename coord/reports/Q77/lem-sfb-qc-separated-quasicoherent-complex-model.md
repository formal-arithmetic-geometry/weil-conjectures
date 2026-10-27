# Stage-1 delivery: lem-sfb-qc-separated-quasicoherent-complex-model

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-qc-separated-quasicoherent-complex-model.json: item, split; unchanged statement and statement dependencies; not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-open-derived-qcoh-criterion.json: one new statement-only node, unsplit; no Mathlib match.
- citations.json: an exact statement quotation for every node used in every numbered proof step.

## Attachments

None. Searched the project under lean/WeilConjectures for the blueprint tag, termwise quasi-coherent models, coherators, and derived quasi-coherent equivalences. The affine representative/equivalence files cover only affine schemes; DQCoheratorAdjunction concerns the different right adjoint into D_QCoh, not the derived category of QCoh. No project declaration found states the item's entire conclusion with its hypotheses and a completed proof. AffinePushforwardResolutionQuasiIso.lean:152 is the existing prerequisite, not an attachment of this item.

## Wanted literature

None. WANTED: none.

## What needed repair

The item arrived unsplit. Its statement is correct: perfect.tex Tag 08DB implies it, and Tag 0BQR explicitly uses this specialization. No statement dispute or hypothesis change was necessary. The source's proof is not merely an invocation of essential surjectivity: it checks affine-open pushforward compatibility and invokes the conditional criterion 09T6. Those are the steps retained here. The unrelated pro-etale coefficient categories in the unit are not identified with structure-sheaf modules.

blueprint_refs.py ancestor prints None because the historical created.item chain ends at the Lean item name Sheaf.SixFunctors.CtfStabilityDirectImages. I retained the item's inherited blueprint.from.node = null and its precise inherited place/via chain, and used the tool's reported null for the new node. The current blueprint counterpart at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), was read; its detail label is det-thm-sf-ctf-stability-direct-images. This is a support lemma far below that paragraph's alteration/cohomology route, which is retained.

## Not duplicates

No existing node has source Tag 09T6 or label perfect-lemma-argument-proves. Full DAG source/statement searches and blueprint_refs.py searches for coherator, 09T6, affine-open, affine pushforward, quasi-coherent, derived comparison, and quasi-compact affine diagonal found no existing copy of the conditional criterion. The new node does not restate the item: it assumes comparison for every affine open, makes no separatedness assumption, and concludes the full derived comparison is an equivalence. The item proves its premise using affine geometry and unbounded resolutions before extracting a complex model.

lem-sfb-affine-open-derived-qcoh-criterion vs lem-pc-affine-qcoh-derived-equivalence: the existing node treats a single affine scheme and modules over its ring; the new criterion assembles comparisons from affine opens on an arbitrary qcqs scheme.
lem-sfb-affine-open-derived-qcoh-criterion vs lem-pc-dq-coherator-adjunction: the latter concerns the right adjoint of D_QCoh into D(O), not the comparison D(QCoh) into D_QCoh.

## Searches

All new searches ran through the required msearch.py command and their original tool/query/results are preserved in searches.jsonl. The node records the actual criterion queries, including two different LeanFinder phrasings, LeanSearch, Loogle and source grep. Searches returned abstract derived localization/exact-functor results and quasi-coherence presentation data, not the geometric criterion. The item also records freshly run searches in addition to its inherited Q65 searches. There were no unavailable services. Abstract essential surjectivity of DerivedCategory.Q gives arbitrary module-sheaf complexes; it does not give quasi-coherent terms without the geometric comparison. No new leaf is asserted.

## Review by Q77

I read the complete local source proof of perfect.tex Tag 08DB and its inputs 09T6 and 08D7, together with 08D8 and 08D9 in the surrounding coherator section. I read the first paragraph of 0BQR to check the requested consequence and the absence of boundedness restrictions. For the one new node I read the full statement and proof of 09T6, including its induction on closed support covered by finitely many affine opens, and compared the online source https://stacks.math.columbia.edu/tag/09T6. The node retains the full affine-open derived comparison hypothesis and the unbounded equivalence conclusion; it omits only the optional identification of a quasi-inverse. It is statement-only so that its own induction and coherator foundations remain work for its subsequent split.

Step 1 uses the existing kernel, cokernel/image, binary-sum and ambient module-category statements. I opened each statement: they give ambient kernels, ambient cokernels/images and biproducts in the quasi-coherent subcategory. The zero module is the associated zero module, supplied by the tilde node. Closure under these constructions makes the inherited coimage/image isomorphism an isomorphism of that full subcategory; no separate categorical closure lemma is hidden. The existing exact-functor factorization supplies the induced functor and its representative comparison. I read schemes.tex Section 01LA and Tag 01IC against this argument. This is a short assembly from cited closure statements, rather than a new node asserting QCoh is abelian.

Step 2 uses the existing closed-immersion definition, spectrum quasi-compactness, quasi-separatedness definition and affine-source/separated-target lemma. The closed-immersion definition explicitly includes the quotient-spectrum description, so the quasi-compactness inference needs no uncited general permanence theorem. Applied to the absolute diagonal, this proves the exact quasi-separatedness hypothesis of 09T6. The affine-source lemma applies to every affine open inclusion into the given separated X, with no finite-type or Noetherian assumption. I read morphisms.tex Tag 01SG. I did not assume affine intersections merely from quasi-separatedness.

Step 3 uses the affine-image quasi-coherence clause of lem-pc-affine-morphism-hi, the definition of affine morphism, the actual affine-section surjectivity clause of the existing cokernel/image statement, the sectionwise definition of direct image, and the exact-derived-functor theorem. I corrected an earlier draft to prove exactness directly on affine opens: W=j^{-1}(V) is affine, and since C is the ambient cokernel the statement really supplies B(W) onto C(W) with kernel A(W). This avoids silently assuming sheaf-level acyclicity alone handles unbounded complexes. Exactness in QCoh is the inherited exactness established in step 1. I read coherent.tex lemma-relative-affine-vanishing and derived.tex Tag 015F in addition to 08D7.

Step 4 uses exactly the existing unbounded affine-pushforward resolution lemma: its source complex must have quasi-coherent terms, its target must be K-injective, and its morphism must be a quasi-isomorphism. These are all supplied by the chosen functorial ambient resolution and the complex in QCoh. The resolution node is valid for any small ringed site; the opens form a set. Its target need not have quasi-coherent terms. The derived-direct-image definition expressly says that j_*J represents Rj_* for every such resolution, so the citation gives the identification actually used. The comparison is the natural resolution comparison itself, not an arbitrary objectwise isomorphism. The node explicitly handles unbounded source and target complexes.

Step 5 cites the new 09T6 criterion after all its hypotheses have been checked, and the existing derived-category definition to choose a representative in D(QCoh). The factorization established in step 1 identifies its underlying sheaf complex with the chosen quasi-coherent derived object. This is essential surjectivity plus localization, with no construction of a K-injective complex inside QCoh assumed by the item. I verified every citations.json quote is verbatim from the relevant statement and reviewed B1--B10, C1--C8, D1--D5 and E1--E7 against these steps. No step exceeds 2000 characters. The only new node is the genuine local-to-global criterion; closure facts, exactness and final representative extraction remain steps.

I checked X empty, K zero, X affine, a complex nonzero in arbitrarily positive and negative degrees, and non-Noetherian separated quasi-compact X. Empty X admits the zero model; the criterion's finite-support induction includes its zero-affine base case. For affine X the conclusion agrees with the existing affine equivalence. No truncation or bounded spectral-sequence argument has been inserted, so the unbounded case has no extra hypothesis. I also tested the criterion with U empty and with the identity affine open on an affine X: the displayed comparisons reduce to the zero or identity functors. I retained quasi-separatedness in the new criterion rather than claiming the same result for arbitrary non-quasi-separated schemes.

All off-unit statement tools are declared in split_report.tool_uses for maintainer review. They are generic module-sheaf, affine-geometric and homological-algebra inputs; none replaces a prescribed unit-level step. No SGA source was used. No Lean file, compiler, build tool, repository file or launcher file was changed.

## Unfinished work

The new conditional comparison criterion remains unsplit, as required for new stage-1 nodes. No requested part of the item proof remains unaccounted for. Server-side checks and final delivery are recorded by the delivery tool.
