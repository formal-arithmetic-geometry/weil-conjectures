# Stage-1 repair report: lem-trf-affine-etale-relation-separated-lqf

## Files written

- dag/nodes/sec-trace-formula/lem-trf-affine-etale-relation-separated-lqf.json: statement unchanged, three assembly steps, status split.
- dag/nodes/sec-trace-formula/lem-trf-affine-square-monomorphism-absolute-separated.json: statement, unsplit; no full Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-monomorphism-finite-type-composite-lqf.json: statement, unsplit; no full Mathlib match for the pointwise conclusion.
- citations.json: one checked verbatim statement quotation per proof-step citation.

## Attachments

None. A tag/notion search under lean/WeilConjectures found no declaration of this item. The existing theorem AlgebraicGeometry.affine_etale_relation_separated_locally_quasi_finite in lean/Sheaf/AlgebraicGeometry/AffineEtaleRelationSeparatedQuasiFinite.lean ends with sorry. It does not qualify as an attachment. The existing unramified-to-quasi-finite theorem is reused through its existing node, not recreated.

## Wanted literature

None. All sources read locally in literature/stacks-project/; no SGA source is used.

## Returned problem and repair

The return requests at least two independent statement-only work items, retaining the statement and the entire mathematical argument, with a parent proof of at most 3000 characters. The sandbox was empty at startup (including no report or prior search log); the initial required dry run exited with 'no node files'. I copied the current repository's five-step split as the returned baseline. Its five steps have exactly the lengths in the return. I did not discard a retained sandbox attempt or replace the original argument with a compressed proof. The complete returned argument is preserved below, with a work allocation. Both new nodes have empty proof and proof_deps, null proof_origin, explicit definitions, source, blueprint ancestry, real searches and status unsplit. Neither is the item or just a restatement of one of its six requested properties: the first constructs an absolute affine ambient scheme for a monic relative relation, without any etaleness; the second is a general three-scheme monomorphism theorem, without affineness or equivalence relations. They have independent hypotheses and neither depends on the other. These extraction boundaries implement the explicit human re-split instruction even where some internal deductions are short.

No statement dispute was found. The chapter and unit are unchanged and no route is replaced. The inherited tool-use declaration for lem-weil-pbc-unramified-quasi-finite-at-points is retained; this supplies the pointwise notion and is not silently identified with Mathlib's class.

## Preservation and work allocation

The first new node owns returned step 1 (affine absolute product, canonical comparison monicity and composite monicity), returned step 2 applied to q (the explicit diagonal inverse and separatedness), and the first part of returned step 3 (absolute separatedness over the affine product). The second new node owns returned step 2 applied to j (isomorphic diagonal, open and closed immersion consequences), and all of returned step 5 (local finite type cancellation, unramifiedness and pointwise local quasi-finiteness). Its extra separatedness conclusion records the same diagonal computation. Returned step 3's final cancellation for s,t is assembly step 1; returned step 4 is assembly step 2. The applications of existing unramified local quasi-finiteness in both locations are retained. Thus no argument disappears and no single child carries the whole item. The first block has roughly 1600 characters of the old argument and the second roughly 1500 including the shared diagonal computation; the two future workers have comparable separate arguments.

### Verbatim returned proof, retained for the next workers

Old step 1 (619 characters):

Write $V=U\times_SU$ and $P=U\times_{\operatorname{Spec}\mathbf Z}U$. If $U\cong\operatorname{Spec}A$, the affine fibre-product formula gives $P\cong\operatorname{Spec}(A\otimes_{\mathbf Z}A)$, so $P$ is affine. Let $k:V\to P$ be the morphism with the same two projections to $U$ as $V$. It is a monomorphism: for any two morphisms $a,b:T\to V$, equality $ka=kb$ gives equality of both projections of $a,b$ to $U$, and hence $a=b$ by the defining universal property of $V$. Therefore $q=k\circ j:R\to P$ is a monomorphism too: $qa=qb$ first implies $ja=jb$ by cancellation of $k$, and then $a=b$ by cancellation of $j$.

Cited nodes: lem-weil-pbc-fibre-product-affine-spectra, def-pc-fibre-product.

Old step 2 (755 characters):

For $f=j:R\to V$ and for $f=q:R\to P$, write $p_1,p_2:R\times_{\operatorname{target}(f)}R\to R$. Since $f$ is a monomorphism, $fp_1=fp_2$ implies $p_1=p_2$. The diagonal $\Delta_f$ is inverse to $p_1$: $p_1\Delta_f=1_R$, and both projections of $\Delta_fp_1$ agree with those of the identity, so $\Delta_fp_1=1$ by the fibre-product universal property. Thus both diagonals are isomorphisms. An isomorphism identifies the source with the whole target, a closed and open subset, and induces isomorphisms on structure sheaves; by the definitions it is both a closed and an open immersion. Consequently $j,q$ are separated and $\Delta_j$ is an open immersion. This proves the elementary monomorphism-diagonal argument of Schemes Tags 01L3 and 01L4 explicitly.

Cited nodes: def-pc-fibre-product, def-weil-closed-immersion, def-weil-open-immersion, def-weil-proper-morphism.

Old step 3 (622 characters):

Apply the separated-over-affine lemma to $q:R\to P$: step 1 gives that $P$ is affine, and step 2 gives that $q$ is separated. It follows that the absolute structure morphism $a_R:R\to\operatorname{Spec}\mathbf Z$ is separated. Write $a_U:U\to\operatorname{Spec}\mathbf Z$ for the absolute structure morphism. Since $a_U\circ s=a_R=a_U\circ t$, separated cancellation, clause (b), applied to these two factorizations shows that $s$ and $t$ are separated. Together with step 2 this gives separatedness of all three requested morphisms. The argument uses the affine scheme $P$, and makes no assumption on the diagonal of $S$.

Cited nodes: lem-sc-separated-over-affine-scheme-separated, lem-weil-pbc-separated-cancellation.

Old step 4 (390 characters):

By the definition of etale, each of $s,t$ is unramified. Apply the unramified-to-locally-quasi-finite theorem to each morphism to obtain that $s,t$ are locally quasi-finite, in the pointwise sense of the statement. The definition of unramified also gives that $s$ is locally of finite type. This deduction requires no quasi-compactness or separatedness hypothesis on an unramified morphism.

Cited nodes: def-weil-etale-morphism, def-weil-unramified-morphism, lem-weil-pbc-unramified-quasi-finite-at-points.

Old step 5 (778 characters):

Let $\pi_1:V\to U$ be the first projection. The equality $\pi_1\circ j=s$ and the local finite type of $s$ from step 4 allow clause (f) of the permanence lemma to be applied to $j$ followed by $\pi_1$; it yields that $j$ is locally of finite type. Step 2 already gives that $\Delta_j$ is an open immersion. These are exactly the two conditions in the definition of an unramified morphism, so $j$ is unramified. Apply the unramified-to-locally-quasi-finite theorem once more to get that $j$ is locally quasi-finite. This supplies the local quasi-finiteness required in the second paragraph of the source, using its monomorphism hypothesis through the explicitly computed diagonal. Combining steps 2--5 proves every clause. Nothing in these steps assumes quasi-compactness of $R$.

Cited nodes: lem-weil-pbc-proper-fp-permanence, def-weil-unramified-morphism, lem-weil-pbc-unramified-quasi-finite-at-points.

## Search record and candidate checks

Every new search in the node files was run through batch2/msearch.py and is in searches.jsonl. LeanFinder was tried twice for each new argument (and a third time for the pointwise formulation); Loogle and Mathlib grep were also run. LeanSearch returned an explicit shared-service rate-limit error and is recorded unavailable. The inherited item searches and citations are retained in its JSON. Searches for an initially guessed Unramified.lean path returned no hits because that file does not exist; I did not treat that as mathematical evidence and corrected the path to FormallyUnramified.lean. The grep service's single-file output mislabels line prefixes as file names; the later directory queries and direct source reading identify the real files and declarations.

Read Mathlib/AlgebraicGeometry/Morphisms/Separated.lean:61,75,256,338-370 (monomorphism separatedness, composition, cancellation and absolute separatedness), Morphisms/FiniteType.lean:72 (finite-type cancellation), FormallyUnramified.lean:79,126 (open diagonal/formal unramifiedness), and QuasiFinite.lean:70-110 (the different Mathlib quasi-finite class and permanence). These are components of the first construction, not a declaration giving the canonical absolute embedding and its conclusions. For the second node the monomorphism diagonal and finite-type consequences are present, but the pointwise affine-neighbourhood conclusion is the existing project's unramified-to-quasi-finite theorem, not a Mathlib result found by the searches. No component match has been misreported as a full match. The source of lean/WeilConjectures/AlgebraicGeometry/UnramifiedQuasiFinite.lean and QuasiFiniteMorphism.lean was checked for this distinction.

Whole-DAG statement searches included monomorphism with unramified, finite type, affine and separated; relative square and absolute square; and the source tags. Whole-blueprint searches through tools/blueprint_refs.py included monomorphism, monic, 0265, affine square, affine product, locally quasi-finite, unramified and separated scheme. They found no equivalent blueprint statement; the new same_as fields are empty. The ancestor command confirms lem-trf-local-term-locality and the new via lists prepend the present item to its existing ancestry.

## Review by NP

I read the item and its existing Lean docstring, the chapter sec-trace-formula and unit sk-i-curve-zero, then Spaces Tag 0265 (lemma-presentation-quasi-compact), including both opening paragraphs and the first representability step. This is the source for the parent and the first new node. Its monomorphism into the absolute affine square is valid for arbitrary S, while assuming that the relative square itself is affine would be unjustified. The new node explicitly keeps the absolute square and the canonical map. Schemes Tags 01L3 and 01L4 (lemma-monomorphism and lemma-monomorphism-separated) give the diagonal argument and its separatedness consequence. I checked that the inverse of the diagonal is the first projection because the two projections agree by monicity, not because j is surjective. For the second node I read Morphisms Tags 01T8 (lemma-permanence-finite-type), 02GE (lemma-diagonal-unramified-morphism), and 02V5 (lemma-unramified-quasi-finite); these require local finite type, open diagonal, and unramifiedness in precisely that order. They do not impose quasi-compactness or separatedness on g. The diagonal is over Y, not Z. The full old arguments, including these verifications, are allocated above rather than embedded as proof sketches in the new statement-only nodes.

For assembly step 1 I opened both cited node statements. The first new statement actually provides separatedness of the absolute structure morphism of R. Clause (b) of lem-weil-pbc-separated-cancellation actually permits cancelling the second map from a separated composite; it applies to a_U after s and t. The identities of structure maps are the elementary uniqueness of the absolute structure map; they impose no condition on S. I also opened the existing affine-product and separated-over-affine statements behind the extracted argument; the former has precisely the Z-algebra tensor product specialization, and the latter requires a separated map to an affine target, which is q into P after its diagonal calculation.

For assembly step 2 I opened def-weil-etale-morphism and def-weil-unramified-morphism: they respectively supply unramifiedness of both legs and local finite type of s. I opened lem-weil-pbc-unramified-quasi-finite-at-points: it states the affine-open/isolated-fibre-point conclusion for every unramified morphism and explicitly identifies this as local quasi-finiteness. Thus both s and t meet its hypotheses. No theorem is inferred from a definition beyond the definition's own conjunction.

For assembly step 3 I opened def-pc-fibre-product, whose projection identity gives pi_1 j=s, and the full second new statement. Its hypotheses are only monicity of f and local finite type of gf. They hold for f=j and g=pi_1 by the original hypothesis and step 2. Its statement gives both separatedness and the required pointwise local quasi-finiteness, so no appeal to its future proof or a hidden fibre-finiteness lemma is needed in this assembly. Each node citation has an actual verbatim statement substring in citations.json; no quote was bent to a desired inference. The parent proof_deps is exactly the union of uses. No proof step exceeds 2000 characters and their total is below 3000.

Small cases: the empty affine scheme (the zero ring) and empty R give vacuous pointwise conclusions and the same product/diagonal construction. For a nonempty example take S=U=Spec k and R=U with the diagonal relation; all maps have the stated properties. For the second node, identities and closed points Spec k to A^1_k (g the structure map) satisfy the claim; the latter is unramified even though it is not etale. Infinite disjoint unions of affine opens mapping monomorphically into a scheme illustrate why no global quasi-compactness may be inferred or used. Removing finite type would fail for a transcendental generic-point inclusion, so that hypothesis is deliberately retained. A nonseparated S does not affect the first construction: monicity of k uses equality of the two projections only, not a closed diagonal for S. No finite presentation, field, reducedness, finite fibre cardinality bound, or affineness of R has been added.

B1-B10: the new files are statement-only and self-contained, cite definitions of all scheme properties, render TeX once, locate sources by correct tags and labels, and contain only logged searches with the service failure recorded as unavailable. C1-C8: all assembly inputs are named and were read, projection and structure identities are written, citations quote statements, no new child points back to the parent or uses the parent's proof, no duplicate or off-route replacement is used, and the inherited tool declaration is retained. D1-D5: the two distinct general arguments are separated as requested rather than renaming target clauses or delegating the entire item. E1-E7: hypotheses, correct diagonal base, empty cases, and absolute versus relative products were checked against the sources; no source error or transport gap was found. I corrected the initial missing sandbox baseline and the mistaken guessed search path, not the mathematical statement.

## Not duplicates

lem-trf-affine-square-monomorphism-absolute-separated vs lem-weil-pbc-finite-ring-map-quasi-finite: the new node constructs the monic absolute affine-square embedding and absolute separatedness without etaleness; the existing node has a different quotient, local-finiteness, or ring-map conclusion.

lem-trf-affine-square-monomorphism-absolute-separated vs lem-trf-affine-etale-relation-separated-lqf: the new node constructs the monic absolute affine-square embedding and absolute separatedness without etaleness; the existing node has a different quotient, local-finiteness, or ring-map conclusion.

lem-trf-affine-square-monomorphism-absolute-separated vs lem-trf-etale-affine-quotient-representable: the new node constructs the monic absolute affine-square embedding and absolute separatedness without etaleness; the existing node has a different quotient, local-finiteness, or ring-map conclusion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-galois-fpqc-descend-unramified: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-fd-finite-ring-compact-support-finiteness: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs def-weil-etale-morphism: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs def-weil-unramified-morphism: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lemma-nagata-finite-type-to-separated-target: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-weil-pbc-etale-pointed-map-rigidity: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-weil-pbc-etale-ring-map-conormal-criterion: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-weil-pbc-etale-ring-map-iff-etale-affine: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-weil-pbc-finite-ring-map-quasi-finite: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-weil-pbc-flat-unramified-formally-etale: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-weil-pbc-lft-formally-unramified-unramified: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-weil-pbc-proper-fp-permanence: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-weil-pbc-smooth-zero-differentials-affine-open-etale: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-weil-pbc-unramified-fibre-point-isolated: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-weil-pbc-unramified-quasi-finite-at-points: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-weil-pbc-unramified-ring-map-iff-unramified-affine: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-trf-affine-etale-relation-separated-lqf: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

lem-trf-monomorphism-finite-type-composite-lqf vs lem-trf-etale-affine-quotient-representable: the new node starts from monicity and a locally finite type composite and proves its diagonal and pointwise local quasi-finiteness; the existing node supplies a definition or a different permanence, quotient, compact-support, or unramified theorem and does not establish this combined monomorphism assertion.

The two new nodes also differ from one another: the first assumes an affine relative-square presentation and has no local finite type conclusion; the second has arbitrary X,Y,Z, assumes local finite type of a composite, and has no affine ambient or absolute separatedness conclusion. Neither is a specialization of the other. In particular the old item cannot serve as a dependency of either child: it requires etale equivalence-relation legs and is the node being assembled.

## Unfinished work and validation

The two new lemmas are deliberately unsplit so separate workers can prove their assigned arguments. Nothing else is left incomplete within stage 1. No Lean file was written, no compiler or Lake command was run, and no repository or launcher file was modified. Required server dry run and push results are recorded below when complete.
