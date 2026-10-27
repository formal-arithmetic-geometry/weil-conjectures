# Stage-1 repair: lem-trf-reduced-curve-normalization-genus

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-reduced-curve-normalization-genus.json`: existing statement, repaired split; original Mathlib searches retained.
- `dag/nodes/sec-trace-formula/lem-trf-finite-curve-quotient-stalk-euler.json`: new statement, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-smooth-curve-family-euler.json`: new statement, unsplit; no Mathlib match.
- `citations.json`: a verbatim statement quotation for every citation of all five parent steps.

Attachments: none. The whole project was searched by the item tag and normalization/genus concepts. `AlgebraicGeometry.reduced_curve_normalization_genus` in `lean/Sheaf/TraceFormula/ReducedCurveNormalizationGenus.lean:80` ends with `sorry` and is not an attachment; no declaration under WeilConjectures states the item or either new lemma without sorry.

WANTED: archival local copy of Temkin, Stable Modification of Relative Curves, arXiv:0707.3953v3, Appendix B, Lemma B.1, printed p. 57, for lem-trf-reduced-curve-normalization-genus. The primary PDF was read online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf (PDF page 57, index 56); no download or repository write was made. The new nodes use the local Stacks source instead.

What was wrong: the returned proof occupied 6553 characters in eleven steps, so the batch5 instruction requires distributing its arguments. The sandbox initially contained only brief marker files, with no node, report or search log to recover. I copied the current reviewed repository node, whose eleven steps match the return, and retained its statement and other metadata. The corrected five-step assembly is 2947 characters after the current landing-return repairs. There is no statement dispute or change to the target or Lean signature.

Unfinished work: proving each of the two new lemmas is intentionally left to another stage-1 worker. Their JSON has status unsplit, empty proof/proof_deps, and no proof sketch in the statement. Their respective inherited arguments have 2870 and 1840 characters; both are substantial independent pieces, and neither restates the arithmetic-genus identity. No compiler, Lake, Lean file, git command or agent was run.

## Landing-return repair and rebase (2026-10-22)

The return records branch head `665667e06c7`: the reader approved the split, but landing refused the side completion because it had not been promoted to the live DAG. I retained the complete sandbox split, source notes, citations, inherited arguments and search log. The initial resumed dry run completed successfully at `089aca31b87` against the delivery tool's freshly fetched current DAG; no interrupted delivery process remained active before that invocation.

I compared the retained item with the current shared-repository item: the statement, statement dependencies, source, blueprint ancestry, Lean record and historical metadata agree; only proof, proof dependencies and split report differ. The current item still carries the eleven-step source proof, while the retained delivery distributes it into the two new lemmas and five assembly steps. Both child ids are still absent from the current DAG. The released stage-1 repair note remains in force and requires at least two new statement-only nodes and an assembly of at most 3000 characters, so the old passing review does not supersede this repair.

I reread the full current statements of every parent proof citation, rather than assuming the returned branch's dependency versions still apply. All twelve citation quotations remain verbatim current statement substrings. In step 1 the finite-type theorem requires a Noetherian base, furnished by the field; reduced normalization supplies finite surjectivity and the normal-open isomorphism. In step 2 normalization-properties supplies precisely finiteness, properness, dimension and smoothness over a perfect field. The residue-field normalization theorem also assumes quasi-separatedness: the proof now explicitly establishes this from properness of the component before applying it to its generic point with the identity function-field extension. The integral-scheme and normalization definitions identify its integral source with the component normalization. Steps 3 and 4 apply the exact retained new statements, with finite surjectivity and the generic-open condition already verified, and with finite composite component maps and smooth proper connected sources already available. Step 5 uses the current Euler-additivity statement on the coherent exact sequence. I also reread the current statement definitions, including pure dimension and reduced induced structures; no meaning or target hypothesis changed.

The archived duplicate-review statements in this report still agree with the corresponding current DAG statements. I reread local Stacks Tags 0C1R, 0AYT, 0BXR, 08AA, 089W and 0BY7, including their proofs where present. They confirm the quotient support/germs calculation, affine cohomology comparison, Euler additivity and genus convention used here. The Mathlib search questions and both child statements are unchanged, so the recorded search results were read and reused. The smooth, disconnected-two-lines, nodal, cuspidal and empty-family checks in the signed review continue to apply. This revision changes step 2 and the split report as well as documenting the rebase; it is not an unchanged re-push. The final dry run and push are performed only after this revision.

## Current landing-return repair (head ae96c5adab2)

The current return in coord/returns/Q104.md names ae96c5adab2 (2026-10-22 09:46 UTC) and again asks for a rebase after the side-completion landing refusal. The first resumed deliver.py --no-push invocation exited successfully at c77b423c768 after fetching the current DAG. I kept the complete retained split, both child statements, citations, all inherited arguments and searches.jsonl. The delivery tool constructs the rebased commit; no manual git command or write to the shared repository is involved.

I compared all fields of the sandbox item with the current shared item: only proof, proof_deps and split_report differ. The statement, source, statement dependencies, blueprint, Lean record, creation and historical review fields agree. Both new ids remain absent. I reread every current parent proof-dependency statement in full and checked all twelve citation quotes as literal substrings; no changed dependency invalidates the argument. I also compared all twenty archived duplicate-review statements with the current statements, and each agrees exactly. The item still has the released stage-1 repair order requiring at least two statement-only children and at most 3000 characters of assembly; its old reviewed flag does not supersede that order.

The proof is adjusted, rather than re-pushed unchanged. Step 2 now explicitly takes finiteness of each component normalization from clause (a) of lem-sc-normalization-properties; this is the hypothesis used to compose the component maps in step 4. Step 3 now explicitly checks that the normal open contains every component generic point before invoking lem-trf-finite-curve-quotient-stalk-euler. Step 1 already proves this by the reduced zero-dimensional local-ring argument. The existing properness, perfectness and quasi-separatedness checks in step 2 are retained. These changes introduce no new facts, statements or search questions, and the exact source/citation matches remain valid.

I reread local Stacks 0BXR, 0C1R, 0AYT, 08AA, 089W and 0BY7, with their proofs, and reopened Temkin's primary PDF at Appendix B Lemma B.1. The connected-source convention for pa=h1 is not imposed on X; the assembly uses 1-chi throughout. I read all retained search-log hits again: normalization and germ-injectivity infrastructure does not imply the quotient Euler result, and finite coproduct/pushforward infrastructure does not compute the family genus sum. Because both child statements and search questions are unchanged, those searches are reused without alteration. The smooth, nodal, cuspidal, disconnected and empty-family edge cases remain as checked below. The final server dry run is run after these edits and must exit before the push.

## Repair coverage

Returned point 1 is repaired by two new statement-only nodes of comparable argument size. Parent steps 1--2 preserve old steps 1--2; the quotient lemma carries old steps 3--7, the family lemma carries old steps 8--10 (with closed-immersion finiteness and composition also written in parent step 4), and parent step 5 carries old step 11. The full old argument is transcribed below, not shortened or blurred.

The quotient lemma is deliberately more general than normalization: a finite surjection, an arbitrary source, and an open isomorphism containing every component generic point suffice. For injectivity in this generality, on an affine U any section killed on f^(-1)(U) has zero residue at every point of U because f is surjective and maps of residue fields are injective. It lies in every prime, hence is zero since X is reduced. This retains the original componentwise integral-closure argument as its normalization specialization; the remaining old steps apply verbatim. Finite pushforward applies over the locally Noetherian X and its coherent structure sheaf on Y. Properness and pure dimension one make the closed support finite after its generic points have been excluded.

The family lemma concerns arbitrary finite maps h_i from smooth proper connected curves into any proper X, not necessarily a curve or reduced. It distributes exactly the cohomology/decomposition calculation, independent of the quotient lemma. The empty family is explicitly allowed. In the parent the finite h_i are established using their original factorizations.

## Review by Q104

I read Temkin Appendix B Lemma B.1 and its proof in the primary PDF, including the affine normalization cohomology comparison, skyscraper quotient, and global-functions calculation. Its standing connectedness assumption is not imported: the parent uses p_a=1-chi and retains the 1-v term for disconnected X. I read local Stacks varieties.tex Tag 0C1R, including the normalization inclusion and support argument; Tag 0AYT, including the germs decomposition, higher vanishing and Euler computation; Tag 08AA and its exact-sequence proof; Tag 0BXR for normalization finiteness and components; coherent.tex Tag 089W for affine cohomology. These are the sources of the parent and of both new nodes. The latter source references identify actual tags and TeX labels, rather than unstable section numbers.

For parent step 1 I opened the finite-type-over-Noetherian and reduced-algebraic-normalization statements: the former assumes a Noetherian base, supplied here by Spec k, and the latter supplies finite components, finite surjectivity and precisely the normal-open isomorphism. Reduced local rings at generic points are fields, so the open contains every required generic point. For parent step 2 I opened every cited statement: the integral-scheme definition gives reduced plus irreducible implies integral; the closed-immersion-proper lemma explicitly covers the composite into a proper base; normalization-properties (a),(c) supplies properness, dimension and smoothness over a perfect field; the normalization-in-residue-field-extension lemma supplies integrality for the identity extension of the component function field. The integral-closure definition identifies that normalization with the one here. Algebraic closedness gives perfectness, and integral implies nonempty connected. No quasi-separatedness issue arises for the proper components.

For step 3 I checked the new quotient statement itself, not its future proof: it assumes exactly the finite surjectivity, reduced proper pure-one target and generic-open isomorphism available from steps 1--2. Its conclusion explicitly includes injectivity, coherence, finite closed support, finite-dimensional stalks and the Euler sum, so no conclusion is smuggled in through a definition or source tag. For step 4 I read the finite-morphism definition and finite-radicial-basechange statement: finiteness of A/I over A is the elementary cyclic-module calculation, and the latter statement includes composition for finite maps independently of radiciality. The family lemma's required smooth proper connected curves are step 2 and its required finite k-maps are those composites. Its statement supplies the decomposition and Euler sum. Step 5 uses the exact coherent sequence from step 3; I opened Euler-additive and checked it assumes only proper X and coherent terms. It gives exactly the equality used, followed by integer subtraction and the stated p_a definition.

I checked delivery-errors B--E: the new statements introduce all objects, define the support, germs, cokernel and pushforward in words/formulas, and cite existing definition nodes for their other notions; neither contains proof steps. All non-elementary parent facts cite a statement that says them; citations.json reproduces those statements verbatim. All parent proof dependencies are the union of uses; the two new nodes have no proof edges and their definition edges do not point upward. Every parent step is under 2000 characters. No SGA source or change of the historical unit route occurs. The new generic-tool uses are declared in split_report.tool_uses as the standing brief allows; no maintainer-owned top-level tool_uses was set. The source's connected-case proof is extended explicitly, rather than silently equating p_a with h^1 for disconnected curves.

Small cases checked: X smooth and f the identity gives F=0, empty S and zero Euler contribution; two disjoint projective lines give p_a=-1 and v=2; a nodal cubic has one genus-zero normalized component and a one-dimensional quotient, giving p_a=1; a cuspidal cubic has the same delta=1 calculation without nodality. A finite partial normalization is covered by the generic quotient lemma, and even an extra finite point over a closed point is permitted, confirming it is not a restatement of the normalization-only node. Surjectivity and reducedness are essential for injectivity; they are present. In the family lemma an empty family gives B=0; one rational curve gives chi=1; one genus-one curve gives chi=0; a degree-d finite map does not multiply chi(h_*O_C) by d, since affine cohomology preserves the source groups. The conclusions use vector-space dimension over k, not unweighted module length over a nontrivial residue field.

## Searches and blueprint references

Whole-DAG statement/concept and source-tag searches and whole-blueprint searches were run before creating the nodes: normalization, normalization genus, finite support, finite birational, finite morphism cohomology, normalization quotient, coherent stalks, curve genus, finite pushforward and Euler characteristic curve. The nearest blueprint ancestor is lem-trf-local-term-locality via lem-trf-curve-p1-tree-local-criterion and lem-trf-valuation-exceptional-local-criterion. The child via lists prepend this item and the precise inherited proof ranges are named in from.place. No equivalent blueprint statement was found. Existing normalization/exact-sequence nodes were read and distinguished below.

Each new node has its own natural-language search, a second phrasing, Loogle, LeanSearch and Mathlib grep, all run through msearch.py. searches.jsonl contains the exact tools/queries/digests, retained unchanged. All services answered. Returned normalization and germ results do not give the finite-support coherent quotient calculation; returned finite coproduct, properness and additive pushforward results do not give the coherent Euler/genus identity. I read the candidate signatures and source definitions of normalization, finite maps and pushforward. No exact match or one-line specialization was found. Original item searches are retained without repeating them because the parent statement and its search question did not change.

## Not duplicates

- lem-trf-finite-curve-quotient-stalk-euler vs lem-trf-integral-filtration-euler-difference: the existing node assumes a coherent filtration with integral-ideal quotients and computes the difference under an invertible twist; it neither proves injectivity and finite support for a generically isomorphic finite surjection nor identifies its defect global sections with stalks. Taking the twist trivial only gives zero difference, not the new Euler/stalk identity.

- lem-trf-finite-smooth-curve-family-euler vs lem-trf-finite-ideal-twist-cohomology-comparison: the existing node gives coherence, projection and edge comparisons for an ideal-twisted coherent module along one finite map; it has no smooth proper connected source hypotheses and no global-functions, higher-vanishing or genus-sum conclusion. Its untwisted specialization supplies only the edge comparison, not the new finite-family Euler calculation.

- lem-trf-finite-curve-quotient-stalk-euler vs lem-pc-chi-zero-dim-support: the existing node assumes coherent zero-dimensional support and gives higher vanishing and chi=dim global sections; the new lemma must first prove injectivity, coherence and finite support and then identify global sections with stalks.

- lem-trf-finite-curve-quotient-stalk-euler vs lem-pc-finite-scheme-cohomology-tensor: the existing node starts with Spec of a finite-dimensional algebra and an invertible twist; the new lemma establishes injectivity and finite support for a quotient on a one-dimensional target.

- lem-trf-finite-curve-quotient-stalk-euler vs lem-pc-zero-support-finite-scheme: the existing node assumes zero-dimensional coherent support and constructs its annihilator support scheme; the new lemma proves support is finite for a finite generically-isomorphic map and identifies the germs/Euler contribution.

- lem-trf-finite-curve-quotient-stalk-euler vs lem-trf-nodal-curve-normalization-euler: the existing node assumes connectedness and nodality and computes the structure-sheaf Euler characteristic by node counts; the new lemma neither assumes nodality nor calculates the genus or structure-sheaf Euler characteristic.

- lem-trf-finite-curve-quotient-stalk-euler vs lem-trf-nodal-normalization-quotient: the existing node assumes a connected nodal curve and identifies each normalization defect with k; the new lemma treats arbitrary finite surjective generically-isomorphic maps and arbitrary finite stalk dimensions.

- lem-trf-finite-curve-quotient-stalk-euler vs lem-trf-normalization-singular-skyscraper: the existing node treats componentwise normalization over an algebraically closed field and completion/skyscraper modules; the new lemma treats any finite surjective generically-isomorphic map over any field and computes the global germs/Euler sum, which the existing statement does not give.

- lem-trf-finite-smooth-curve-family-euler vs def-sc-genus: the existing statement concerns The genus of a curve; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-smooth-curve-family-euler vs def-weil-pbc-formal-functions-finite-pullback: the existing statement concerns Canonical finite-level pullback through the local base change; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-smooth-curve-family-euler vs def-weil-pbc-formal-functions-local-comparison: the existing statement concerns Local-base-change cohomology and canonical germ comparison; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-smooth-curve-family-euler vs lem-pc-euler-additive: the existing statement concerns Additivity of the Euler characteristic; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-smooth-curve-family-euler vs lem-pc-genus-agrees-sc: the existing statement concerns Agreement with the genus of file 06; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-smooth-curve-family-euler vs lem-weil-pbc-affine-morphism-cohomology-edge: the existing statement concerns Cohomology along an affine morphism: the edge map is an isomorphism; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-smooth-curve-family-euler vs lem-weil-pbc-formal-functions-finite-quotient-comparison: the existing statement concerns Finite quotient and fibre cohomology comparison; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-smooth-curve-family-euler vs lem-weil-pbc-formal-functions-finite-quotient-iso: the existing statement concerns Canonical quotient-system isomorphism and pullback factorization; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-smooth-curve-family-euler vs lem-weil-pbc-formal-functions-finite-quotient-iso-b: the existing statement concerns quotient-system isomorphism and factorization; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-smooth-curve-family-euler vs lem-weil-pbc-formal-functions-finite-quotient-iso-r: the existing statement concerns linear pullback factorization through a quotient-system isomorphism; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-smooth-curve-family-euler vs lem-weil-pbc-formal-functions-finite-quotient-maps: the existing statement concerns Finite canonical pullback carries the local germ formula to Theta; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-smooth-curve-family-euler vs lem-weil-pbc-formal-functions-local-dictionary: the existing statement concerns Geometric dictionary for stalk and infinitesimal quotient cohomology; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-smooth-curve-family-euler vs lem-weil-pbc-formal-functions-local-stalk-comparison: the existing statement concerns Canonical uncompleted local stalk comparison; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-smooth-curve-family-euler vs lem-weil-pbc-graded-finiteness-cohomology: the existing statement concerns Cohomology of a finite type graded module over f^*B~ is a finite B-module; the new lemma computes the coherent pushforward Euler characteristic for a whole finite family of smooth proper connected source curves into arbitrary proper X, including the decomposition, affine edge maps and 1-genus values. The existing statement alone does not assert that finite-family calculation.

- lem-trf-finite-curve-quotient-stalk-euler vs lem-trf-reduced-curve-normalization-genus: the child proves the quotient contribution for a general finite map and says nothing about component smoothness, genera or the arithmetic genus of X. The parent still establishes the component geometry and assembles both independent contributions.
- lem-trf-finite-smooth-curve-family-euler vs lem-trf-reduced-curve-normalization-genus: the child has no normalization or quotient sheaf, and no formula for p_a(X); it treats arbitrary finite images of independently given smooth curves.
- lem-trf-finite-curve-quotient-stalk-euler vs lemma-weil-pbc-normalization-exact-sequence: the existing statement is about constant finite-coefficient etale sheaves and base-change connecting maps, whereas the child is about coherent structure-sheaf modules and their k-vector-space Euler characteristic.
- lem-trf-finite-curve-quotient-stalk-euler vs lem-weil-pbc-zero-dimensional-sections-stalks: the existing statement concerns geometric etale stalks on a zero-dimensional scheme; the child concerns ordinary module stalks on a proper curve and establishes its quotient support.
- lem-trf-finite-smooth-curve-family-euler vs lem-weil-pbc-affine-morphism-cohomology-edge: the existing statement supplies a single affine edge isomorphism for a quasi-coherent module, but no finite-family decomposition or genus/Euler calculation.

## Complete inherited arguments assigned to the new workers

The following text is the full returned argument, preserved verbatim with its uses, organized by its new owner. This is handoff proof material in the report, not proof text in the statement-only child JSON.

### lem-trf-finite-curve-quotient-stalk-euler

Old step 3:

The map $\mathcal O_X\to\nu_*\mathcal O_{\widetilde X}$ is injective. Indeed, on an affine open $U\subseteq X$, if a section $s$ pulls back to zero, its restriction to each $U\cap X_i$ is zero: normalization of an integral scheme embeds its affine coordinate ring into its function field, by the integral-closure construction [def-sc-normalization]. Every point of $U$ lies on a component, so $s$ vanishes in every residue field. In the notation of [lem-weil-pbc-reduced-induced-closed-subscheme](1), this says $s\in\mathcal I_X(U)=\sqrt{(0)}$. This ideal is zero since $\mathcal O_X(U)$ is reduced [def-pc-reduced-scheme]. Consequently $0\to\mathcal O_X\to B\to F\to0$, with $B=\nu_*\mathcal O_{\widetilde X}$, is exact by the definition of the quotient sheaf $F$.

Cited statements: def-sc-normalization, lem-weil-pbc-reduced-induced-closed-subscheme, def-pc-reduced-scheme.

Source: {"document": "literature/stacks-project/varieties.tex", "place": "Tag 0C1R (lemma-prepare-delta-invariant), injectivity in the normalization sequence; schemes.tex Tags 01J3 (lemma-reduced-closed-subscheme), 01J1 (lemma-reduced)."}.

Old step 4:

Since $X$ is locally Noetherian and $\nu$ is finite, [lem-weil-pbc-finite-pushforward-coherent] applied to $\mathcal O_{\widetilde X}$ gives coherence of $B$. The cokernel clause of [lem-weil-pbc-coherent-kernel-cokernel-locnoeth] gives coherence of $F$ in step 3. Its support $S=\{y:F_y\ne0\}$ is closed by [lem-weil-pbc-finite-type-module-support-closed].

Cited statements: lem-weil-pbc-finite-pushforward-coherent, lem-weil-pbc-coherent-kernel-cokernel-locnoeth, lem-weil-pbc-finite-type-module-support-closed.

Source: {"document": "literature/stacks-project/coherent.tex", "place": "Tags 01Y6 (lemma-finite-pushforward-coherent), 01Y0 (lemma-coherent-abelian-Noetherian); morphisms.tex Tag 056J (lemma-support-finite-type)."}.

Old step 5:

On the dense normal open $N$ of step 1 the normalization is an isomorphism [lem-weil-pbc-reduced-algebraic-normalization-field-change], so $F|_N=0$. Every generic point of an irreducible component belongs to $N$. A closed subset of a one-dimensional Noetherian space avoiding all component generic points has dimension at most zero: a chain of two distinct irreducible closed subsets inside it would, after containment in a component, extend to a chain of length two in that component. Thus $\dim S\le0$. Apply [lem-sc-dim0-finite] to the closed subset $S$ of the finite-type $k$-scheme $X$: it is a finite set of closed points.

Cited statements: lem-weil-pbc-reduced-algebraic-normalization-field-change, lem-sc-dim0-finite.

Source: {"document": "literature/stacks-project/varieties.tex", "place": "Tags 0BXR (lemma-normalization-locally-algebraic), 0C1R (lemma-prepare-delta-invariant); finiteness of zero-dimensional closed subsets as in lem-sc-dim0-finite."}.

Old step 6:

The germs map $\Gamma(X,F)\to\bigoplus_{y\in S}F_y$ is an isomorphism. It is injective because a section with zero germs at $S$ has zero germs everywhere. For surjectivity choose a representative $t$ of a germ at $y$ on an open neighbourhood $U_y$ avoiding $S\setminus\{y\}$. On $U_y\setminus\{y\}$ the sheaf is zero, so $t$ glues with zero on $X\setminus\{y\}$ to a global section with just that germ. Summing these sections over the finite set $S$ realizes any tuple. These operations are $k$-linear. This is the elementary sheaf-gluing argument for part (2) of Stacks Tag 0AYT, and also works when $S$ is empty.

Cited statements: .

Source: {"document": "literature/stacks-project/varieties.tex", "place": "Tag 0AYT (lemma-chi-tensor-finite), part (2); the germs and gluing argument is written out here."}.

Old step 7:

The hypotheses of [lem-pc-chi-zero-dim-support] hold for $F$: it is coherent on the proper scheme $X$ and has zero-dimensional support. Hence its higher cohomology vanishes and $\chi(X,F)=\dim_k\Gamma(X,F)$. This space is finite-dimensional by [lem-pc-euler-characteristic-well-defined]. The isomorphism in step 6 therefore also makes each $F_y$ finite-dimensional, and gives $\chi(X,F)=\sum_{y\in S}\dim_kF_y=\sum_{y\in X\text{ closed}}\delta_X(y)$; the last sum is finite since the other stalks are zero.

Cited statements: lem-pc-chi-zero-dim-support, lem-pc-euler-characteristic-well-defined.

Source: {"document": "literature/stacks-project/varieties.tex", "place": "Tag 0AYT (lemma-chi-tensor-finite), parts (2)--(4); finiteness of coherent cohomology on a proper scheme."}.

### lem-trf-finite-smooth-curve-family-euler

Old step 8:

For each $i$, the proper finite-type curve $\widetilde X_i$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. Apply [lem-sc-noetherian-cohomology-above-dimension] in dimension one to obtain $H^q(\widetilde X_i,\mathcal O)=0$ for $q>1$. The smooth proper connected curve has $H^0(\widetilde X_i,\mathcal O)=k$ by [lem-sc-global-functions]. Its first cohomology has dimension $g_i$ by [def-sc-genus]. Thus the Euler sum of [def-pc-euler-characteristic] gives $\chi(\widetilde X_i,\mathcal O)=1-g_i$.

Cited statements: lem-weil-pbc-finite-type-over-noetherian, lem-sc-noetherian-cohomology-above-dimension, lem-sc-global-functions, def-sc-genus, def-pc-euler-characteristic.

Source: {"document": "literature/stacks-project/curves.tex", "place": "Tag 0BY7 (definition-genus); cohomology.tex Tag 02UZ (proposition-vanishing-Noetherian); varieties.tex Tag 0BUG (lemma-proper-geometrically-reduced-global-sections); morphisms.tex Tag 01T6."}.

Old step 9:

Let $h_i:\widetilde X_i\to X$ be the composite through the closed immersion $X_i\hookrightarrow X$. A closed immersion is finite directly from [def-weil-finite-integral-morphism]: the inverse image of $\operatorname{Spec}A$ is $\operatorname{Spec}(A/I)$, a cyclic $A$-module. Since $\widetilde X_i\to X_i$ is finite, stability under composition [lem-trf-finite-radicial-basechange] makes $h_i$ finite. Its pushforward $G_i=h_{i,*}\mathcal O_{\widetilde X_i}$ is coherent by [lem-weil-pbc-finite-pushforward-coherent]. Sections of a sheaf on a disjoint union are the product of the sections on its summands by the sheaf gluing axiom. Hence the definition of direct image gives $B=\prod_iG_i=\bigoplus_iG_i$, since there are finitely many summands.

Cited statements: def-weil-finite-integral-morphism, lem-trf-finite-radicial-basechange, lem-weil-pbc-finite-pushforward-coherent.

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "Tag 01WH (definition-integral), definition of finite morphism; finite composition; coherent.tex Tag 01Y6 (lemma-finite-pushforward-coherent)."}.

Old step 10:

For each finite $h_i$, which is affine by [def-weil-finite-integral-morphism], [lem-weil-pbc-affine-morphism-cohomology-edge] identifies $H^q(X,G_i)$ with $H^q(\widetilde X_i,\mathcal O)$ for every $q$, compatibly with the $k$-action from the structure maps. Taking the alternating dimensions yields $\chi(X,G_i)=1-g_i$ by step 8. Apply [lem-pc-euler-additive] successively to the split exact sequences of partial sums of the coherent modules $G_i$ (finite sums are coherent by [lem-weil-pbc-coherent-kernel-cokernel-locnoeth]). Step 9 then gives $\chi(X,B)=\sum_i(1-g_i)=v-\sum_i g_i$.

Cited statements: def-weil-finite-integral-morphism, lem-weil-pbc-affine-morphism-cohomology-edge, lem-pc-euler-additive, lem-weil-pbc-coherent-kernel-cokernel-locnoeth.

Source: {"document": "literature/stacks-project/coherent.tex", "place": "Tag 089W (lemma-relative-affine-cohomology); varieties.tex Tag 08AA (lemma-euler-characteristic-additive); coherent.tex Tag 01Y0."}.

The parent retains old steps 1--2 in its first two steps and old step 11 in its last step. The extraction therefore loses none of the eleven arguments.

## Duplicate-review statement record

### def-sc-genus

Let $C$ be a proper smooth connected curve over
an algebraically closed field $k$. The *genus* of $C$ is

$$
g(C):=\dim_kH^1(C,\mathcal O_C),
$$

finite because coherent cohomology of a proper scheme over a field
is finite-dimensional (coherent higher direct images of a proper
morphism are coherent: *reference: Stacks Project, Cohomology
of Schemes, Proposition 30.19.1, [Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)*; this is the genus of
Stacks Project, Algebraic Curves, Definition 53.8.1,
[Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7), which
defines $g=\dim_kH^1(X,\mathcal O_X)$ for a proper scheme $X$ of
dimension one with $H^0(X,\mathcal O_X)=k$, the present $C$).
Equivalently, by duality
$g=\dim_kH^0(C,\Omega^1_{C/k})$ (*reference: Stacks Project,
Algebraic Curves, Lemma 53.4.1, [Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2), parts (5) and
(6)*). (For a smooth separated, not necessarily proper, connected curve the
genus used in this blueprint is the genus of a compactification
$\overline C$ of $C$, i.e. of a proper smooth connected curve containing
$C$ as an open subscheme with finite complement; this convention is
fixed explicitly at the single place where it is used, and it is the
compactification lemma below that provides the compactification.)

### def-weil-pbc-formal-functions-finite-pullback

Let f:X→Y be a scheme morphism, y∈Y, F an O_X-module and p,n≥0. Put X′=Spec O_y×_Y X with projection g′, and X_n=Spec(O_y/m_y^(n+1))×_Y X with projection i_n [def-pc-fibre-product, def-weil-pbc-formal-fibre-cohomology]. Define i′_n:X_n→X′ by pullback.lift from its projection to Spec O_y and i_n; thus i′_n followed by g′ equals i_n. Write F′=g′*F and F_n=i_n*F [def-pc-module-pullback]. Define the h-map F′→i′_(n*)F_n to be the adjoint, under the tensor-pullback adjunction of g′ pinned by its sectionwise unit [lem-pc-module-pullback-adjunction], of the unit F→i_(n*)F_n followed by the projection-equality and pushforward-composition identifications. Define formalFunctionsFinitePullback to be the additive cohomology map of this h-map [def-weil-pbc-module-cohomology-fmap], from formalFunctionsLocalCohomology [def-weil-pbc-formal-functions-local-comparison] to formalFibreCohomologyLocal [def-weil-pbc-formal-fibre-cohomology].

### def-weil-pbc-formal-functions-local-comparison

Let f:X→Y be a scheme morphism, y∈Y, F an O_X-module and p≥0 [def-pc-fibre-product, def-pc-module-pullback, pqf-def-cohomology, def-weil-pbc-module-stalk]. Put A=O_(Y,y), X′=Spec(A)×_Y X, g′:X′→X and f′:X′→Spec(A). Define H=H^p(X′,g′*F) with A-action through Gamma-Spec and f′.appTop. For an A-linear map a:(R^p f_*F)_y→H, define IsFormalFunctionsLocalComparison by the following formula for every resolution I of F, resolution K of g′*F, neighbourhood V of y, open comparison choices D [def-weil-pbc-flat-base-change-open-choices] and class xi on f^{-1}V. Restriction to W=g′^{-1}(f^{-1}V) of a applied to the germ of the resolutionSectionClass of xi is moduleCohomologyFMap of the restricted g′-map D.psi applied to xi [def-weil-pbc-module-cohomology-fmap]. All class maps and restriction units are the canonical ones in the Lean formula.

### lem-pc-chi-zero-dim-support

Let $k$ be a field, $X$ a scheme proper over $k$ [def-weil-proper-morphism] and $\mathcal F$ a coherent $\mathcal O_X$-module [pqf-def-coherent] whose support $\operatorname{Supp}(\mathcal F)=\{x\in X:\mathcal F_x\ne0\}$ has dimension $\le0$ [def-kun-topological-krull-dimension]. Then, with the cohomology $H^i(X,-)$ and Euler characteristic $\chi(X,-)$ of [def-pc-euler-characteristic]:\n\n1. $H^i(X,\mathcal F)=0$ for all $i>0$;\n1. $\chi(X,\mathcal F)=\dim_kH^0(X,\mathcal F)=\dim_k\Gamma(X,\mathcal F)$;\n1. for every invertible $\mathcal O_X$-module $\mathcal N$ [def-sc-invertible-module] the module $\mathcal F\otimes_{\mathcal O_X}\mathcal N$ is coherent with the same support, and $\chi(X,\mathcal F\otimes_{\mathcal O_X}\mathcal N)=\chi(X,\mathcal F)$.

### lem-pc-euler-additive

Let $k$ be a field, $X$ a proper scheme over $k$, and let

$$
0\to\mathcal{F}_1\to\mathcal{F}_2\to\mathcal{F}_3\to0
$$

be a short exact sequence of coherent $\mathcal{O}_X$-modules. Then

$$
\chi(X,\mathcal{F}_2)=\chi(X,\mathcal{F}_1)+\chi(X,\mathcal{F}_3).
$$

Moreover, for a morphism $f:Y\to X$ of proper $k$-schemes and a
coherent $\mathcal{O}_Y$-module $\mathcal{G}$:

$$
\chi(Y,\mathcal{G})=\sum_{i\ge0}(-1)^i\chi(X,R^if_*\mathcal{G}).
$$

### lem-pc-finite-scheme-cohomology-tensor

Let $k$ be a field, let $A$ be a finite-dimensional $k$-algebra [def-weil-finite-dimensional-subspace] [def-weil-vector-space-dimension], let $T=\operatorname{Spec}(A)$ [def-pc-scheme], let $\mathcal G$ be a coherent $\mathcal O_T$-module [pqf-def-coherent], and let $\mathcal L$ be an invertible $\mathcal O_T$-module [def-sc-invertible-module]. Then $H^q(T,\mathcal G)=0$ and $H^q(T,\mathcal G\otimes_{\mathcal O_T}\mathcal L)=0$ for every $q>0$ (cohomology of [pqf-def-cohomology], tensor product of [def-pur-sheaf-tensor-product]), both $\Gamma(T,\mathcal G)$ and $\Gamma(T,\mathcal G\otimes\mathcal L)$ are finite-dimensional $k$-vector spaces, and $\dim_k\Gamma(T,\mathcal G\otimes\mathcal L)=\dim_k\Gamma(T,\mathcal G)$. Consequently, the Euler characteristics of [def-pc-euler-characteristic] are defined and satisfy $\chi(T,\mathcal G)=\dim_k\Gamma(T,\mathcal G)$ and $\chi(T,\mathcal G\otimes\mathcal L)=\chi(T,\mathcal G)$.

### lem-pc-genus-agrees-sc

Let $k$ be an algebraically closed field and $C$ a
smooth projective curve over
$k$ (or, more generally, a proper smooth connected curve in the sense of
[def-sc-curves] with $\dim H^0(C,\mathcal{O}_C)=1$). Then the genus
$g(C)$ of [def-pc-genus] equals the genus of
[def-sc-genus].

### lem-pc-zero-support-finite-scheme

Let $k$ be a field, let $X$ be a scheme of finite type over $k$ [def-pc-scheme] [def-pc-morphism-conventions], let $\mathcal F$ be a coherent $\mathcal O_X$-module [pqf-def-coherent], and suppose that $\operatorname{Supp}(\mathcal F)$ has dimension at most zero [def-kun-topological-krull-dimension]. Let $\mathcal N$ be an invertible $\mathcal O_X$-module [def-sc-invertible-module]. Then there exist a finite-dimensional $k$-algebra $A$ [def-weil-finite-dimensional-subspace] [def-weil-vector-space-dimension], a closed immersion $i:\operatorname{Spec}(A)\hookrightarrow X$ [def-weil-closed-immersion], and a coherent module $\mathcal G$ on $\operatorname{Spec}(A)$ [pqf-def-coherent] such that the underlying set of $\operatorname{Spec}(A)$ is $\operatorname{Supp}(\mathcal F)$, $\mathcal F\cong i_*\mathcal G$, and $\mathcal F\otimes_{\mathcal O_X}\mathcal N\cong i_*(\mathcal G\otimes i^*\mathcal N)$. In particular, $\mathcal F\otimes\mathcal N$ is coherent and has the same support as $\mathcal F$. For every $q\ge0$, the closed immersion gives canonical isomorphisms $H^q(X,\mathcal F)\cong H^q(\operatorname{Spec}(A),\mathcal G)$ and $H^q(X,\mathcal F\otimes\mathcal N)\cong H^q(\operatorname{Spec}(A),\mathcal G\otimes i^*\mathcal N)$, where cohomology and global sections are those of [def-pc-euler-characteristic].

### lem-trf-nodal-curve-normalization-euler

Let $k$ be an algebraically closed field [def-weil-algebraic-closure]. Let $B$ be a proper reduced connected $k$-scheme of pure dimension one [def-weil-proper-morphism, def-pc-reduced-scheme, def-kun-topological-krull-dimension, def-weil-connected-scheme], nodal at every nonsmooth point in the sense that its completed local rings are $k[[u,v]]/(uv)$ [def-weil-pbc-adic-completion, def-weil-pbc-multivariate-power-series], and let $B_1,\ldots,B_v$ be its irreducible components [def-weil-irreducible-components]. For each $i$, let $\widetilde B_i\to B_i$ be the normalization [def-sc-normalization], assumed smooth proper connected, and put $g_i=\dim_k H^1(\widetilde B_i,\mathcal O_{\widetilde B_i})$ [def-sc-genus]. Let $e$ be the number of internal nodes of $B$, counting a self-node once. Then, for the Euler characteristic of the structure sheaf [def-pc-euler-characteristic], $$\chi(B)=v-e-\sum_{i=1}^{v}g_i.$$

### lem-trf-nodal-normalization-quotient

Let $k$ be an algebraically closed field [def-weil-algebraic-closure]. Let $B$ be a proper reduced connected $k$-scheme of pure dimension one [def-weil-proper-morphism, def-pc-reduced-scheme, def-kun-topological-krull-dimension, def-weil-connected-scheme], nodal at every nonsmooth point with completed local ring $k[[u,v]]/(uv)$ [def-weil-pbc-adic-completion, def-weil-pbc-multivariate-power-series]. Let $B_1,\ldots,B_v$ be its irreducible components [def-weil-irreducible-components], let $\nu_i:\widetilde B_i\to B_i$ be their normalizations [def-sc-normalization], and let $\nu:\widetilde B:=\coprod_i\widetilde B_i\to B$ be the induced finite normalization map. If $N$ is the finite set of nonsmooth points and $e=|N|$, then there is a short exact sequence of coherent $\mathcal O_B$-modules $0\to\mathcal O_B\to\nu_*\mathcal O_{\widetilde B}\to Q\to0$ with $Q\cong\bigoplus_{x\in N}i_{x,*}k$. In particular $Q$ is supported on $N$ and $\chi(B,Q)=e$ [def-pc-euler-characteristic].

### lem-trf-normalization-singular-skyscraper

Let $k$ be an algebraically closed field [def-weil-algebraic-closure] and $X$ a reduced finite-type $k$-scheme [def-pc-reduced-scheme, def-weil-finite-type-morphism] all of whose irreducible components have dimension one [def-weil-irreducible-components, def-kun-topological-krull-dimension]. Let $\nu:X^\nu\to X$ be its componentwise normalization [def-weil-pbc-reduced-normalization], and let $S$ be the set of points at which $X\to\operatorname{Spec}k$ is not smooth [def-sbc-smooth-morphisms]. Then $S$ is a finite set of closed points, each with residue field $k$ via the structural map, $\nu$ is finite [def-weil-finite-integral-morphism], and there is a short exact sequence of coherent $\mathcal O_X$-modules [pqf-def-coherent]
$$0\longrightarrow\mathcal O_X\longrightarrow\nu_*\mathcal O_{X^\nu}\longrightarrow Q\longrightarrow0,$$
where $Q\cong\bigoplus_{x\in S}\mathscr S_x(M_x)$. Here $A_x=\mathcal O_{X,x}$, $C_x=(\nu_*\mathcal O_{X^\nu})_x$ is the integral closure [def-weil-pbc-integral-closure] of $A_x$ in its total ring of fractions (the localization obtained by inverting all non-zero-divisors), $M_x=C_x/A_x$ is a nonzero finite-length $A_x$-module (it admits a finite filtration with simple successive quotients), and $\mathscr S_x(M_x)(U)=M_x$ if $x\in U$, and $0$ otherwise, with $\mathcal O_X(U)$ acting by germs in $A_x$. Writing $\mathfrak m_x$ for the maximal ideal of $A_x$, the completions [def-weil-pbc-adic-completion]
$$\widehat A_x=\varprojlim_n A_x/\mathfrak m_x^n,\qquad \widehat C_x=\varprojlim_n C_x/\mathfrak m_x^nC_x$$
have the following properties: $\widehat C_x$ is the integral closure of $\widehat A_x$ in its total ring of fractions, and the natural map induces an $A_x$-linear isomorphism $M_x\cong\widehat C_x/\widehat A_x$.

### lem-weil-pbc-affine-morphism-cohomology-edge

Let $h:X\to S$ be an affine morphism of schemes [pqf-def-affine-morphism] (for instance a closed immersion [def-weil-closed-immersion]) and $\mathcal F$ a quasi-coherent $\mathcal O_X$-module [pqf-def-coherent]. Then $R^ph_*\mathcal F=0$ for $p>0$ [pqf-def-cohomology], and for every $p\ge0$ the edge map $e_{h,\mathcal F}:H^p(S,h_*\mathcal F)\to H^p(X,\mathcal F)$ of [def-weil-pbc-module-cohomology-fmap] (c) (the map induced by the $h$-map $\mathrm{id}_{h_*\mathcal F}$) is an isomorphism of $\mathcal O_S(S)$-modules.

### lem-weil-pbc-formal-functions-finite-quotient-comparison

Let f:X→Y be proper, Y locally Noetherian, F coherent, y∈Y and p≥0 [def-weil-proper-morphism, pqf-def-locnoeth, pqf-def-coherent]. Put A=O_(Y,y), X′=Spec A×_Y X, F′=g′*F, J=m_y O_(X′), C=H^p(X′,-) restricted to A, H=C(F′), M=(R^p f_*F)_y [def-pc-fibre-product, def-pc-module-pullback, def-nagata-extended-ideal, pqf-def-cohomology, def-weil-pbc-formal-functions-local-comparison]. There are an A-linear natural isomorphism b from the inverse system C(F′/J^(n+1)F′) to the infinitesimal fibre cohomology system restricted from the completed local ring [def-weil-pbc-coherent-formal-module, def-weil-pbc-formal-fibre-cohomology], and A-linear maps r_n:H→H^p(X_n,F_n) with r_n(z)=b_n C(q_n)(z). For every A-linear a:M→H satisfying IsFormalFunctionsLocalComparison, (r_n).comp a satisfies IsFormalFunctionsTheta at every n [def-weil-pbc-formal-functions-local-comparison, def-weil-pbc-formal-fibre-cohomology]. This states no existence of a stalk equivalence.

### lem-weil-pbc-formal-functions-finite-quotient-iso

Let f:X→Y be proper, Y locally Noetherian, F coherent, y∈Y and p≥0 [def-weil-proper-morphism,pqf-def-locnoeth,pqf-def-coherent]. Put A=O_y, X′=Spec A×_Y X, F′=g′*F, J=m_y O_(X′) and C=H^p(X′,-) restricted to A. There are an A-linear natural isomorphism b from C(F′/J^(n+1)F′) to the infinitesimal fibre cohomology system restricted from the completed local ring, and A-linear maps r_n:H^p(X′,F′)→H^p(X_n,F_n). For every n,z, r_n(z)=b_n C(q_n)(z) and r_n(z)=formalFunctionsFinitePullback(f,y,F,p,n)(z) [def-weil-pbc-formal-functions-finite-pullback]. This is the quotient-system/pullback part only, without a stalk comparison or Theta condition.

### lem-weil-pbc-formal-functions-finite-quotient-iso-b

Finite quotient-system isomorphism with the quotient-unit factorization, as stated in the Lean declaration.

### lem-weil-pbc-formal-functions-finite-quotient-iso-r

Given a quotient-system isomorphism whose components equal finite pullback, there are linear maps whose components satisfy both displayed formulas, as stated in the Lean declaration.

### lem-weil-pbc-formal-functions-finite-quotient-maps

Let f:X→Y be proper, Y locally Noetherian, F coherent, y∈Y and p,n≥0 [def-weil-proper-morphism,pqf-def-locnoeth,pqf-def-coherent]. Let r:formalFunctionsLocalCohomology(f,y,F,p)→H^p(X_n,F_n) be A-linear whose underlying function equals formalFunctionsFinitePullback [def-weil-pbc-formal-functions-finite-pullback]. For every A-linear a:formalFunctionsStalk(f,y,F,p)→formalFunctionsLocalCohomology(f,y,F,p) satisfying IsFormalFunctionsLocalComparison [def-weil-pbc-formal-functions-local-comparison], r composed with a satisfies IsFormalFunctionsTheta at level n [def-weil-pbc-formal-fibre-cohomology]. There is no quotient-system isomorphism in this statement.

### lem-weil-pbc-formal-functions-local-dictionary

Let $f:X\to Y$ be proper [def-weil-proper-morphism], with $Y$ locally Noetherian [pqf-def-locnoeth], $\mathcal F$ coherent [pqf-def-coherent], $y\in Y$ and $p\ge0$. Put $A=\mathcal O_{Y,y}$, $\mathfrak m=\mathfrak m_y$, $c:\operatorname{Spec}A\to Y$ the canonical map [lem-weil-pbc-spec-local-ring-canonical-morphism], $X'=\operatorname{Spec}A\times_YX$ with projections $f':X'\to\operatorname{Spec}A$, $g':X'\to X$ [def-pc-fibre-product], and $\mathcal F'=g'^*\mathcal F$ [def-pc-module-pullback]. Let $J=\mathfrak m\mathcal O_{X'}$ [def-nagata-extended-ideal] and let $C$ be $H^p(X',-)$ [pqf-def-cohomology] regarded as an $A$-module by $A\to\Gamma(X',\mathcal O_{X'})$. Put $M=(R^pf_*\mathcal F)_y$ [def-weil-pbc-module-stalk], $Q_n=C(\mathcal F'/J^{n+1}\mathcal F')$ with its quotient transitions [def-weil-pbc-coherent-formal-module], and $B_n=H^p(X_n,\mathcal F_n)$ with the canonical transitions and scalar actions [def-weil-pbc-formal-fibre-cohomology]. Then $\mathcal F'$ is coherent, and there exist an $A$-linear equivalence $a:M\to C(\mathcal F')$, an isomorphism of inverse systems $b:Q\to B$ after restricting scalars from $\widehat A$ to $A$ [def-weil-pbc-adic-completion], and $A$-linear maps $\kappa_n:M\to B_n$ satisfying IsFormalFunctionsTheta [def-weil-pbc-formal-fibre-cohomology], such that $\kappa_n(z)=b_n(C(q_n)(a(z)))$ for every $n\ge0$ and $z\in M$, where $q_n:\mathcal F'\to\mathcal F'/J^{n+1}\mathcal F'$ is the quotient projection. This assertion concerns uncompleted cohomology and finite-level quotient systems; it asserts no isomorphism involving a completed cohomology module or a limit.

### lem-weil-pbc-formal-functions-local-stalk-comparison

Let f:X→Y be proper, Y locally Noetherian, F coherent, y∈Y and p≥0 [def-weil-proper-morphism, pqf-def-locnoeth, pqf-def-coherent]. Write A=O_(Y,y) and H=H^p(Spec(A)×_Y X,g′*F) as an A-module [def-weil-pbc-formal-functions-local-comparison]. There exists an A-linear equivalence a:(R^p f_*F)_y→H satisfying IsFormalFunctionsLocalComparison [def-weil-pbc-formal-functions-local-comparison], i.e. it sends each germ of a neighbourhood cohomology class to its pullback to the local base change. No quotient system or completed cohomology comparison is asserted.

### lem-weil-pbc-graded-finiteness-cohomology

Let $A$ be a Noetherian ring [def-weil-pbc-noetherian-ring] and $B=\bigoplus_{k\ge0}B_k$ a commutative graded $A$-algebra (the $B_k$ are $A$-submodules with $B_kB_l\subseteq B_{k+l}$ and $1\in B_0$, the structure map $A\to B$ landing in $B_0$) which is a finite type $A$-algebra [def-weil-pbc-finite-type-algebra]. Let $f:X\to\operatorname{Spec}A$ be a proper morphism [def-weil-proper-morphism], and write $f^\sharp(a)\in\Gamma(X,\mathcal O_X)$ for the image of $a\in A$. Let $(\mathcal G_m)_{m\ge0}$ be quasi-coherent $\mathcal O_X$-modules [pqf-def-coherent], and for all $k,m\ge0$ and $b\in B_k$ let $\mu^{(m)}_b:\mathcal G_m\to\mathcal G_{m+k}$ be an $\mathcal O_X$-linear map [def-weil-sheaf-of-modules-category], such that: (i) $\mu^{(m)}_{b+b'}=\mu^{(m)}_b+\mu^{(m)}_{b'}$ for $b,b'\in B_k$; (ii) $\mu^{(m+l)}_b\circ\mu^{(m)}_{b'}=\mu^{(m)}_{bb'}$ for $b\in B_k$, $b'\in B_l$; (iii) for $a\in A$ with image $a\cdot1\in B_0$, $\mu^{(m)}_{a\cdot1}$ is multiplication by $f^\sharp(a)$ on $\mathcal G_m$; (iv) (finite type) $X$ is covered by open sets $U$ for each of which there are finitely many integers $d_1,\dots,d_r\ge0$ and sections $s_i\in\mathcal G_{d_i}(U)$ such that for every $m\ge0$, every open $V\subseteq U$ and every $t\in\mathcal G_m(V)$, each point of $V$ has an open neighbourhood $W\subseteq V$ on which $t|_W=\sum_{i:\,d_i\le m}\sum_jc_{ij}\,\mu^{(d_i)}_{b_{ij}}(s_i)|_W$ for finitely many $c_{ij}\in\mathcal O_X(W)$ and $b_{ij}\in B_{m-d_i}$. (These data are the same as a quasi-coherent graded module $\bigoplus_m\mathcal G_m$ of finite type over the graded $\mathcal O_X$-algebra $f^*\widetilde B$, $b\in B_k$ acting through its pulled-back global section.) Fix $p\ge0$ and put $M_m=H^p(X,\mathcal G_m)$ (sheaf cohomology [pqf-def-cohomology]). Then $M=\bigoplus_{m\ge0}M_m$ is a $B$-module under $\big(\sum_kb_k\big)\cdot(x_m)_{m\ge0}=\big(\sum_{k+m=n}H^p(X,\mu^{(m)}_{b_k})(x_m)\big)_{n\ge0}$ ($b_k\in B_k$, $x_m\in M_m$, almost all zero), and $M$ is a finitely generated $B$-module [def-weil-finitely-generated-module].


## Resumed landing repair for 9eba196d339 (2026-10-22)

The current return entry identifies approved delivery 9eba196d339, refused at landing because the side completion had not been promoted to the live queue. I continued the retained sandbox instead of restarting. The interrupted dry-run session had ended: no item delivery process remained active, and its saved readiness record records a successful dry run at ed4114c550f. The delivery tool supplies the rebase; I ran no git command in the shared repository.

I compared the retained parent to the current repository node field by field. Only proof, proof_deps and split_report differ; the target statement, source, definitions, blueprint ancestry, Lean record and historical metadata remain identical. The released repair note still requires this re-split. Neither child id exists in the current repository. All twenty existing-node statements archived in the duplicate review are still literal matches to the current statements. I reread the full current statements of all parent citations. All twelve citations.json entries are verbatim statement substrings, and their step/node pairs are exactly the citations of the five proof steps.

For step 1, the Noetherian theorem applies over Spec k, and the reduced-algebraic-normalization theorem explicitly gives the finite surjection and normal-open isomorphism. Reducedness makes each generic-point local ring a field, so the open contains every required generic point. For step 2, the integral definition, closed-immersion properness, normalization-properties clauses (a),(c), and normalization in the identity function-field extension give the precise component geometry; properness supplies the quasi-separatedness hypothesis of the last theorem. For step 3, the quotient lemma includes injectivity, coherence, support and the stalk/Euler formula under exactly the hypotheses established in step 1. I adjusted this step to define $B=\nu_*\mathcal O_{\widetilde X}$ explicitly: its cokernel is the parent's F, and its B is the same pushforward used in step 4. For step 4, the finite-morphism definition and finite-composition statement give the maps required by the family lemma, whose smooth proper connected sources are step 2. For step 5, Euler additivity applies to the coherent exact sequence on proper X and gives precisely the subtraction used. This is an adjusted split, not an unchanged re-push.

I reopened local Stacks 0BXR and 0C1R for normalization and its quotient, 0AYT for germs and zero-dimensional coherent cohomology, 089W for affine cohomology, 08AA for additivity, and 0BY7 for the genus convention. These agree with the retained source analysis and the two statement-only children. I read the retained search results and reused them because neither child statement nor the search question changed. I checked B--E again: the children have self-contained statements and no proof fields filled, all non-elementary assembly facts are statements of their citations, and no parent step exceeds 2000 characters. The whole assembly remains below 3000 characters. The disconnected two-line example still has p_a=-1; the smooth identity case has zero quotient; nodal and cuspidal cubics both contribute delta=1; the empty source family gives zero pushforward. No hypothesis of connectedness or nodality enters the parent. The final server dry run and push follow this actual notation repair and report update.


## Rebase for landing return d1f65224583 (2026-10-23)

I continued the retained delivery for the current 2026-10-22 16:29 UTC return. The required first dry run exited with a duplicate-review diagnostic, not a successful push: two current same-tag nodes were missing from the retained comparison list. I opened their full statements and added both pairwise distinctions under Not duplicates. The filtration Euler-difference statement assumes its filtration and integral-ideal quotients; it gives no finite-surjection defect construction or germs decomposition. The finite-ideal-twist comparison gives an affine edge isomorphism but does not supply the smooth-source cohomology or finite-family genus sum. Neither can replace the retained child statement.

The current shared item and retained item agree in statement, statement dependencies, source, Lean record and blueprint fields; their differences are the proof, proof dependencies and split report. Both child ids are still absent from the shared DAG. The released stage-1 re-split order still requires these two statement-only children and a short assembly. I reread every current parent proof-citation statement, and all twelve citations.json quotes are exact substrings. The Noetherian field base and generic-point normality in step 1, the proper integral components, perfect base and quasi-separatedness in step 2, the finite-surjection and generic-open hypotheses in step 3, and the finite component maps in step 4 remain available. I adjusted step 4 to identify its family map h with nu on every summand before identifying B. Step 5 still uses exactly Euler additivity on the coherent short exact sequence.

For this repair I reopened Temkin's primary PDF, Appendix B Lemma B.1 and its proof on printed page 57, and local Stacks Tags 0C1R, 0AYT, 0BXR, 089W, 08AA and 0BY7. Temkin's connectedness convention is not imposed on X: the assembly keeps pa=1-chi and therefore the 1-v term. I read the retained searches.jsonl results and the recorded verdicts: normalization and germ infrastructure do not give the quotient Euler formula; finite coproduct and pushforward infrastructure do not compute the family genus sum. Both new statements and search questions remain unchanged, so these searches are reused. The quotient lemma still covers the identity with F=0 and empty support, and the family lemma covers an empty family. Two disjoint projective lines give pa=-1; nodal and cuspidal cubics each have one-dimensional defect. These checks do not require connectedness or nodality of X. No Lean, compiler, git command, agent, repository write or launcher edit was used. The dry run is repeated after this repair, and its process must exit before the push.
