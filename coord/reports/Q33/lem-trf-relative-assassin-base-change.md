## Worker report

Files written (all under this item's sandbox):

- dag/nodes/sec-trace-formula/lem-trf-relative-assassin-base-change.json: existing statement, unchanged statement and statement dependencies; four assembly steps, 1663 characters.
- dag/nodes/sec-trace-formula/lem-trf-base-change-fibre-flat-qcoherent.json: statement, unsplit; no Mathlib match. Fibre square, flatness, locally Noetherian source fibre, quasi-coherent coefficient comparison.
- dag/nodes/sec-trace-formula/lem-trf-base-change-residual-fibre-cm.json: statement, unsplit; no Mathlib match. Residual-fibre identification, finite-generation hypothesis, Noetherian and local Cohen–Macaulay conclusions.
- dag/nodes/sec-trace-formula/lem-trf-cm-affine-associated-generic.json: statement, unsplit; no Mathlib match. Local associated points, minimal primes and component generic points for a Noetherian Cohen–Macaulay affine spectrum.
- citations.json: one verbatim statement quote for every citation of every assembly step.

Attachments: none. Searched WeilConjectures/ for relative assassin and the blueprint tag; there is no finished project declaration of this statement. The live Sheaf/AlgebraicGeometry/RelativeAssassinBaseChange.lean theorem at line 143 has `sorry`. Read its whole statement and nine-step docstring. No Lean file was written or compiled.

WANTED: none. All sources used are present locally.

The return concerns work size, not a false statement. No STATEMENT-DISPUTED issue was found. The sandbox initially had only dispatcher marker files, so the current live item was copied; its nine-step proof is the returned 5318-character proof. The initial dry-run session was lost across the provider interruption. After checking that no invocation was still active, the resumed initial dry run exited for the missing report. All original proof arguments are retained verbatim below and distributed explicitly among the three new work items. No target, imported statement, chapter route, unit route, or Lean record was changed.

Nothing mathematical is left unfinished at this split level: the new nodes deliberately have no proof steps, proof dependencies or proof origin. They are independently assignable statements for other workers, as ordered. No new node states relative assassin base change or either direction of its equivalence.

## Repair of the returned delivery

The one repair order requires at least two comparable statement-only work items and an assembly of at most 3000 characters. Added three, each with its own objects and hypotheses, source, definition citations, blueprint ancestry, five actual searches (LeanFinder twice, Loogle, LeanSearch, grep), and status unsplit. Their statement sizes are comparable, and their arguments are different: fibre/module functoriality, geometric residual-fibre calculation, and local commutative algebra.

Allocation of every old argument:

- Old steps 1–3 go to lem-trf-base-change-fibre-flat-qcoherent. It exposes the actual square and coefficient isomorphism, not merely their existence without compatibility. Its future proof is exactly the old square/pullback-composition argument, field-extension flatness/base-change argument, and finite-type-over-a-field Noetherianity and quasi-coherence argument.
- Old step 4 remains assembly step 2: apply the already existing flat-pullback equality and inspect the fibre images. No new node restates this consequence.
- Old steps 5–6 go to lem-trf-base-change-residual-fibre-cm. It exposes the fibre residue-field isomorphism, finite generation at any point, the actual tensor ring and its canonical point, and Noetherian/local Cohen–Macaulay properties. The explicit distinguished-point kernel is the affine residual-fibre description; it ensures the final genericity concerns the original z'.
- Old steps 7–8 and the minimal-prime/component-generic part of old step 9 go to lem-trf-cm-affine-associated-generic. Its future proof is the original stalk/localization argument in both directions followed by the prime/closed-set correspondence, now for an arbitrary Noetherian Cohen–Macaulay ring rather than just the residual tensor.
- The last fibrewise-definition argument in old step 9 remains assembly step 4. It converts the two associations into the two relative-assassin memberships.

This distributes the proof, rather than deleting it or placing the entire equivalence in one child. All old argument texts follow below for the future proof workers, because unsplit node statements must not contain proof sketches.

## Sources and searches

Read Divisors Tag 05DC, label lemma-base-change-relative-assassin, statement and both proof paragraphs in full (divisors.tex lines 1120–1169). Its first paragraph gives the first work item and the flat-pullback application; its second gives the residual tensor and the no-embedded-points calculation. Read Divisors Tag 05DB, lemma-bourbaki, statement and proof (lines 311–341), to check that its equality only needs the target locally Noetherian and allows an arbitrary quasi-coherent module. Read Algebra Tag 045M, lemma-tensor-fields-CM, statement and proof (algebra.tex lines 47267–47290): exactly one field extension must be finitely generated. Read Algebra Tags 0BUS, lemma-CM-ass-minimal-support (lines 25108–25132), 05BV, lemma-ass-minimal-prime-support (lines 15260–15276), and 05BZ, lemma-localize-ass (lines 15423–15449), and the no-embedded criterion at lemma-criterion-no-embedded-primes, to check the third work item against the source's final sentence. Tags were verified against stacks-project/tags/tags.

Whole-DAG searches used the source tags 05DC, 045M, 0BUS, 05BV, 05BZ, and concepts: relative assassin, residual fibre, flat fibre base change with Noetherianity and coefficients, and associated/generic points of Cohen–Macaulay rings. Opened the statements listed under Not duplicates, the flat-pullback and tensor-fields nodes, and all original proof dependencies. Blueprint searches via tools/blueprint_refs.py: 'Cohen Macaulay associated', 'relative assassin', 'residual fibre', '05DC', 'Cohen', 'associated', 'fibre', and '045M'. No imported blueprint node states a new work item. Broad 'associated' and 'fibre' results concern general module or geometric operations, not these combined statements. The nearest ancestor is lem-trf-local-term-locality, inherited through the existing relative-associated-specialization chain; read its statement and unit sk-i-curve-zero. The new blueprint.from.place records the inherited route and the precise subargument of 05DC; via prepends this item. The ancestor's updated contraction route is unchanged by this repair.

All fifteen new Mathlib searches are in searches.jsonl, with the exact query texts, real hit names and digests transferred to the corresponding new node. Each new statement had two differently worded semantic searches. None was unavailable. No earlier item's search was rerun or replaced. Read the returned hit statements; in particular the flatness stability hits and LocallyOfFiniteType.isLocallyNoetherian are only individual ingredients, and the module hits do not give the coefficient/fibre comparison plus the geometric hypotheses. Read Mathlib/AlgebraicGeometry/PullbackCarrier.lean lines 68–92: Triplet.tensor is a residue-field pushout; it gives no finite-generation or CM theorem. Read Mathlib/RingTheory/Ideal/AssociatedPrime/Localization.lean lines 117–146: Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes only gives the minimal-to-associated implication; it does not prove the Cohen–Macaulay converse or the stalk formulation. Read Mathlib/RingTheory/Spectrum/Prime/Topology.lean lines 1259–1288: zeroLocus_minimalPrimes identifies minimal primes with components but has no associated-point content. None of the three new statements is an exact hit or a one-line specialization.

## Not duplicates

lem-trf-base-change-fibre-flat-qcoherent vs lem-trf-flat-pullback-associated-points: the new statement supplies the cartesian fibre square, coefficient pullback comparison and flat/Noetherian/quasi-coherent hypotheses for a given arbitrary base change; 05DB assumes those hypotheses and concludes an associated-point equality. Neither statement implies the other directly; the assembly applies the existing equality after the new setup.

lem-trf-base-change-fibre-flat-qcoherent vs lem-trf-relative-assassin-base-change: the former is the geometric and coefficient setup, with no assertion about associated points or component genericity; it cannot alone prove the item.
lem-trf-base-change-residual-fibre-cm vs lem-trf-relative-assassin-base-change: the former identifies a residual fibre and establishes its local ring properties, without a sheaf, an associated point, or any relative-assassin equivalence.
lem-trf-base-change-residual-fibre-cm vs lem-trf-tensor-fields-cohen-macaulay: 045M treats two fields with an already supplied finite-generation hypothesis; the new geometric statement proves that hypothesis for kappa(z)/kappa(r) at a nonclosed point and identifies the scheme and distinguished point. The existing field theorem is an input, not a statement of the new node.
lem-trf-cm-affine-associated-generic vs lem-trf-relative-assassin-base-change: the former is a general affine-ring/stalk characterization with no morphism or coefficient base change; the item's flat-pullback equality and geometric identification are still required.
lem-trf-cm-affine-associated-generic vs lem-weil-pbc-cm-local-associated-prime-minimal: 0BUS gives only associated implies minimal within a Noetherian local ring; the new statement treats a global spectrum and includes descent of minimality from the localization, the converse, and component genericity.
lem-trf-cm-affine-associated-generic vs lem-weil-pbc-noetherian-minimal-prime-associated: 05BV gives only an annihilator witness for a minimal global prime; it neither gives the local stalk condition nor the CM converse or component identification.
lem-trf-cm-affine-associated-generic vs lem-weil-pbc-minimal-support-prime-associated: the existing statement produces associated primes minimal in the support of a finite module; it does not characterize associated points of a CM spectrum or prove the reverse implication.
lem-trf-cm-affine-associated-generic vs lem-weil-pbc-associated-prime-localization-depth-zero: 05BZ transports a global associated-prime witness to its localization, not the converse-to-minimality or component statement.
lem-trf-cm-affine-associated-generic vs lem-trf-fibre-module-localization: that node identifies two localizations of a fibre module and transports a localized annihilator witness, without any Cohen–Macaulay/minimal-prime characterization.
lem-trf-cm-affine-associated-generic vs lem-trf-fibre-associated-primes-module-ring: that node compares associated primes after restriction of scalars of a fibre module; it has neither the CM hypothesis nor the minimal-prime/component conclusion.
lem-trf-cm-affine-associated-generic vs def-sc-no-embedded-points: the existing definition assumes the associated-to-generic property as a predicate; it does not establish it under CM hypotheses and does not give the converse.
lem-trf-base-change-residual-fibre-cm vs lem-pur-cohen-macaulay-field-extension: the latter compares CM loci of schemes locally of finite type over a field. A finitely generated field extension of positive transcendence degree is not a finite-type algebra, so its spectrum is not covered by that statement. The new node uses the field-tensor theorem 045M, not a misapplication of that locus theorem.

## Review by Q33

I checked the return against the live file and retained its statement word for word, including arbitrary g, arbitrary quasi-coherent F, and the generic-component condition for the actual point z'. The copied item has no saved earlier sandbox rewrite to lose. I checked B1–B7 for each new node: all objects are introduced in its statement; notions cite actual defining nodes; CM and finite-generation meanings are explicitly written; all three nodes have empty proof/proof_deps and no proof sketch in their statements; sources name the right local Stacks labels and tags; TeX is encoded once. Each new statement is strictly smaller than the item, and all three are separately usable without assuming another's theorem.

Assembly step 1 uses only lem-trf-base-change-fibre-flat-qcoherent. I read its exact statement: it supplies h flat, Y locally Noetherian, G quasi-coherent, and F' restricted to the fibre is h^*G, with the correct projections. The source's F is not assumed finite or coherent. Y is locally of finite type over the field k even if S is non-Noetherian; flatness comes from k'/k and not from f or g. The coefficient functor is the same tensor pullback as in the original statement.

Assembly step 2 uses only lem-trf-flat-pullback-associated-points. I read its equality, not an argument inside its proof: it assumes a flat morphism with locally Noetherian target and arbitrary quasi-coherent coefficients, exactly as supplied in step 1. Its j_y-images lie over y by the definition of fibre, so inspecting membership in that union is elementary once the equality is supplied. The point in Y is the canonical fibre point, not a new arbitrary point with the same image.

Assembly step 3 uses only lem-trf-base-change-residual-fibre-cm. Its statement supplies both the canonical fibre identification and the distinguished-point kernel, as well as the Noetherian/local CM claims. The finite-type chart at z can be chosen without z closed. The field extension k'/k can be arbitrary: 045M only needs kappa(z)/k finitely generated. No separability or geometric reducedness is claimed. The added explicit kernel description follows the two structural residue-field maps under the affine tensor-fibre identification, so it cannot switch to a different point of Spec T.

Assembly step 4 uses lem-trf-cm-affine-associated-generic and def-trf-relative-assassin. I read both statements: the ring node equates stalk association, minimality, and component genericity for exactly the Noetherian local-CM ring T from step 3. The definition's final sentence is the equivalence with association of the canonical point in X_{f(x)}, on both the original and base-changed scheme. It therefore converts exactly the two associations already in step 2. No identification from a cited proof is used. citations.json quotes each of these statements verbatim; proof_deps is the exact union of uses. The original generic tools now occur inside the unsplit work items, not as uncited assertions of the assembly.

For the new ring node I checked the difficult local/global direction rather than silently calling it standard: association in the stalk gives a minimal prime of T_q by 0BUS, and the order-preserving prime correspondence excludes any strictly smaller global prime; conversely a minimal prime of the Noetherian ring has a global witness by 05BV and a localized witness by 05BZ. V(q) reverses inclusions, yielding component genericity. These are precisely old steps 7–9, now assigned to a future worker and retained below. The ring node is not a one-line consequence of a definition.

Small cases checked: empty X or a fibre with no z has no pointwise obligation; F=0 gives no associated stalk on either side. With k'=k the residual fibre is Spec kappa(z) and its unique point satisfies the condition. For z the generic point of A^1_k, kappa(z)=k(t) is finitely generated as a field but not finite as a k-algebra: the residue-finiteness statement is formulated correctly. A purely inseparable example K tensor_k K = K[epsilon]/(epsilon^p) is allowed: nilpotents do not obstruct the CM result and its sole prime is both associated and generic. For the general ring node T=0 is vacuous; for a field its sole prime has witness 1; for k[x] a nonminimal closed prime is not associated in its local ring. For k(t) tensor_k k(u), the diagonal prime is nonminimal and not associated, so the generic-component restriction cannot be dropped. No step uses a closed-point, perfection, flatness of g, or Noetherianity of S hypothesis.

The only corrected feature is the granularity required by the return: nine original steps became three substantive statement-only work items and four assembly steps, with all original arguments preserved. I have not marked the maintainer's earlier review as a fresh review or changed any maintainer-owned field. No SGA source is used. The initial server review_split returned PASS. The first full dry run requested the 05DB duplicate comparison between the new fibre-setup node and the existing flat-pullback associated-point formula; I added the precise distinction under Not duplicates after rereading both statements. Final deliver.py preflight is rerun after this report and all its diagnostics are repaired before push.

## Repair L: rebase onto the current DAG (2026-10-22)

The returned head was aef90fc3cdf. L approved its mathematics but refused its landing because completion in the side project's DAG had not been promoted to the live DAG. This is a separate return from the earlier work-size order. I retained the delivered sandbox nodes, original-proof.json, citations.json, report and all fifteen logged searches. The required first dry run now exited successfully at dff0b3a1a22; it rebuilt the retained overlay on the current origin/sheaf-dag rather than resending the returned commit. The delivery tool fetches the live branch and overlays only stage-1-owned fields, preserving current maintainer records.

I compared the retained item with the current repository item field by field. Only proof, proof_deps and split_report differed before this repair; statement, stmt_deps, source, blueprint ancestry, Lean record and maintainer-owned fields agreed. In particular, original-proof.json equals the current nine-step proof exactly. All three new ids are still absent from the current repository. Thus none needs replacement by a newly landed equivalent, and the original allocation of all nine arguments still applies. I updated split_report to record the current-DAG audit; the accepted mathematical split and search records are retained.

I reread every current statement used by the assembly, including both existing citations, rather than presuming that the previous review still applies. Step 1's retained fibre-setup statement supplies precisely the flat h, locally Noetherian Y, quasi-coherent G and coefficient isomorphism. The current lem-trf-flat-pullback-associated-points used in step 2 still states the full union equality for any quasi-coherent module with locally Noetherian target; it imposes neither finite generation of the module nor local Noetherianity of the source. Step 3's retained residual-fibre statement still supplies the canonical point, the same ordered tensor product, Noetherianity and all local CM equalities. Step 4's retained affine-CM statement gives association iff component genericity, and the current def-trf-relative-assassin explicitly identifies relative membership with association at the canonical fibre point. Every entry of citations.json is still a verbatim substring of the current cited statement, and there is exactly one entry for each (step,node) pair. No citation needed changing.

I also reopened the original proof inputs in the current DAG: fibre-of-base-change, module-pullback composition, field-extension flatness, flat and locally finite type base change, locally-Noetherian finite type schemes, quasi-coherent module pullback, fibre-ring residue fields, affine fibre products, finitely generated residue extensions, tensor-fields Cohen–Macaulay, affine stalk localization, CM local associated primes, localization prime correspondence, Noetherian minimal-prime association and associated-prime localization. Their statements still supply the arguments retained below. In particular the current tensor-fields statement only requires one finitely generated field extension, and the local CM input accepts the equality of depth and dimension supplied by the new ring statement. Nothing assumes a closed z or a Noetherian S. I reread local Stacks 05DC, 05DB, 045M, 0BUS, 05BV and 05BZ, including the proofs, and rechecked the canonical tensor point against the current Lean statement. The project theorem still ends in sorry; no completed WeilConjectures declaration was found. No attachment is claimed.

The B–E audit therefore needs no change to the mathematical route: the new nodes remain self-contained statement-only independent subarguments, and no source hypothesis has changed. The empty/zero, identity-extension, generic-point and inseparable test cases recorded above remain valid. All assembly steps are below 2000 characters, their combined text remains below 3000 characters, and no argument of the old proof was discarded. The final dry run follows this report update and must exit before the push. No Lean was written or compiled, no repository file or launcher file was changed, and no search was invented or repeated.

Current existing assembly statements reread (SHA-256 of the statement text, for comparison by a future repair):

- lem-trf-flat-pullback-associated-points: f13793f5169f91a366b8420b62b4306a5be9931db4dba63e2e376cf2a686e62d
- def-trf-relative-assassin: e98d64d90703a2803c1f728250fecbb399331785d3ea196bc60a2e6ebd69d064

## Repair L: current returned head 95d6da53354 (2026-10-23)

The current return in coord/returns/Q33.md is dated 2026-10-22 16:22 UTC and names head 95d6da53354. It repeats the side-completion promotion refusal. The earlier rebase audit above concerns an older return; it is retained as history, not presented as the audit of this head. I continued the retained delivered payload, including all three nodes, citations, original-proof.json and actual search log. The mandatory first dry run rebuilt it against the fetched current DAG and exited OK at bec7f82a334. This repair updates split_report and this report; the final push is a new delivery rebuilt by deliver.py, not an unchanged resend of the refused commit. Promoting the side completion remains L's landing operation, as the return explicitly says.

The field-by-field comparison with the current shared DAG again finds only proof, proof_deps and split_report different. All maintainer-owned fields agree. The current nine-step proof equals original-proof.json exactly, so the allocation recorded above still preserves every old argument. All three new ids remain absent from the shared DAG. I reread the current statements of all five assembly citations: the fibre setup supplies exactly the flatness, locally Noetherian target, quasi-coherent coefficients and coefficient isomorphism used in step 1; the current flat-pullback statement supplies the full union equality used in step 2; the residual-fibre statement supplies the same tensor ring, distinguished point and local CM properties used in step 3; and the affine-CM equivalence and relative-assassin definition supply exactly the two substitutions in step 4. The two existing assembly-statement hashes still equal the values recorded in the preceding audit. Each citations.json quote is a verbatim substring of its current statement. No citation or mathematical step needs replacement.

For this audit I reopened Stacks divisors.tex, lemma-base-change-relative-assassin (05DC), and lemma-bourbaki (05DB), and algebra.tex, lemma-tensor-fields-CM (045M), lemma-CM-ass-minimal-support (0BUS), lemma-ass-minimal-prime-support (05BV), and lemma-localize-ass (05BZ). I reread every current node cited by the preserved original proof as well. The hypotheses still fit: local finite type supplies the Noetherian fibre and finitely generated residue-field extension at arbitrary z; arbitrary g is allowed; the module need not be finite; only one field extension needs finite generation. The stalk/localization statements still supply the associated/minimal-prime argument. I checked current same-tag neighbours lem-trf-generic-cm-locus-field, lem-trf-fibre-component-relative-associated and lem-sc-hilbert-embedded-points-affine-removal: their statements concern an open CM locus, one direction for fibre components, and removal of embedded primes, respectively, and none states any of these three new work items. The earlier Not duplicates distinctions remain applicable.

I read all fifteen retained searches and their actual hit lists and digests. The statements have not changed, so none was repeated or invented. The current project-source search still finds no WeilConjectures declaration of the item. The recorded Sheaf theorem at RelativeAssassinBaseChange.lean:143 still ends in sorry. The B–E review above remains valid: each child is self-contained and statement-only; the assembly uses their statements, not their proofs; all non-elementary assertions are cited; neither implication of the item was moved into a child. Empty fibres and the zero module are vacuous, the identity field extension gives a one-point residual spectrum, and the inseparable nilpotent example remains covered without a reducedness hypothesis. Each assembly step is shorter than 2000 characters and the assembly remains 1663 characters. The final dry run is run after these edits and must exit successfully before pushing. No Lean, repository or launcher file was written and no compiler was invoked.

## Preserved original proof and future-worker arguments

The following is the complete original nine-step proof, copied before the repair. The allocation above tells each future proof worker exactly which argument belongs to its work item. This material is intentionally in the report rather than in unsplit node statements.

### Original step 1

Put $k=\kappa(r)$, $k'=\kappa(r')$, $Y=X_r$ and $Y'=X'_{r'}$. By [lem-weil-pbc-fibre-of-base-change] there is a cartesian square identifying $h:Y'\to Y$ with the base change of $\operatorname{Spec}k'\to\operatorname{Spec}k$. If $i:Y\to X$ and $i':Y'\to X'$ are the fibre projections, then $i\circ h=g'\circ i'$. Pullback composition in [def-pc-module-pullback] therefore gives $\mathcal F'_{r'}=(i')^*(g')^*\mathcal F\cong h^*i^*\mathcal F=h^*\mathcal F_r$. This comparison identifies the same pullback module, rather than changing the coefficient sheaf.

Uses: lem-weil-pbc-fibre-of-base-change, def-pc-module-pullback.

### Original step 2

The map $\operatorname{Spec}k'\to\operatorname{Spec}k$ is flat by [lem-pc-field-extension-flat]. Its base change $h$ is flat by [lem-weil-pbc-flat-morphism-base-change]. No flatness of the original morphism $f$ or of $g$ is required.

Uses: lem-pc-field-extension-flat, lem-weil-pbc-flat-morphism-base-change.

### Original step 3

The structure map $Y\to\operatorname{Spec}k$ is locally of finite type by [lem-weil-pbc-lft-base-change]. A field has only the ideals $(0)$ and $(1)$, so its spectrum is locally Noetherian. Apply [pqf-lem-locnoeth-lft] to conclude that $Y$ is locally Noetherian. The sheaf $\mathcal F_r=i^*\mathcal F$ is quasi-coherent by [lem-weil-pbc-module-pullback-quasi-coherent]. Thus the flat pullback formula can be applied with base $Y$ and arbitrary quasi-coherent coefficients $\mathcal F_r$; no finite generation of $\mathcal F$ has been assumed.

Uses: lem-weil-pbc-lft-base-change, pqf-lem-locnoeth-lft, lem-weil-pbc-module-pullback-quasi-coherent.

### Original step 4

Apply [lem-trf-flat-pullback-associated-points] to $h:Y'\to Y$ and $\mathcal G=\mathcal F_r$, using steps 1–3. It gives
$$\operatorname{Ass}_{Y'}(\mathcal F'_{r'})=\bigcup_{y\in\operatorname{Ass}_Y(\mathcal F_r)}j_y\operatorname{Ass}_{Y'_y}(\mathcal O_{Y'_y}).$$
The point of $Y$ underlying $z'\in Y'$ is the canonical point $z\in X_r$. Since the images of the fibre maps $j_y$ lie over their respective $y$, this equality says precisely that $z'$ is associated to $\mathcal F'_{r'}$ if and only if $z$ is associated to $\mathcal F_r$ and the corresponding point of $Y'_z$ is associated to $\mathcal O_{Y'_z}$.

Uses: lem-trf-flat-pullback-associated-points.

### Original step 5

The residue field at the canonical point $z\in Y=X_r$ is $\kappa(z)$: on affine charts, clause (2) of [lem-weil-pbc-fibre-ring-primes-residue-fields] identifies the residue field in the fibre ring with that of the original point. Base-changing the square of step 1 along $\operatorname{Spec}\kappa(z)\to Y$, the fibre $Y'_z$ is consequently $\operatorname{Spec}k'\times_{\operatorname{Spec}k}\operatorname{Spec}\kappa(z)$. By [lem-weil-pbc-fibre-product-affine-spectra] it is $\operatorname{Spec}T$ for $T=k'\otimes_k\kappa(z)$. To check the finiteness needed below, choose an affine neighbourhood $V=\operatorname{Spec}R$ of $r$ and a finite-type affine chart $U=\operatorname{Spec}B$ of $f^{-1}(V)$ containing $z$, as in [def-weil-finite-type-morphism]. Apply [lem-weil-pbc-finite-type-residue-field-extension-finitely-generated] to $R\to B$ and the primes of $r,z$. It gives that $\kappa(z)/k$ is finitely generated as a field, even when $z$ is not closed.

Uses: lem-weil-pbc-fibre-ring-primes-residue-fields, lem-weil-pbc-fibre-product-affine-spectra, def-weil-finite-type-morphism, lem-weil-pbc-finite-type-residue-field-extension-finitely-generated.

### Original step 6

Apply [lem-trf-tensor-fields-cohen-macaulay] to $k'/k$ and $\kappa(z)/k$, the latter finitely generated by step 5. Thus $T$ is Noetherian and every $T_{\mathfrak q}$ is Noetherian local Cohen–Macaulay. The other extension $k'/k$ may be completely arbitrary. We now determine the associated points of $\operatorname{Spec}T$ directly in these local rings.

Uses: lem-trf-tensor-fields-cohen-macaulay.

### Original step 7

Let $\mathfrak q\in\operatorname{Spec}T$ be an associated point of its structure sheaf. By [lem-weil-pbc-affine-open-stalk-localization](c) its local ring is $T_{\mathfrak q}$; association means its maximal ideal $\mathfrak qT_{\mathfrak q}$ is an element-annihilator associated prime of that ring. Step 6 and [lem-weil-pbc-cm-local-associated-prime-minimal] imply that $\mathfrak qT_{\mathfrak q}$ is a minimal prime of $T_{\mathfrak q}$. The inclusion-preserving prime correspondence [lem-weil-pbc-primes-of-localization](1) now implies that $\mathfrak q$ is minimal in $T$: a strictly smaller prime would extend to a strictly smaller prime below $\mathfrak qT_{\mathfrak q}$, a contradiction.

Uses: lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-cm-local-associated-prime-minimal, lem-weil-pbc-primes-of-localization.

### Original step 8

Conversely, if $\mathfrak q$ is a minimal prime of $T$, the Noetherian hypothesis from step 6 lets us apply [lem-weil-pbc-noetherian-minimal-prime-associated]: $\mathfrak q$ is an element-annihilator associated prime of $T$. By [lem-weil-pbc-associated-prime-localization-depth-zero], its extension $\mathfrak qT_{\mathfrak q}$ is associated to $T_{\mathfrak q}$. The stalk identification [lem-weil-pbc-affine-open-stalk-localization](c) therefore says that $\mathfrak q$ is an associated point of the structure sheaf of $\operatorname{Spec}T$. Together with step 7 this characterizes those associated points as exactly the minimal primes.

Uses: lem-weil-pbc-noetherian-minimal-prime-associated, lem-weil-pbc-associated-prime-localization-depth-zero, lem-weil-pbc-affine-open-stalk-localization.

### Original step 9

The prime-ideal/irreducible-closed-set correspondence in [def-weil-pbc-krull-dimension-ring] reverses inclusions: the closure of $\{\mathfrak q\}$ is $V(\mathfrak q)$, and it is a maximal irreducible closed subset exactly when $\mathfrak q$ is minimal. By [def-sc-generic-point] these are exactly the generic points of irreducible components of $\operatorname{Spec}T$. Hence steps 7–8 replace the last condition in step 4 by the generic-component condition of the statement. Finally the fibrewise definition [def-trf-relative-assassin] identifies association of $z$ to $\mathcal F_r$, respectively of $z'$ to $\mathcal F'_{r'}$, with membership in the two relative assassins. This proves both implications of the desired equivalence.

Uses: def-weil-pbc-krull-dimension-ring, def-sc-generic-point, def-trf-relative-assassin.
