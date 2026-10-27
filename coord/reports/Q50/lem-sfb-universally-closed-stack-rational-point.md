# Q50: lem-sfb-universally-closed-stack-rational-point

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-universally-closed-stack-rational-point.json: item, split; statement unchanged, six proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-qc-diagonal-stack-spectral.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-reduced-singleton-qc-diagonal-gerbe.json: statement, unsplit; no Mathlib match.
- citations.json: one literal statement quotation for every step/node pair (12 entries).
- report.md: this report. Search logs and scratch scripts remain sandbox-only.

## Attachments

None. Searches under lean/WeilConjectures for the exact blueprint tag and the stack/gerbe/rational-point concepts found no declaration stating this item. GeometricallyConnected.lean concerns schemes and assumes a rational point; it does not establish existence for stacks. Existing lem-pc-rational-points-dense is reused: DensePoints.lean, Hom.nonempty_fieldPoints at lines 215–218, has the required nonempty smooth-scheme conclusion and an existing closed audit.

## WANTED

None. All source inputs used are available in literature/stacks-project. The proof is agent-written, assembled from these sources, not claimed to be verbatim from an Alper paper.

## What needed repair

The imported item was statement-only. It deliberately imposes neither local finite type over K nor local Noetherianity. Several tempting existing nodes (finite-type-stack-closed-specialization, noetherian-singleton-gerbe, singleton-stack-finite-field-homeomorphism and singleton-stack-flat-lfp-field-cover) require one of those missing hypotheses. I did not apply them. Instead the split exposes the general spectrality and reduced singleton gerbe results which work without either hypothesis.

The live and sandbox item were identical at resumption. There was no report or split to dry-run first. Existing search records were read and reused; interrupted missing searches were completed and their actual results recorded. The first singleton Loogle query was rejected for an unknown identifier, which is recorded explicitly, and a valid typed query was run as a follow-up. Neither the scheme hits nor the topological SpectralSpace hits specialize to a theorem about algebraic stacks. The Mathlib Prespectral.lean hit is merely the abstract compact-open basis definition, not a stack spectrality theorem. The scheme UniversallyClosed and Proper hits are restricted to schemes. No new node is a Mathlib leaf.

The nearest blueprint ancestor tool returns null for this item, as already recorded by the inherited chain. I preserve that value and extend the exact inherited proof place and via chain for each new node. I read the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof. Its paragraph (3) is the direct-image/compactification argument; this generic rational-object input sits far below that paragraph in the existing alteration/moduli chain. It does not replace a step of the unit route. Searches of the full DAG and blueprint for gerbe, singleton, spectrality and quasi-compact diagonal found no blueprint statement duplicating either new node. No unit realization is changed: this is not its key node.

## Source and argument for the new inputs

For lem-sfb-qc-diagonal-stack-spectral I read stacks-morphisms.tex Tag 0DQN, lemma-spectral-qc-diagonal-qc, including its proof, and Tag 0DQQ, lemma-sober-qs. The precise source assumes a quasi-compact algebraic stack with quasi-compact diagonal, exactly the new node's chart hypotheses. It gives a spectral point space, not just quasi-compactness. Spectrality includes sobriety, hence the Kolmogorov property used in step 1.

For lem-sfb-reduced-singleton-qc-diagonal-gerbe I read Tag 06RC, proposition-open-stratum, and its proof; Tag 0DQL, lemma-gerbe-diagonal-quasi-compact; Tags 0DN8 and 06R9; spaces-descent.tex Tag 0GB3, lemma-reduced-local-smooth; decent-spaces.tex Tag 03JX, lemma-bounded-fibres, and Tag 047Z, lemma-when-field. Here is the argument reserved for its later split, not put into the new statement: inertia is a base change of the quasi-compact diagonal. Tag 06RC produces a dense open gerbe in the reduced stack, which is the whole stack because its nonempty point space is a singleton. Say the gerbe is over Q. Tag 06R9 gives |Q| a singleton; 0DQL makes Q quasi-separated. A reduced smooth atlas of the stack maps smoothly and surjectively to Q by 0DN8, so 0GB3 gives reducedness of Q on etale charts. Quasi-separated Q is decent by 03JX and the decency condition; 047Z gives Q = Spec L. The original k-structure gives the field inclusion k -> L. Neither 06RC nor this argument needs local Noetherianity or local finite type over k. This is a structural gerbe statement for arbitrary k and arbitrary extensions L/k, not the item's rational-object conclusion.

## Review by Q50

I checked B through E of delivery-errors.md against the JSON and the source text. Both new nodes introduce their own field, stack, point topology and chart assumptions, cite the definitions their statements use, and have empty proofs and proof dependency lists. The gerbe condition is written in the statement using fppf-local objects and isomorphisms rather than being defined by a source tag. They are neither elementary observations nor clauses of the item: spectrality is an independent topological theorem, and the singleton lemma identifies a general reduced stack as a gerbe over an unspecified possibly transcendental extension. The item still has to choose a closed substack, use universal closedness to control that extension, and produce its rational object.

For step 1 I opened the new spectrality statement and the existing compact Kolmogorov closed-point statement: they supply exactly quasi-compactness, Kolmogorov separation, and a closed singleton. I opened smooth-presentation-closed-subsets: its statement explicitly constructs the unique reduced closed substack for any closed subset. Nonemptiness is the item's hypothesis; the empty case is not being asserted.

For step 2 I checked def-sfb-stack-qcqs-morphism and stack-closed-immersion-calculus. Fullness of a closed substack identifies its isomorphism spaces with those in the ambient stack, so its relative diagonal is the displayed base change of the ambient diagonal. On quasi-compact scheme tests this is directly the defining quasi-compactness condition; no finiteness theorem is smuggled in. The closed-immersion node explicitly supplies arbitrary stack base change and the closed embedding on point spaces. Thus a closed subset in C_T is closed in Z_T, and the hypothesis on Z_T -> T applies. This is a short elementary passage through the definitions and the cited closed-embedding statement, not an unsupported permanence claim.

For step 3 I checked every hypothesis of the new singleton lemma: reducedness and singleton point space came from step 1, and quasi-compact diagonal from step 2. I read the existing gerbe-smooth-universal-homeomorphism statement: it supplies smoothness, surjectivity, and the homeomorphism after every algebraic-stack base change. The ordinary noetherian singleton lemma does not supply this application and is not cited.

For step 4 I checked the gerbe homeomorphism is applied over Spec L, along Y_T = Spec L x_K T. Its source is precisely C x_K T, by associativity of the 2-fibre product; it is not a different field fibre. A closed D in Y_T pulls back to a closed subset with exactly the same image in T, so step 2 proves that image is closed. This checks universal closedness for every K-scheme T. I opened pqf-lem-integral-univclosed: it states both directions of integral iff affine and universally closed for schemes. Both its objects are now field spectra (schemes); their structural map is affine. Thus it really supplies integrality of L/K, without a finite-type assumption.

For step 5 I wrote the elementary argument that every integral element of an extension of an algebraically closed field lies in the base field. It uses monicity, successive extraction of roots, and the absence of zero divisors in a field. I did not claim that an arbitrary extension of an algebraically closed field is trivial. Identifying L with K preserves the given K-structure.

For step 6 I checked the exact smooth-over-the-base atlas convention in def-sfb-algebraic-moduli-stack. The smooth gerbe over K supplies a nonempty smooth K-scheme atlas. I opened lem-pc-rational-points-dense and its source Lean: the statement gives a rational point of every nonempty smooth scheme over a separably closed field. K is separably closed because it is algebraically closed. The resulting point is composed with the atlas and closed-substack inclusion to obtain an object over the same K; no extension of K is used at the end.

I checked small cases: the spectrality theorem allows an empty stack but is used only for the nonempty item. Spec K and classifying gerbes of flat finite-presentation groups satisfy the singleton structural statement; a nonneutral gerbe over a nonclosed field is allowed because the new lemma does not assert a section. Spec k(t) over k is also covered by the new structural lemma with L = k(t), and illustrates why step 4's universal closedness is essential before concluding L = K. A reduced singleton need not initially be assumed locally Noetherian; I avoided all existing inputs that require this. Nonreduced singleton thickenings are excluded from the new structural statement and are handled in the item only by passing to the reduced closed substack.

The citation file uses literal quotations copied from the statements, not from their proofs. Each of the six steps is below 700 characters; none hides a long inline lemma. I verified proof_deps is exactly the union of the six uses lists and no new node depends on the item as a logical dependency. Blueprint.from and created.item record provenance only. No Lean was written, no compiler or Lake/build tool was run, and no repository or launcher file was edited.

## Tool uses

pqf-lem-integral-univclosed is the scheme affineness/universal-closedness criterion; lem-sc-quasi-compact-kolmogorov-closed-point is general topology; lem-pc-rational-points-dense is smooth-scheme point existence. They are generic tools below the inherited moduli argument, declared in split_report.tool_uses. No node in the item's unit states these generic facts.

## Not duplicates

lem-sfb-qc-diagonal-stack-spectral vs lem-sfb-finite-type-stack-closed-specialization: the existing node requires finite type over a field and gives Noetherianity/closed specializations; the new node assumes only quasi-compactness and quasi-compact diagonal and gives spectrality without finite type.
lem-sfb-qc-diagonal-stack-spectral vs lem-sfb-adequate-integral-comparison-finite: the existing node concerns finite integral comparison for adequate moduli spaces of finite-type stacks, not spectrality for arbitrary quasi-compact stacks.
lem-sfb-qc-diagonal-stack-spectral vs lem-sfb-universally-closed-stack-rational-point: the item asserts a rational object under universal closedness and algebraic closedness; the new node is a general topological input with neither assumption nor rational-object conclusion.
lem-sfb-qc-diagonal-stack-spectral vs lem-sfb-adequate-geometric-fibres-submersion: the existing node asserts adequate-moduli universal submersiveness and geometric-fibre closure equivalence, not general stack spectrality.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-universally-closed-stack-rational-point: the new node allows any base field and arbitrary L/k and asserts a gerbe structure; the item forces L = K and a rational object using universal closedness and algebraic closedness.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-space-reduced-closed-support: the existing node constructs a reduced closed algebraic subspace from a closed support; it does not give a gerbe quotient of a singleton stack.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-space-smooth-reduced-locality: the existing node is reducedness ascent/descent for smooth algebraic-space maps, a supporting ingredient of the new structural theorem, not its conclusion.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-adequate-geometric-fibres-submersion: the existing node is an adequate-moduli space property theorem; the new node is independent of adequate moduli and identifies reduced singleton stacks over a field.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-smooth-presentation-closed-subsets: the existing node constructs reduced closed substacks and describes point-space quotient topology; it asserts no gerbe-over-a-field structure.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-noetherian-singleton-gerbe: the existing node assumes local Noetherianity and returns a reduced locally Noetherian singleton algebraic space; the new node removes that hypothesis using quasi-compact diagonal and concludes a field spectrum.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-singleton-stack-finite-field-homeomorphism: the existing node requires local finite type over k and concludes a finite field extension and universal homeomorphism; the new node allows arbitrary extensions with no local finite-type assumption and asserts a gerbe structure.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-singleton-stack-flat-lfp-field-cover: the existing node requires local Noetherianity and gives a field-valued cover pointing into the stack; the new node has no Noetherian hypothesis and gives a gerbe morphism out to a field spectrum.

lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-qs-space-rational-point-topology: the existing node gives injectivity and closedness of already given rational points on a quasi-separated algebraic space; it constructs no quotient gerbe or field for a singleton algebraic stack.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-quasiseparated-space-atlas-dimension: the existing node compares dimensions of a quasi-separated algebraic space and its etale atlas; it constructs no gerbe quotient of a singleton stack.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-quasiseparated-space-dense-scheme-open: the existing node supplies a dense scheme open in a quasi-separated algebraic space; it does not construct a gerbe quotient of a reduced singleton algebraic stack.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-quasiseparated-space-etale-specializations: the existing node lifts specializations through etale charts of a quasi-separated algebraic space; it asserts no gerbe or field quotient.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-quasiseparated-space-sober: the existing node gives sobriety of a quasi-separated algebraic space, not a gerbe structure on a reduced singleton algebraic stack.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-space-etale-atlas-topological-dimension: the existing node compares dimensions after scheme base change using etale atlases; it does not identify singleton algebraic stacks as gerbes over fields.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-space-etale-maximum-degree: the existing node finds the maximum-degree finite-etale locus of an atlas of a separated finite-type algebraic space; the new node concerns gerbe structure without finite type.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-space-qc-etale-fibre-bound: the existing node bounds geometric fibres of a quasi-compact etale scheme chart of a quasi-separated algebraic space; it does not construct a gerbe quotient.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-space-topological-dimension-local-rings: the existing node expresses dimension of a quasi-separated algebraic space in terms of local-ring dimensions; it asserts no singleton-stack gerbe quotient.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-space-relative-dimension-base-change: the existing node proves base change and descent for fibre-dimension bounds on locally finite-type algebraic-space morphisms, not a singleton-stack gerbe structure.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-space-eventually-fibre-dimension: the existing node descends fibre-dimension bounds along inverse limits for finitely presented algebraic spaces, not a gerbe-over-field construction.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-space-fibre-dimension-base-change: the existing node preserves fibre-dimension bounds under base change of locally finite-type algebraic spaces, not gerbe structure for stacks.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-qcqs-space-integral-scheme-cover: the existing node gives a surjective integral scheme cover of a qcqs algebraic space, not a gerbe morphism from a singleton stack to a field.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-space-weak-chow: the existing node gives a proper scheme cover and projective immersion for a separated finite-type algebraic space, not gerbe structure without finite type.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-space-quasifinite-source-dimension-bound: the existing node bounds dimension of locally quasi-finite scheme sources over a quasi-separated algebraic space; it constructs no gerbe quotient.

lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-qs-space-field-monomorphism: the existing node gives an incoming field monomorphism representing each point of a quasi-separated algebraic space; it does not produce a gerbe morphism out of an arbitrary reduced singleton algebraic stack.
lem-sfb-reduced-singleton-qc-diagonal-gerbe vs lem-sfb-relative-qs-affine-chart-point-fibres: the existing node proves finite point fibres of affine etale charts and their relations over relatively quasi-separated algebraic spaces; it does not give a field quotient or gerbe structure for stacks.

## Unfinished work

The two new nodes are intentionally unsplit for later workers. The assigned item's argument and citation audit are complete; server checks and final delivery are recorded by the delivery command.
