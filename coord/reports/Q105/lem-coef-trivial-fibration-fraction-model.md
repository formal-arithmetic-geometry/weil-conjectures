# Q105: lem-coef-trivial-fibration-fraction-model

## Files written

- dag/nodes/sec-six-functors/lem-coef-trivial-fibration-fraction-model.json: statement split into seven proof steps; no Mathlib match for the whole statement.
- dag/nodes/sec-six-functors/lem-coef-edge-inverting-anodyne-extension.json: new statement-only input, unsplit; no Mathlib match. Strict parameter-boundary lifting for edge-inverting functor categories.
- dag/nodes/sec-six-functors/lem-coef-horn-completion-point-colimit.json: new statement-only input, unsplit; no Mathlib match. Functorial horn completion and its weak homotopy comparison. The identifier is retained from the earlier sandbox, but the unused constant-point colimit clause has been removed and the title now describes its actual statement.
- dag/nodes/sec-six-functors/lem-coef-terminal-local-kan-corepresentability.json: new statement-only input, unsplit; no Mathlib match. The general local-comma criterion for an arbitrary putative right calculus at one object.
- citations.json: an exact excerpt of the cited statement for each dependency of each numbered step. Full statements are quoted where the hypotheses and conclusion are used together.

## Attachments

None. I searched the project declarations in /home/ubuntu/weil-src-slopmaster2/WeilConjectures by the item id, the blueprint docstring tag, trivial-fibration/fraction/span terminology, and the new input notions. I also searched the corresponding upstream-master reference directories. No project declaration states the whole item or a new input. Both imported audit states are none. Mathlib's ordinary fraction API is not an enhanced localization attachment.

## Literature needed

WANTED: Denis-Charles Cisinski, Higher Categories and Homotopical Algebra, https://cisinski.app.uni-regensburg.de/CatLR.pdf, Proposition 7.1.3; Definitions 7.2.2, 7.2.4, 7.2.6; Theorem 7.2.8 and Remark 7.2.10; Lemma 7.2.15, Theorem 7.2.16, Corollary 7.2.18 and Definition 7.2.20, for the item and the local-comma criterion.

WANTED: the same source, Corollary 3.5.13, for lem-coef-edge-inverting-anodyne-extension.

WANTED: the same source, Proposition 2.1.9, construction 2.4.36 and Section 3.1, for lem-coef-horn-completion-point-colimit.

I read these places in the online PDF; no copy was downloaded to the shared repository. Remark 7.2.10 explicitly identifies the constant-point comma colimit with its weak homotopy type by Proposition 6.1.14, and gives the component formula in (7.2.10.4). This is included in the general criterion's statement rather than borrowed from an uncited source proof. No Stacks tag states these enhanced categorical results. No SGA source is used. The proof is recorded as agent-written with the current blueprint exceptional-adjoint proof paragraph 2 as its route ancestor, because the reference is not locally archived.

## Corrections and route

The item's mathematical hypotheses and conclusions are preserved. The sandbox's existing clarification of pullback stability explicitly names the projection that belongs to T; this spells out the inherited hypothesis rather than strengthens it. No functorial splitting is assumed, no cancellation property is imposed on T, and all coherent transformations remain in the universal property.

The earlier attempt was unfinished. Its report claimed a second reading and altered the inherited created stamp, although this is still the first-reader handoff. I removed that second-reading section and restored the original stamp from the shared node. The delivery tool in fact preserves creation metadata on existing nodes.

The first dry run in this continuation failed on a dependency cycle. The current split of lem-coef-infinity-space-valued-pointwise-lan returns through lem-coef-infinity-join-cone-calculus, lem-coef-kan-quillen-right-proper and lem-coef-brown-fibrant-localization-pullbacks to this item. Consequently this item cannot cite that general theorem. It also cannot use lem-coef-system-localization-universal, which has a return path through isofibration-pullback-limit and Kan-Quillen right properness. Both are existing useful statements, but circular here; neither was modified.

The repair keeps the explicit horn localization construction, and formulates the general local-comma criterion directly as a statement-only input. That criterion is Theorem 7.2.8 with the comma-nerve identification of Remark 7.2.10, for arbitrary terminal-indexed diagrams. The parent still supplies the actual mathematical argument: it constructs I_x, identifies its comma category with the stated spans, builds the pullback right adjoint, and uses the split weak-equivalence factorization to prove locality. The criterion assumes this locality and an already supplied localization; it proves neither. Thus it is not a node saying merely that T-spans model mapping spaces under this item's hypotheses.

This is general localization infrastructure below the coefficient-adjunction comparison, not a replacement of a unit-level six-functor argument. The unrelated old biduality-unit metadata is inherited and is not changed. The only off-unit statement used as a generic tool is lem-cbc-enhanced-functor-cone-calculus, declared in split_report.tool_uses: it gives full functor quasicategories and the pointwise equivalence criterion; no same-unit input supplies that acyclic foundation.

## Not duplicates

lem-coef-edge-inverting-anodyne-extension vs lem-cbc-simplicial-groupoid-localization: the latter supplies an equivalence for a weak equivalence to a Kan complex; the new input supplies strict boundary lifts for an anodyne restriction, needed by the strict simplicial pushout construction. An abstract equivalence alone does not specify those lifts.

lem-coef-edge-inverting-anodyne-extension vs lem-coef-quasicategory-invertible-interval: the existing node treats endpoint evaluation for the walking isomorphism, rather than arbitrary all-edge-inverting anodyne restriction and compatible parameter-boundary data.

lem-coef-edge-inverting-anodyne-extension vs lem-coef-infinity-isofibration-exponentiation: the existing statement gives an isofibration for a monomorphism restriction, rather than trivial boundary lifting on the all-edge-inverting subcategories.

lem-coef-horn-completion-point-colimit vs lem-coef-presheaf-bounded-intersection-replacement: the latter gives a generic replacement with cardinal and intersection control; it does not give the weak homotopy comparison of the explicit countable horn attachment.

lem-coef-horn-completion-point-colimit vs lem-coef-kan-quillen-right-proper: the existing model theorem supplies replacement in a model structure, but does not state this explicit countable construction and would be circular as an input to this item.

lem-coef-horn-completion-point-colimit vs lem-coef-presheaf-cylinder-model-recognition: the existing theorem recognizes an abstract presheaf cylinder model structure, not the weak homotopy comparison for this prescribed horn construction.

lem-coef-terminal-local-kan-corepresentability vs lem-coef-infinity-space-valued-pointwise-lan: the latter gives existence and the pointwise colimit formula for coherent Kan extensions. It does not identify a W-local comma-nerve diagram with a localization corepresentable, which is the new conclusion. It is also cyclic as a dependency here.

lem-coef-terminal-local-kan-corepresentability vs lem-coef-weak-equivalence-representable-local-model: the existing node assumes a model category and identifies equivalence components between weak-equivalence objects by locally constant presheaves. The new criterion assumes only an ordinary relative category, a localization and a local terminal-indexed diagram, and computes whole mapping spaces.

lem-coef-terminal-local-kan-corepresentability vs lem-coef-trivial-fibration-fraction-model: the new criterion has no T, no pullback assumptions, no split factorization and no two-arrow-denominator category. Its arbitrary pi has local comma nerves as a hypothesis. The parent proves that hypothesis using the pullback adjunction and split factorization; it separately constructs the localization.

lem-coef-terminal-local-kan-corepresentability vs lem-coef-system-localization-universal: the latter constructs the localization; the new criterion assumes it and identifies a specified mapping-space diagram.

I reran whole-blueprint searches for anodyne, constant point, local Kan, calculus of fractions and corepresentable; there were no matching blueprint nodes. I searched the whole DAG for these concepts and the cited Cisinski places, and opened the relevant existing statement records above. The ordinary Lean-source hits concern scheme chart fractions or ordinary sheaf Kan extensions, not these enhanced results.

## Review by Q105

I checked the item against Cisinski Definition 7.2.20: T contains isomorphisms, is closed under composition and base change, and each w admits the two trivial-fibration retractions with a common section. The item does not need terminal objects or a full model structure. I checked the fraction morphisms against Remark 7.2.10; they are all commuting triangles, not only T-morphisms. The source calls 7.2.15 a Lemma, so the repaired step uses that designation.

For step 1 I opened Corollary 3.5.13 and Proposition 7.1.3. The new horn-completion statement supplies a functorial small Kan S and an anodyne NW -> S. The edge-inverting input explicitly asserts strict boundary lifting for H(S,E) -> H(NW,E), with unrestricted parameter directions; that is exactly the map needed in the pushout pullback. The enhanced definition gives the degreewise pushout and internal Hom conventions. Maps from a Kan complex send its edges to equivalences, since the inverse and triangle fillers are preserved by a simplicial map. W is an ordinary wide subcategory because its two-out-of-three condition gives composition closure.

For step 2 I read the actual inner-anodyne-pushout-product statement, a Mathlib leaf. It applies to an attached inner horn and a parameter boundary, with the latter degreewise injective. The step writes the stage-by-stage extension and the finite-domain argument for small inner-horn completion. It also writes the section and contraction argument for a boundary-lifting map. The functor-cone statement explicitly gives quasicategory closure of functor categories and their full subcategories, and its pointwise criterion makes the resulting transformations equivalences. No unnamed model-localization theorem is being invoked.

For step 3 I read localization-homotopy-category: it supplies essential surjectivity from precisely the coherent localization universal property already proved, and detects equivalence edges in hE. The saturation calculation is written out using ps=1 and rs=w, with p and r invertible after applying a T-inverting functor. It makes no natural choice of the splittings.

Step 4 is an elementary identification from slice, comma and span definitions. I checked that the unique arrow to 1_x is t, and that the two equations on h are exactly the span equations. The horn input supplies the only asserted replacement theorem. Smallness follows because the indexing objects and arrows are selected from those of A. The proof has no appeal to the newly cyclic pointwise-Lan lemma.

For step 5 I checked the directions of both functors and the Hom bijection against Lemma 7.2.15 and Theorem 7.2.16. The projection a of the pullback of v lies in T; composition then makes ta a denominator. A map into the pullback is exactly the indicated pair of maps satisfying fk=vf_0, so the bijection proves v_* left adjoint to v^*. The cited nerve-natural-homotopy-equivalence statement explicitly allows unit and counit components that are not isomorphisms. It therefore proves weak equivalence of these actual postcomposition nerves. Functorial horn completion permits the split ps=1, rs=w calculation in a strict space diagram, giving weak equivalence for all w in W, not merely for T. Natural completion maps then give the same assertion before replacement. No pullback of a general W-arrow is used.

For step 6 I opened Theorem 7.2.8, its proof, and Remark 7.2.10 in the online PDF. The new local-comma criterion includes the ordinary nerve formulation and the right-pinched mapping convention in its own statement, together with the component normalization. Each hypothesis has been proved: localization in steps 1-3; small terminal I_x and W-valued terminal cocone in step 4; and W-invariance of its comma nerves in step 5. The criterion is a generic reusable theorem, with locality as a genuine hypothesis. A minimal singleton I with pi=x would not automatically meet locality: for W=all arrows and A=[1], x=1, the comma nerve changes from empty at 0 to a point at 1. Thus the input does not hide the essential hypothesis the parent proves.

For step 7 I checked the criterion's explicit map-of-data and coherent-naturality clauses. U sends denominators to denominators, gives the required index functor and preserves its specified terminal object exactly; it need not preserve the pullbacks chosen to establish locality. The source's comparison is induced by the comma cocones and represents the space-valued functor, rather than only its pi_0. The proof therefore uses a statement giving the full coherent target-diagram compatibility, not an ordinary naturality lemma.

For each new input I read the source places listed in Literature needed. The horn construction has all its data written explicitly and leaves only a theorem unproved; finite horns factor through a finite stage, and no zero-dimensional horn adds a vertex to the empty complex. The anodyne restriction input leaves parameter edges unrestricted, matching h(-,E) in the source rather than its core k(-,E). The local-comma criterion introduces all objects and has no proof text in its statement. All three have empty proof, empty proof_deps, null proof_origin, complete definition dependencies and the exact ancestry of the item with this item prepended to via.

I tested empty A, a terminal category, a discrete category, and T equal to all isomorphisms. In a discrete category the off-diagonal span nerves are empty and the diagonal one is a point. For T the isomorphisms, the fraction f t^{-1} gives a terminal object in each span component, with the unique map t to its representative (1_x,f t^{-1}). The pullback adjunction's units and counits satisfy their triangles by uniqueness; neither is assumed invertible. The local criterion excludes empty I by requiring a terminal object. These checks found no statement dispute in the item.

All Mathlib records in the final files are exact query strings and result records from searches.jsonl. I ran leanfinder, loogle, grep and leansearch, with multiple semantic phrasings, for every new node and the item. I read the plausible ordinary localization, Kan-extension, OrthogonalReflection and simplicial horn sources. The pinned anodyne source explicitly marks its weak-equivalence characterization as TODO, so its lifting-class small-object result does not close the entire horn comparison. No search service failure was recorded as absence. I checked B-E for self-contained statement-only new nodes, every non-elementary fact assigned to a cited statement, exact quotations, no clause merely relabelled as a new input, acyclic dependency directions, actual hypotheses and the blueprint route. The previous cycle and invented second-reading conclusion were corrected.

## Completion

The split and self-review are complete; the full no-push server preflight is the final check. Nothing is delivered by this first reader. The unchanged accepted sandbox is for the independent second reader.

## Second reading by Q105

- Step 1: checked against Cisinski Proposition 7.1.3, Corollary 3.5.13, and the three cited node statements; the horn pushout and unrestricted parameter lifting match, with no missing hypothesis.
- Step 2: checked against the inner-horn completion argument, [lem-coef-inner-anodyne-pushout-product], and [lem-cbc-enhanced-functor-cone-calculus]; the lifting and coherent universal-property argument is valid, and vertex surjectivity is now explicit.
- Step 3: checked against [lem-coef-localization-homotopy-category] and the split-factorization equations; the saturation calculation correctly upgrades T-inversion to W-inversion and preserves full transformation spaces.
- Step 4: checked against Cisinski Definitions 7.2.2 and Remark 7.2.10 plus both cited statements; the slice terminal object, comma/span identification, smallness, and W-membership of span maps are correct.
- Step 5: checked against Lemma 7.2.15, Theorem 7.2.16, Corollary 7.2.18, and the cited nerve and horn-completion nodes; pullback orientation, adjunction, and split-factorization weak-equivalence argument all use the stated T hypotheses.
- Step 6: checked against Theorem 7.2.8 and Remark 7.2.10 and the local-comma node; every criterion hypothesis is supplied by steps 1–5 and the fraction component formula has the correct orientation.
- Step 7: checked against the functorial clause of Theorem 7.2.8 and the local-comma statement; applying a W,T-preserving functor gives the required index functor and coherent target naturality without assuming preservation of pullback choices.
- `lem-coef-edge-inverting-anodyne-extension`: checked against Cisinski Corollary 3.5.13; statement-only, self-contained, and its strict arbitrary-parameter boundary lifting clause is the needed result.
- `lem-coef-horn-completion-point-colimit`: checked against Cisinski Proposition 2.1.9, construction 2.4.36, and Section 3.1; statement-only, functorial, small, Kan, anodyne, weak-equivalence, and empty-case clauses are all explicit.
- `lem-coef-terminal-local-kan-corepresentability`: checked against Cisinski Definitions 7.2.2, 7.2.4, 7.2.6, Theorem 7.2.8, and Remark 7.2.10; statement-only and self-contained, with localization and comma-locality correctly hypotheses.

Changes made:

- Added the missing argument in item step 2 that inner-horn attachments add no vertices, hence the constructed localization functor is essentially surjective as required by the item.
- Added this second-reading record after checking every step, dependency statement, edge case (empty/discrete/terminal categories and isomorphism denominators), duplicate search, and citation quotation.
