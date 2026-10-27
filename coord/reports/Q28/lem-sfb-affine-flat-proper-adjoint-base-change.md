# Stage-1 worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-flat-proper-adjoint-base-change.json: item split into five steps, with its statement and inherited provenance retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-pullback-perfect-detection.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-perfect-hom-base-change.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-global-hom-right-adjunction.json: statement, unsplit, no Mathlib match.
- citations.json: one verbatim statement quotation for each step/node citation.

Three new nodes, zero Mathlib leaves. Each new node has an empty proof and introduces its own objects, site, coefficients, derived-functor convention and hypotheses. The item is written after its dependencies.

## Attachments

None. The item tag has no match in lean/WeilConjectures. The nearby declarations `AlgebraicGeometry.affineMorphism_hom_out_of_perfect`, `AlgebraicGeometry.affinePullbackPerfect_detects_iso`, `AlgebraicGeometry.schemeGlobalHomAdjunctionIso`, and `AlgebraicGeometry.proper_flat_rightAdjoint_baseChange_hβ` concern scheme structure-sheaf categories, not arbitrary algebraic spaces on their small etale sites. The last declaration proves pushforward base change rather than right-adjoint base change. They cannot attach this item or its space inputs. Existing project sorry declarations were not counted as completed proofs.

## WANTED

None. All the sources used are in the read clone.

## Corrections and scope

The item already corrects the type error in Stacks 0E5I: K must belong to D_QCoh(O_Y), since a(K) is otherwise undefined. I retained that correction and did not change its statement. No new statement dispute arises. No Noetherian or boundedness assumption has been added. The algebraic-space argument cannot be replaced by the existing scheme-only base-change nodes.

The source's long concluding diagram is realized by a shorter counit calculation: the defining mate gives the trace equation first, and that equation together with naturality identifies the induced global Hom map with the composite of the canonical scalar-extension and adjunction comparisons. This identifies the actual map; it does not infer invertibility merely from an abstract isomorphism of its source and target. No additional mate-coherence lemma is being assumed.

The proof follows spaces-duality.tex Tag 0E5I case (1) and 0E5L. The newest blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially direct-images step (3). This supporting coherent-duality item lies below the existing alteration/curve-stability route. It changes no unit or chapter route or realization. The inherited blueprint ancestor is null (as `blueprint_refs.py ancestor` reports); its existing detailed place and via chain are retained and extended in the new nodes.

## Not duplicates

lem-sfb-space-affine-pullback-perfect-detection vs lem-sc-affine-pullback-perfect-detects-iso: the existing node assumes schemes and their Zariski structure-sheaf derived category; the new node allows algebraic spaces and uses their small etale module categories.

lem-sfb-space-affine-pullback-perfect-detection vs lem-pc-perfect-generator-pullback: the existing node concerns a chosen generator on schemes; the new node is the shifted-Hom detection criterion for an arbitrary affine morphism of algebraic spaces.

lem-sfb-space-affine-pullback-perfect-detection vs lem-sfb-space-perfect-localizing-generation: the existing node says that perfect objects locally generate D_QCoh on a space, but does not assert that their affine pullbacks detect objects or that affine derived pushforward is conservative.

lem-sfb-space-affine-perfect-hom-base-change vs lem-pc-affine-morphism-hom-out-of-perfect: the existing node is for schemes; the new node allows a quasi-compact quasi-separated algebraic space over an affine scheme, on its small etale site. Flatness is a sufficient specialization of the source's Tor-independence assumption.

lem-sfb-space-affine-perfect-hom-base-change vs lem-sfb-flat-space-derived-pushforward-base-change: pushforward base change alone does not give global Hom base change out of a perfect source; the new node gives the canonical comparison of Hom complexes and its scalar-extension construction.

lem-sfb-space-global-hom-right-adjunction vs lem-pc-global-hom-adjunction: the existing node assumes schemes, so it does not supply the enriched global Hom adjunction on arbitrary algebraic spaces.

lem-sfb-space-global-hom-right-adjunction vs lem-sfb-qcqs-space-pushforward-right-adjoint: the existing node supplies an ordinary adjunction bijection and existence of a_f, not the canonical isomorphism of global derived Hom complexes in D(A).

The whole DAG was searched for the Stacks tags 09IY, 0E4R, 0E4S and 0E59, and for global Hom, affine/perfect and generator keywords. Whole-blueprint searches used `blueprint_refs.py search` with right adjoint, affine morphism, global hom, pullback generator, base change, 0E4S, 0E59, 0E4R and perfect generator. The source-tag overlaps and the relevant near matches are distinguished above; no imported blueprint node states one of the three new space assertions. The item itself is distinguished from lem-sc-proper-flat-right-adjoint-affine-basechange by allowing X to be an algebraic space, and also explicitly specifying the trace equation.

## Mathlib searches

The item and all three new nodes were searched through the prescribed msearch.py command, with two distinct LeanFinder phrasings, Loogle, source grep and LeanSearch. Exact queries and full returned hits are preserved in the corresponding mathlib_searches fields; searches.jsonl is the command's log, and the *-search-*.txt files retain its output. All services answered. Ordinary sheaf pullback/pushforward adjunctions, morphism properties, localization of derived categories and abstract `Adjunction.derived` do not supply the enriched algebraic-space assertions, so none was marked a leaf. In particular a categorical adjunction is not itself the global derived Hom comparison. No query was invented and no service failure was recorded as absence.

## Review by Q28

I read coord/delivery-errors.md sections B through E in full and checked the actual item and dependency statements against them. The new statements are generic inputs to the proof, not the item again: none asserts that the proper pushforward's right-adjoint base-change mate is invertible. None is a two-line specialization of an existing space node. Each is statement-only and has definition citations for schemes, algebraic spaces, modules, quasi-coherence and derived categories; perfection and affine morphisms are defined inline. The Hom nodes name internal derived Hom and define global Hom, with its coefficient ring made explicit. TeX uses a single mathematical backslash after JSON decoding.

For the detection node I read spaces-perfect.tex theorem-bondal-van-den-Bergh (09IY) and remark-pullback-generator (0E4R), including the statement that the equivalences hold for affine morphisms. Taking a cone gives precisely the shifted-Hom detection form stated here. Both spaces are required to be quasi-compact and quasi-separated. This is not a generator assertion for arbitrary morphisms: the affine hypothesis is essential and is retained.

For the perfect-Hom node I read spaces-perfect.tex lemma-affine-morphism-and-hom-out-of-perfect (0E4S), its map construction and proof, and remark-multiplication-map (0E4T). Case (1) allows arbitrary quasi-coherent Q. I restricted its Tor-independent square to flat f so that Tor independence is automatic, avoiding an undefined Tor-independence notion in a statement. A' is not required flat over A. The construction as extension of the pullback-induced map is printed before the proof's reductions and is included in the statement; the unit clause is the defining scalar-extension adjunction, not a hidden compatibility theorem.

For the global-Hom adjunction node I read spaces-duality.tex lemma-iso-global-hom (0E59), its proof and equation-sheafy-trace. It is the canonical counit-induced global Hom map that is invertible, not an arbitrarily chosen equivalence. The node is restricted to affine target so all global Hom complexes carry the coordinate-ring coefficients used by this proof. It retains arbitrary unbounded P and F and all quasi-compact/quasi-separated assumptions.

Step 1 cites flat-space-derived-pushforward-base-change for the canonical beta and quasi-coherent functor values, and affine-pullback-perfect-detection for exactly its shifted-Hom test. I opened both statements. Properness and the affine target give quasi-compactness/quasi-separatedness; h is affine by affine chart fibre products. There is no surjectivity assumption on g, and none is used.

Step 2 cites the new Hom base-change node at Q=a_fF and the global-Hom adjunction at (P,F). Both statements are unbounded, which matters here. The cited right adjoint is the one already chosen in the item, and the counit used to define d is the item's counit. The displayed comparisons therefore have identical objects and coefficient ring A.

Step 3 again uses global-Hom adjunction, this time on f', and the existing flat pushforward theorem for beta_P. I opened flat-proper-space-perfect-sections: it gives perfection of RGamma(X,P) for every perfect P under exactly the proper-flat-finitely-presented hypotheses. I opened affine-etale-derived-module-realization: its quasi-inverse is RGamma and it applies to every commutative ring, so no Noetherian assumption is smuggled in. Under it a bounded projective module complex sheafifies to a perfect complex. Applying the new Hom base-change lemma to f=id_Y is legitimate because the identity is flat, while g remains arbitrary. This avoids confusing flatness of f with flatness of the base-change map.

Step 4 is elementary: the adjoint of t is by definition Lg*epsilon composed with inverse beta. Applying the adjunction formula and cancelling beta proves the precise trace equation with the correct order of all three factors. It needs no new trace theorem node because the mate was specified by this formula in the item's statement.

Step 5 cites the three statements that fix the constructions of c, d and beta. I checked their statements, not only their proofs. Naturality of beta applied to the Hom argument followed by the step-4 counit equation makes the two underlying maps identical. Extension/restriction adjunction then gives equality of the B-linear maps of derived Hom complexes. This is the same verification as the final paragraphs of 0E5I, expressed with the mate's already specified transpose. Cancelling the established isomorphisms proves that the actual Hom map induced by t is invertible. The argument is not a cohomology-only identification of derived objects. The longest step is 1268 characters, below the 2000-character long-step threshold; it consists of this one naturality/adjunction calculation and hides no independent geometric lemma.

Small-case checks: for f=id the counit equation and beta reduce to the identity; for X empty every Hom test and both adjoint values are zero; for finite flat f the maps agree with finite-projective duality; for A to B a non-flat quotient the identity-case Hom comparison remains valid because its first input is perfect; and unbounded F is permitted in both Hom comparisons. I also checked that the new generic statements do not assert these facts for arbitrary non-affine h or non-perfect P. No choice from a sorried mere existence claim is made, and there is no Lean writing, compiler execution, SGA citation, or repository write.

## Unfinished work

No part of the item's split is left unfinished. The three new inputs intentionally remain unsplit under the one-level stage-1 contract. Server check_dag and review_split passed before the full delivery dry run. Final dry-run and push results are recorded below once available.
