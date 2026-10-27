# Stage-1 delivery: lem-pur-support-injective-exact-models

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-support-injective-exact-models.json: statement, split into six proof steps; not a Mathlib leaf.
- citations.json: verbatim statement quotations for every cited node at every proof step.
- report.md: this report.

No new nodes; zero new Mathlib leaves. The inherited statement, statement dependencies, source, creation record and blueprint provenance are preserved. The five inherited Mathlib searches remain as supplied source material; the five additional searches are the actual commands recorded in this sandbox's searches.jsonl.

## Attachments

None. I searched the project source for the item id, supported injectives and restriction/support rows. AlgebraicGeometry.ProEtale.shortExact_supportsShortComplex (WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/SupportsExact.lean:136) and its split-epimorphism input prove a sheaf-row subclause, not all the injectivity, global-section and derived-model clauses. Consequently this item cannot be attached to them as finished. No Lean was written or compiled.

## WANTED

None. All sources needed for the argument are available locally.

## Issues and corrections

The imported item was a statement-only lemma. Its statement is correct with its explicit quasi-compact complementary open hypothesis. There is no statement dispute or statement change.

The generic section-surjectivity assertion is already lem-pur-ringed-site-injective-mono-restriction (Stacks 093X); creating a second node would duplicate it. The general closed-support adjunction is already lem-sf-ringed-closed-kernel-adjoint, and the short exact sheaf row already lem-pur-support-exact. Their statements, not their proofs, are used. The nearby lem-pur-proetale-injective-support-global-model was also read; its statement has a localization-triangle dependency that is unnecessary for this row-level proof, so I use the lower-level existing tools directly.

The sources 09XP and 09XQ are written for etale abelian sheaves. They are not cited as if they directly asserted the pro-etale module statement. The proof is explicitly agent-origin, adapting their argument using the existing ringed pro-etale open/closed results and the general ringed-site theorem 093X. No SGA reference is used.

## Unfinished work

No mathematical work remains for this stage-1 split. The server review_split check passed. The full deliver.py --no-push preflight passed at c9e9a0e2641; after correcting the source line reference above I rerun the required dry run and then push.

## Not duplicates

No new nodes were created. The exactness, restriction-surjectivity, injective preservation and derived-computation facts are all reused from existing nodes.

## Review by NS

I read the item's statement, its chapter and sk-prop-a1 unit record, and the current main-20261015 ancestor proof and unit text. The role of this lemma is the injective-row foundation for the unit's localization and global supported-class interpretation, not an alternate purity or orientation proof. The unit and chapter are unchanged. I also read delivery-errors B through E in full and checked the split against their substantive objections.

For the item, I read etale-cohomology.tex Tag 09XP (section-cohomology-support: the first restriction row and definition of supported sections) and 09XQ (lemma-sections-with-support-acyclic: the Hom adjunction and exact closed pushforward argument). I read sites-cohomology.tex Tag 093X (lemma-restriction-along-monomorphism-surjective), including the free module/sheafification proof, and proetale.tex Tags 09BM (lemma-closed-immersion-complement-retrocompact-exact), 09BN (lemma-open-immersion) and 09AH (lemma-ses-associated-to-open). The latter explicitly assumes quasi-compact j, as does the item. I read sites-modules.tex Tag 03DJ (lemma-extension-by-zero-exact), homology.tex Tag 015Z (lemma-adjoint-preserve-injectives), and derived.tex Tags 05TH (lemma-injective-acyclic) and 05TI (lemma-enough-injectives-right-derived). There are no new nodes needing separate source review.

Step 1: I opened the statements of lem-sp-right-adjoint-preserves-injectives, lem-weil-pbc-proetale-ringed-open-closed, def-weil-pbc-proetale-operations and lem-sf-ringed-closed-kernel-adjoint. The first says precisely that an exact left adjoint has injective-preserving right adjoint. The open/closed theorem supplies exact j_! and i_* and j_! adjoint to restriction. The operations definition supplies exact i^*, j^* and their direct-image adjunctions with identified coefficient rings. The closed-kernel lemma supplies i_* adjoint to i^!_0. These establish injectivity successively for j^*I, j_*j^*I, i^!_0I and i_*i^!_0I. No unproved claim about arbitrary subsheaves of injectives is used. The vanishing below the bound follows because additive functors carry zero objects to zero objects.

Step 2: I opened lem-pur-support-exact and def-pur-flasque-support. The former states the exact row for a termwise-injective complex with finite commutative coefficients and quasi-compact open complement; it explicitly characterizes both arrows. The latter identifies the supported kernel with the closed pushforward via the closed unit under the same hypothesis. This step takes only those clauses. It does not infer sectionwise surjectivity merely from a sheaf epimorphism.

Step 3: I opened lem-weil-proetale-weakly-etale-localization, def-weil-pbc-proetale-operations, lem-pur-ringed-site-injective-mono-restriction and def-pur-flasque-support. Localization identifies the actual open inverse image with restriction and identifies constant scalar sheaves; its clause (4) says the open is a monomorphism. The direct-image formula evaluates at the fiber product, hence at X gives sections on U, with the same A-action. The ringed-site theorem says every injective module sheaf restricts surjectively along a monomorphism; it assumes neither enough points nor injectivity of the underlying abelian sheaf. Thus its hypotheses hold on the chosen small pro-etale site. The supported-kernel formula supplies the first term and its induced differential. This verifies the stronger sectionwise assertion independently of step 2.

Step 4: I opened lem-weil-pbc-ring-sheaves-grothendieck and lem-sp-grothendieck-enough-injectives, verifying their arbitrary-small-ringed-site scope, then lem-weil-pbc-right-derived-plus-injective, whose clause (2) gives the canonical derived-computation isomorphism for every bounded-below complex of injectives. I checked the input for Rj_* is j^*I, whose injectivity was proved in step 1. The exact-functor cohomology node gives natural cohomology comparison, hence preservation of quasi-isomorphisms for i_* and j^*. During this review I made explicit a possible hidden comparison: the operations node uses unbounded K-injective derived functors, whereas the computation lemma is stated on D^+. I read and cited lem-weil-pbc-bounded-below-injectives-kinjective and lem-weil-pbc-kinjective-hom-derived. They say bounded-below injective complexes are K-injective and quasi-isomorphisms between K-injectives are homotopy equivalences. Additive termwise functors preserve such homotopies, giving the same model and comparison, not just an unspecified isomorphic object.

Step 5: I rechecked clause (2) of the right-derived computation theorem against all three section inputs; step 1 has proved each is bounded below and termwise injective in its own source category. I read def-pur-support-cohomology through its final pro-etale finite-coefficient clause. Here the functor is explicitly kernel of restriction, valued in A-modules as introduced by the item. Applying the computation theorem to that functor and using the literal sectionwise kernel from step 3 proves the first derived-section identification. The proof keeps module complexes distinct from sheaves.

Step 6: I checked the displayed naturality squares directly from the unit square and restriction to kernels. The support definition explicitly makes the kernel identification natural. The derived-computation node explicitly supplies a natural transformation alpha, so its isomorphisms commute with all chain maps. This step is elementary relative to those statements: it writes the actual commuting equations and uses no choice of section/splitting. Every cited node in these six steps has its statement copied verbatim in citations.json.

For small cases I checked Z empty (support term zero, restriction identity), Z=X with U empty (support term I, right term zero), the zero complex and a complex concentrated in a single degree, zero coefficient ring (all terms zero), and disjoint unions (sections are module products, never rank-one sheaves masquerading as single modules). Quasi-compactness is used exactly where the closed support identification and exact i_* require it; no extra Noetherianity, constructibility, finite-dimensionality or scalar-forgetting injectivity is introduced. A common strict lower bound survives all additive functors. I checked dependency paths back to the item before citing the support-exact, closed-adjunction, open/closed, localization and enough-injectives tools; none creates a cycle. Every proof step is shorter than 2000 characters and none hides a new independent lemma. Off-unit generic tools are declared individually in split_report.tool_uses.

The actual Mathlib searches used LeanFinder twice with distinct statements, Loogle, LeanSearch and grep through the required wrapper. I read the hits: MayerVietorisSquare.shortComplex_shortExact is the free-sheaf Mayer-Vietoris row, not this supported restriction row; locally injective sheaf morphisms concern monomorphisms, not injective objects. The generic injective-preservation theorem in Preadditive/Injective/Preserves.lean:49 and KInjective.lean:133 are already represented by existing DAG nodes. This does not make the complete item a one-line Mathlib specialization, and creates no new leaf.
