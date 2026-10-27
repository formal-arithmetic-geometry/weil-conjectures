# lem-pur-integral-pullback-roos-realization — ND

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-integral-pullback-roos-realization.json: statement node, now split; full original statement and normalizations retained. No Mathlib match for the whole item.
- citations.json: exact statement quotations for all seven step/node citations.
- searches.jsonl: unmodified output log of the required msearch commands.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The existing Mathlib leaf lem-weil-pbc-exact-functor-derived-factorization is reused.

## Attachments

None. Searches in lean/WeilConjectures for the blueprint tag, pullbackTensorIntegralPullbackModel, reference-model name and integral/Roos vocabulary found no matching declaration. The live node's candidate points to a local Sheaf module whose file is absent in this read clone; its historical candidate is not evidence of a finished project proof. IntegralPullbackDescentComponents.lean does contain the separate generic component lemma, and IntegralDerivedOperations.lean contains the actual descent record and its normalization. Neither states the full item, so neither is an attachment for it. No compiler was run.

## WANTED

None. The assembly argument is explicitly agent-written. The blueprint and the local Stacks texts needed to identify its route and distinguish its assumptions are available.

## What was wrong or incomplete

The item had no proof. Its split_report retained an earlier proposed argument, explicitly marked unverified. I retained this historical text and supplied the actual three-step assembly. There is no statement correction and no change to statement dependencies.

The retained argument's key task is naturality of c in the input complex. Its existence as a strict tower isomorphism is already specified by the item and core, so a second node asserting that same comparison would duplicate the data. Step 1 now writes the component naturality equation and explains why it is an equality of strict tower morphisms. Step 2 applies the whole Roos functor, using both cone coordinates, instead of trying to identify a derived morphism from finite projections. Step 3 instantiates the existing normalized-descent component lemma with all seven parameters explicitly named.

The ancestry is already broken at the parent's created.item, which is a module name. blueprint_refs.py ancestor reports None. I preserved the inherited null ancestor and its detailed documentary association rather than inventing a repaired created chain or editing another node. The current latest blueprint places sk-def-purity-conv under sec-six-functors-basics, while the historical DAG unit remains under sec-smooth-purity. This item is not that unit's key statement and changes neither unit nor chapter.

## Searches and reuse

The required archive glob over all groups returned no directories for this item. The sandbox initially held only dispatcher brief markers. Its item was therefore taken from the live DAG. No archived searches were available to reuse. The live node's NF search records are retained as inherited evidence, not represented as my searches; my five actual msearch records are appended from searches.jsonl with their timestamps and results.

The new searches used LeanFinder twice, Loogle, source grep and LeanSearch. The Loogle query reported unknown identifier CategoryTheory.NatIso; this is a failed name lookup, not evidence against the concept. LeanFinder found leftDerivedUnique, leftDerivedNatIso and mapDerivedCategoryFactors, and the second phrasing found Localization.liftNatIso. I read Mathlib/CategoryTheory/Localization/Predicate.lean lines 320–380 and Algebra/Homology/DerivedCategory/ExactFunctor.lean lines 20–85. These are generic localization and exact-derived tools, with additional structure/hypotheses, not the prescribed full Roos theorem. The DAG already has the precise exact-derived factorization leaf, so it is cited without a new leaf. LeanSearch's sheaf-pullback and ordinary categorical pullback hits do not contain the completed reduction/limit functor or full normalization equation.

Whole-DAG concept searches and blueprint_refs searches for Roos realization, normalized descent, coherent reduction and completed integral pullback found no duplicate of this full theorem. The broad pullback search was also inspected; the refined searches isolated the relevant scope. No new fact was declared absent without the second phrasing.

## Not duplicates

No new nodes were created. The core, strict Roos functor, strict finite-pullback tower, exact-derived factorization, normalized descent model, and generic component lemma already exist and are reused.

## Review by ND

I read the latest blueprint's def-weil-frobenius-coefficient-twists, its sk-def-purity-conv, and the smooth-purity chapter, together with the DAG chapter and unit records. The supporting phrase is compatibility with finite reduction and scalar extension; the chapter's purity route is untouched. I read Stacks sites-cohomology.tex, Tag 0941 (lemma-derived-limit-is-ok), derived.tex, Tag 08TC (definition-derived-limit), and proetale.tex, Tag 099N (lemma-pushforward-Noetherian-case), including part (5). In particular 08TC says an abstract triangulated homotopy limit is only nonuniquely isomorphic, and 099N(5) concerns complete inputs. Neither is cited as a proof of unique normalization on the ambient category. The existing fixed core and ambient normalized descent, explicitly included in the item's assumptions, supply those stronger data; this split is their categorical assembly. I also read the separate component lemma's complete statement and Lean proof, and the IntegralPullbackDescent structure, comparison and universal fields.

For step 1 I opened the core and finite-pullback-tower node statements. The former supplies the already strict comparison, the latter explicitly defines its target on chain maps. The input-dependent factors are natural isomorphisms of module functors, hence of termwise cochain functors; their inverses are natural by multiplying the naturality equation by inverses. Composing those equations proves the displayed equation for c. Equality of families is the definition of equality of strict tower maps. No exactness, product preservation by pullback, or derived conservativity is used here. This is a routine assembly step, not a new comparison theorem.

For step 2 I opened the core, exact-derived-factorization and strict-Roos statements. The core data fix natural m and rho with the normalizations repeated fully in the item; their existence and uniqueness are not reproved here. The factorization leaf states a natural isomorphism from the derived exact functor to its termwise model, applicable to both exact F_f and exact U_X. The strict Roos node states the two-coordinate product map on tower transformations. Composition and whiskering of these specified natural isomorphisms gives exactly the displayed mu, including its order and both cone coordinates. This also explains why no product-preservation theorem for F_f is needed. I did not use the internal-Hom or normalized-system conclusions of the much larger coefficient-calculus node.

For step 3 I opened both cited descent statements. The descent model gives precisely the existence and uniqueness hypothesis of the generic component lemma, with the actual epsilon and the same good-representative category. Step 2 supplies its natural c=mu, on every good object and chain map. The formula from the component lemma is epsilon followed by inverse mu, the same as inverse mu composed with epsilon in the item's convention. Thus uniqueness is for the required full formula, with no extra assumption that good objects form a full subcategory of derived objects. The generic lemma is applied in the compatible chosen universes already fixed in the item. The off-unit descent model is declared in split_report.tool_uses as the existing generic normalization tool.

Against delivery-errors B–E: there are no new statements, new definitions or new leaf claims to typecheck; all original TeX and provenance fields are retained. The explicit citations file quotes the statements, never their proofs. Every non-elementary imported theorem in the assembly is cited: exact-derived factorization and normalized descent, with the core comparisons supplied as fixed data. Elementary steps only compose natural transformations or compare componentwise families. The proof does not move a clause into a fresh node, introduce a cycle through the parent realization node, or silently repair a target. All steps are below 2000 characters. I checked P=0, a zero chain map, f the identity, and the empty scheme: all equations are naturality or inverse cancellation and remain valid. Arbitrary noncomplete inputs, unbounded complexes, and schemes where ell is not invertible are covered because none of these properties is used by the assembly. No new smallness assumption on an indexing category is introduced; towers retain the given natural-number index and fixed site universes.

## Unfinished work

None for this one-level split. The existing core and normalized descent nodes remain responsible for their own constructions; no new unsplit obligations are concealed here. No Lean source, repository file, archive, or launcher script was changed.
