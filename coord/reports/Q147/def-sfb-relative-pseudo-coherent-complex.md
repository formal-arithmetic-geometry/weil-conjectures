## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/def-sfb-relative-pseudo-coherent-complex.json: definition, split; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/def-sfb-m-pseudo-coherent-complex.json: new definition, unsplit; no exact Mathlib match.
- citations.json: empty list, because this definition has no proof steps.

Attachments: none. Searches for the item id, relative pseudo-coherence and RelativePseudoCoherent in lean/WeilConjectures found no declaration. The existing AlgebraicGeometry.Scheme.IsPseudoCoherent is absolute all-degree pseudo-coherence, and AlgebraicGeometry.Scheme.IsStrictlyPerfect supplies only the approximation ingredient, not this item.

WANTED: none; all sources were available locally.

The item already had a correct expanded definition but had not named several ingredients as dependencies. I moved the absolute m-pseudo-coherence paragraph into a separate supporting definition and cited the existing affine-space and closed-immersion definitions. No mathematical hypothesis, conclusion or quantifier changed. The item still concerns complexes, not the additional module clauses (3)-(4) of Stacks 09UI.

Nothing unfinished within the requested split. The supporting definition is intentionally statement-only and unsplit, as required for a one-level stage-1 split. There are no Lean changes or compilation commands.

## Sources and blueprint searches

Item: literature/stacks-project/more-morphisms.tex, Tag 09UI, definition-relative-pseudo-coherence, lines 16674-16695; its clause (1) references lemma-relatively-pseudo-coherent, whose condition (1), lines 16616-16618, is precisely existence of an affine-space closed embedding with m-pseudo-coherent derived pushforward. I read both conditions and the preceding finite-type affine-chart discussion, lines 16666-16672. Selecting condition (1) as the definition does not assert independence of embeddings or require that lemma as a dependency.

New definition: literature/stacks-project/cohomology.tex, Tag 08CB, definition-pseudo-coherent, lines 11957-11975; Tag 08CC, lemma-pseudo-coherent-independent-representative, lines 11983-12012, explicitly supplies the derived-morphism formulation. Tag 08C4, definition-strictly-perfect, lines 11601-11609, agrees with def-pc-perfect-complex. The tag-label mapping was read in stacks-project/tags/tags.

Before creating the node I searched the whole DAG for 09UI, 08CB, 08CC, pseudo-coherent and m-pseudo-coherent, inspected all definition nodes containing these notions, and searched the project Lean for MPseudoCoherent and its variants. tools/blueprint_refs.py search was run for pseudo-coherent, relative pseudo, 09UI, pseudo, m-pseudo and 08CC. No imported blueprint node defines scheme-level m-pseudo-coherence. The one broad pseudo hit was an unrelated pseudocolimit construction. The ancestor command returns None for this item: its inherited creator chain has no surviving imported blueprint ancestor. I retained that null ancestor and its full inherited place, rather than inventing one. The new node extends the same via chain by this item.

I read the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.md and .proof.md. The precise inherited place is the supporting cohomology-and-base-change chain below direct-image clause (3). This delivery supplies a definition needed there; it changes neither the current unit statement nor its proof route. The chapter and unit DAG records were also read; the historical unit record differs from the newest blueprint and was left untouched.

## Mathlib searches

Every new-node search was run through the mandated msearch.py command with Q147 and this item; searches.jsonl is the actual command log. The node records reproduce its tool and query strings. The item was searched by its relative affine-embedding description; the new definition was searched by local strictly-perfect approximation and by finite-projective approximation with a cohomology bound, together with LeanSearch, Loogle and whole-Mathlib grep. All services answered successfully. Loogle and grep found no pseudocoherent or strictly perfect definitions in Mathlib. LeanFinder returned generic t-structure or K-projective facts; LeanSearch returned finite-presentation and quasicoherence declarations. I read the generic TStructure and sheaf Quasicoherent source: they impose no finite-rank local approximation condition of this kind. None is an exact match or a one-line specialization.

## Not duplicates

def-sfb-m-pseudo-coherent-complex vs def-pur-pseudo-coherent-complex: the latter defines absolute pseudo-coherence, quantified over all degrees; the new node defines one fixed-degree approximation condition on an arbitrary scheme. All-degree bounded-above free models do not define the weaker fixed-degree notion.

def-sfb-m-pseudo-coherent-complex vs def-pc-ring-m-pseudo-coherent: the latter is a condition on an object in the derived category of modules over one ring, with a global finite-free approximation; the new node is on the derived category of all structure-module sheaves of any scheme and uses an open cover and strictly perfect approximations. No affine or quasi-coherent hypothesis is imposed.

def-sfb-m-pseudo-coherent-complex vs def-pc-perfect-complex: the latter defines strictly perfect complexes and perfect objects, which locally have a full derived isomorphism to such a complex. It supplies that ingredient; it does not define approximation only above a selected degree.

def-sfb-m-pseudo-coherent-complex vs lem-pc-affine-pseudo-coherent-localization-cover: that statement assumes full pseudo-coherence of a sheafified ring complex and produces principal localizations with full pseudo-coherence; it neither defines nor states the fixed-degree condition on arbitrary sheaf-derived objects.

def-sfb-m-pseudo-coherent-complex vs def-sfb-relative-pseudo-coherent-complex: the old item contained the absolute ingredient inline. The item after refactoring defines the relative condition using pushforwards into affine space; the new node defines only the ambient absolute fixed-degree condition, without a base morphism, closed embedding, or relative quantifier. This is extraction of a constituent notion, not a replacement theorem restating the relative conclusion.

def-sfb-m-pseudo-coherent-complex vs lem-sc-local-strict-perfect-stalk-projective-model: produces a bounded projective stalk model from a given local perfect representation; it does not define fixed-degree approximations on a covering.

def-sfb-m-pseudo-coherent-complex vs lem-sc-picard-scalar-derived-cycles: constructs a Picard derived test class from a based perfect model with a special differential; it does not define m-pseudo-coherence.

def-sfb-m-pseudo-coherent-complex vs def-affine-finite-free-model-complex: constructs the associated sheaf cochain complex from a given affine module chain complex; it does not specify the fixed-degree approximation predicate.

def-sfb-m-pseudo-coherent-complex vs lem-affine-finite-free-perfect-comparison: compares the explicit sheafified affine resolution with a degree-zero sheaf via a full derived isomorphism; no m-approximation predicate is stated.

def-sfb-m-pseudo-coherent-complex vs lem-affine-finite-free-perfect-core: proves strict perfectness of a given bounded finite-free sheafified complex; strict perfectness is an ingredient of the new definition, not the condition being defined.

def-sfb-m-pseudo-coherent-complex vs lem-pc-strictly-perfect-finite-free-refinement: refines a full local strict perfect model to a finite-free model, assuming E is already isomorphic to that model; the new predicate requires only isomorphisms above m and surjectivity at m.

def-sfb-m-pseudo-coherent-complex vs lem-sc-affine-finite-free-resolution-perfect-model: constructs a strictly perfect derived model of a module from a specified finite-free affine resolution; the new definition applies to arbitrary sheaf-derived complexes and partial cohomology approximations.

def-sfb-m-pseudo-coherent-complex vs lem-sc-open-module-stalk-free-projective: states projectivity of the stalk of a finite-rank free sheaf; it says nothing about approximation of a derived object through a selected degree.

def-sfb-m-pseudo-coherent-complex vs lem-sc-open-perfect-model-transport: transports a full perfect representation across restriction and an isomorphism; it does not define weaker fixed-degree approximations.

def-sfb-m-pseudo-coherent-complex vs lem-sc-perfect-qcoherent: deduces quasi-coherent cohomology from perfectness; the new node is a definition and has neither that hypothesis nor that conclusion.

def-sfb-m-pseudo-coherent-complex vs lem-sc-strict-perfect-closed-pushforward-stalk-model: extracts a projective stalk model from a strict perfect model of a closed pushforward of a structure sheaf; it does not define local m-pseudo-coherence of arbitrary derived objects.

## Review by Q147

I read the item and its new definition against the source passages listed above. In 09UI the morphism is locally of finite type, the complex belongs to the unbounded derived category of all structure modules, the base cover is affine, and the source cover is affine over each base member. These hypotheses and both complex clauses are preserved. The selected embedding is a closed immersion over its base member, its dimension is allowed to vary, and the pushforward lies on the ambient affine space, not on the base. I checked the source definition does not require one common collection of charts for all m; the final sentence retains that distinction. I introduced m explicitly after extracting the original paragraph so it is not a free variable.

I opened the statements of def-pc-scheme, def-pc-morphism-conventions, def-pc-derived-category and def-pc-derived-direct-image: respectively they define affine/open subschemes, the locally-finite-type convention, D(O) for all module sheaves, and derived direct image computed by K-injective resolutions. I opened def-weil-closed-immersion and def-nagata-relative-affine-space: they give the closed embedding and relative affine-space notions used in the item. For the new node, def-pc-perfect-complex explicitly defines strictly perfect as bounded with terms direct summands of finite free structure modules, exactly 08C4. Thus every cited definition says what is taken from it. There are no proof steps, so the C1/C4 proof-step checks and verbatim citation entries are vacuous; inventing an assembly proof would add a theorem to a definition. Both proof lists and both proof dependency lists are empty, and citations.json is [].

I tested the new definition on the empty scheme, where the empty covering is allowed, and on the zero object, using the zero strictly perfect complex. For the point Spec(k), a finite-dimensional vector space in degree zero admits its identity approximation. An infinite-dimensional vector space in degree zero is 1-pseudo-coherent via zero but not 0-pseudo-coherent: cohomology in degree zero of a bounded finite-dimensional complex cannot surject onto it. This checks both the strict inequality j>m and the separate surjectivity condition, and demonstrates why the existing all-degree notion is not a duplicate. No uniform global bounds, quasi-compactness, quasi-coherence, Noetherianity or separatedness were added. In relative dimension zero the notation permits n=0; no positive dimension is assumed.

I checked B-E: all new objects and indices are introduced, TeX uses single mathematical backslashes, source tags name their local labels, no unrun or unavailable search is recorded as a failed match, the supporting node contains a statement only, and the existing broad notions are reused. No claim about embedding independence, existence of perfect approximations, or quasi-coherence was inserted as a hidden theorem. No proof step exceeds 2000 characters because this is a definition. The only corrections were dependency extraction and making m explicit. The definition and its source are mathematically consistent, so no STATEMENT-DISPUTED is called for.

The first dry run requested explicit comparisons for eleven further nodes sharing 08C4. I opened and read every full statement, added each comparison under Not duplicates, and confirmed that they concern explicit models, stalks, or consequences of perfectness rather than the new approximation predicate. No duplicate was found.
