# Repair: lem-sfb-scalar-model-immersion-extension

NQ, 2026-10-22; direct delivery, no other agents.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-scalar-model-immersion-extension.json`: same statement, three assembly steps, 1845 proof-text characters. Original searches and all maintainer-owned fields retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-complementary-stratifications.json`: statement-only, status unsplit, no Mathlib match. Geometric work of former steps 1–2: Noetherian sources, qcqs target and sources, quasi-compact open immersion, and actual complementary finite constructible stratifications.
- `dag/nodes/sec-six-functors-basics/lem-sfb-scalar-model-restriction-criterion.json`: statement-only, status unsplit, no Mathlib match. Common argument of former steps 4–6, formulated for arbitrary modules with specified same-side and zero complementary restriction isomorphisms and a specified extended stratification.
- `citations.json`: six entries, one per parent step/node pair, quoting the cited statements verbatim.
- `searches.jsonl` and `search-0.txt` through `search-16.txt`: actual prescribed msearch queries and retained output. The two new nodes record their own relevant queries and results, including unavailable/error results honestly.
- `report.md`: this review and the former six-step proof verbatim below. `previous-report.md` retains the live NW report in the sandbox, and `original-proof.json` retains the former proof in machine-readable form. Neither ancillary file is a DAG change. No Lean or unit file is written; no compiler, Lake or build command is run.

Two new nodes, zero Mathlib leaves. This item is not the key node of its unit, so no realized fields are changed.

## Attachments

None. The exact blueprint-id and name searches in lean/WeilConjectures find no finished declaration stating the item. The current Sheaf.Paper.ScalarModelImmersionExtension theorem ends in sorry. I read the nearby sorry-free upstream open-extension theorem `AlgebraicGeometry.ProEtale.CondensedRing.isConstructibleModuleObject_openImmersionLowerShriek_obj` in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/LowerShriek/Constructible.lean:145`: it uses arbitrary locally finite presentations, not the fixed scalar-matrix local models, and supplies only the open half. Its composite-pullback helper has the same distinction. No attachment is claimed for either new node. Scheme stratification constructors in the project provide ingredients for the first node, but do not state its combined geometric assertions.

## WANTED

None.

## What was wrong and what changed

This repairs the single numbered return: the six-step 4250-character proof needed to be divided into at least two comparable independent tasks, delivered unsplit, leaving at most 3000 characters in the parent. The original statement is true and remains byte-identical. The new node statements have 1332 and 1651 characters; they encode different mathematical work rather than the two open/closed clauses of the item. The original ringed-site comparison step remains in the parent. Its argument, including the coefficient/module comparisons and exactness, is not replaced by an assertion of the final preservation theorem.

The complete former proof is retained below, with this allocation:

1. Former step 1's Noetherian and qcqs argument belongs to noetherian-complementary-stratifications. The parent fixes the model witnesses using the existing constructibility definition. The new geometric statement explicitly includes T as qcqs, supplying the minor implicit fact noted by the former reviewer.
2. Former step 2's descending-chain/minimality argument, quasi-compactness over affine opens, actual immersion composites, finite partition and constructible images all belong to noetherian-complementary-stratifications. They are not erased by shortening the parent.
3. Former step 3 remains verbatim except its backward reference is now to step 1. It supplies exactness, same-side identities and zero cross restrictions via the existing three comparison/excision statements.
4. Former step 4's pullback composition and retention of each fixed cover and scalar module belong to scalar-model-restriction-criterion. Its statement explicitly supplies the composite-stratum and cover-level isomorphisms.
5. Former step 5's zero-model witness, identity cover, rank-zero presentation, zero scalar extension and use of the adapted stratification belong to that same general criterion.
6. Former step 6 is the second application of the same criterion. It retains every closed-side model and supplies the zero open model, rather than introducing a new node restating the closed half of the item.

These two new tasks are requested by the explicit human re-split decision. The scalar criterion packages the full common witness argument (formerly three elementary steps); a separate zero-model node is still unnecessary. Its hypotheses deliberately take the restriction identities and geometric stratification as input, so it proves neither excision nor either extension functor's constructibility. The geometry task has no coefficients or sheaves. Neither restates the original theorem, and neither depends on it.

## Not duplicates

No new source field carries a Stacks tag: their source is the identified paragraph of the blueprint proof, expanded by the retained argument. Whole-DAG searches included the tags 01OZ, 02V0, 005L and the phrases stratification/complement, scalar-model/restriction and finite-constant-local-model; all blueprint chapters were searched with blueprint_refs.py (stratification, complement, constant local model, scalar model, restriction isomorphism, composing). The nearest imported ancestor is det-lem-integral-models-operations; both new nodes have via [lem-sfb-scalar-model-immersion-extension] and precise paragraph-(3) places. No imported statement states either complete new assertion; same_as is empty.

lem-sfb-noetherian-complementary-stratifications vs lem-sfb-finite-stratification-wide-pullback: the existing node constructs fibre-product refinements on a common open, whereas the new node retains each specified source stratum and adjoins the given complementary scheme, also proving the qcqs/quasi-compact hypotheses.
lem-sfb-noetherian-complementary-stratifications vs lem-finite-constant-models-common-reduced-stratification: the existing node chooses a new common reduced ordered stratification for a family of modules; the new node has no modules and preserves an arbitrary given source stratification and the given, potentially nonreduced, complement.
lem-sfb-noetherian-complementary-stratifications vs lem-weil-pbc-proper-fp-permanence: its immersion-composition clause is an ingredient, not the complete geometry statement; reuse it when the new task is split.
lem-sfb-scalar-model-restriction-criterion vs lem-sf-open-extension-zero-constant-model-constructible: the existing node proves one particular open-extension assertion over separated finite-type schemes over a field, whereas the new criterion assumes the restriction identities for an arbitrary ambient module on qcqs schemes and treats either immersion order without a field.
lem-sfb-scalar-model-restriction-criterion vs lem-sfb-scalar-normalized-constant-models: the existing statement compares scalar modules through an equivalence with constant coefficient sheaves; the criterion uses the same internal coefficient ring throughout and restriction along composite stratum immersions.
lem-sfb-scalar-model-restriction-criterion vs lem-sfb-pullback-constant-model-constructible: the existing theorem proves stability under arbitrary pullback with base-changed strata and covers; the new criterion retains a prescribed source cover using an already supplied restriction isomorphism and zero complement.
lem-sfb-scalar-model-restriction-criterion vs det-def-sfb-constructible-local-model: the latter defines the models and compares their presentations; it has no complementary-stratification or composite-restriction assertion.
lem-sfb-scalar-model-restriction-criterion vs lem-weil-pbc-site-tensor-local-model-comparison: the latter is a statement about cohomology of derived tensors on a small site, not underived complementary restriction data.
lem-sfb-scalar-model-restriction-criterion vs lem-weil-pbc-finite-free-constructible-scalar-transport: the latter changes completed integral coefficient rings in derived categories, while the criterion changes no coefficients or scalar presentations.

## Mathlib searches

All seventeen queries ran with the unmodified prescribed msearch command. Relevant queries/results are copied exactly into each node and remain in searches.jsonl. Both nodes have semantic searches with two phrasings, Loogle, LeanSearch attempted, and source grep. Geometry semantic hits include IsLocallyNoetherian.quasiSeparatedSpace, IsNoetherian.noetherianSpace and IsImmersion.comp; these state ingredients and are already represented by existing nodes. Mathlib has no matching scheme-stratification assembly result. The scalar searches found ordinary sheaf finite presentation (Quasicoherent.lean:267), which allows arbitrary ring-sheaf matrix entries and has no fixed scalar-model stratification criterion. The first scalar Loogle pattern contained an unknown identifier; I corrected it to SheafOfModules.IsFinitePresentation and read those hits. The scalar LeanSearch request was rate-limited and is recorded unavailable. No unavailable service is used as evidence of absence. Ancillary file-target greps exposed an output formatting limitation of msearch; their raw results are preserved, and repeated directory-target greps recover proper file/line hits. No claimed leaf depends on those partial results.

## Review by NQ

I read the worker brief, delivery-errors B–E in both copies, GOAL, the three levels of SETUP, the stage-1 document, the chapter and unit records, the live item and its Lean theorem, its previous NW report and the maintainer's review. The sandbox initially contained only brief markers; there was no prior sandbox split/report/search log to dry-run or overwrite. I copied the current item and kept its original statement, searches, blueprint ancestry and maintainer fields. The prescribed delivery tool will overlay split-owned fields on the current server base; no git command was run in the shared read repository.

For the item I read main-20261015 sk-lem-integral-models-operations.proof.md paragraph (3). It gives the immersion-extension route and says the open is quasi-compact in the Noetherian setting. I read the exact local-model definition in sec-proetale-coefficients/sk-def-sfb-constructible/_section.md: a witness uses finitely presented modules over Lambda(*), not arbitrary presentations over R_V. This is why ordinary local-finite-presentation theorems cannot replace the scalar witness argument.

For the geometry task I read the statements of all former step-1 and step-2 dependencies: open subschemes of Noetherian schemes, closed immersions proper including finite type, finite type over Noetherian, locally Noetherian implies quasi-separated, minimal closed subsets, compactness of all subsets in a Noetherian space, open-immersion homeomorphisms, composition of immersions, finite stratifications and constructible subsets. I also read Stacks properties.tex Tag 01OZ, lemma-Noetherian-topology; schemes.tex Tag 02V0, lemma-composition-immersion; topology.tex Tag 005L, lemma-constructible-Noetherian-space, including their proofs. These sources explain the actual argument assigned to the first task: obtain Noetherian U and Z, apply quasi-separatedness to T as well as U,Z, deduce the descending-chain condition from minimality, use compactness of every subset to check j on each affine inverse image, and compose the given immersions before checking the partition. There is no inference of scheme factorization merely from containment of point sets, and no reducedness or finite-presentation hypothesis is introduced.

For the scalar restriction task I read sk-def-sfb-constructible and det-def-sfb-constructible-local-model in full and the entire statement of sk-def-sfb-module-pushforward-pullback. Its displayed composition isomorphism is precisely (h s_a)^* = s_a^* h^*. Given h^*H isomorphic to M, pulling back and then composing with the specified old model isomorphisms retains every cover and every P. This needs no preservation theorem for finite presentations by h_! or h_*. The zero restriction on k has the identity pro-etale cover, the finitely presented scalar zero module, and its rank-zero matrix presentation; R tensor zero is zero. The supplied ambient finite constructible stratification then satisfies the qcqs clause of the constructibility definition. These are all conclusions of the new task, not a hidden appeal to the old item. The retained former proof below gives future workers the complete intended argument while their DAG node remains statement-only as required.

Parent step 1 cites exactly the new geometric statement and the existing constructibility definition. The former supplies all qcqs and stratification hypotheses, and the latter supplies the covers and models; neither must be read through its proof. In particular T is qcqs, a fact the old proof had left implicit. Step 2 cites exactly lem-weil-pbc-proetale-ringed-open-closed, sk-prop-sfb-cartesian-coefficients and lem-sfb-internal-module-operations-transport. I opened all three statements. The first explicitly gives both exact functors, both same-side restriction identities and both zero cross restrictions for a quasi-compact complementary open. The second gives ring identifications for every untwisted admissible coefficient without prime-invertibility conditions. The third explicitly compares the specified internal functors and adjunctions with the section-ring functors via additive exact equivalences. Thus the operations and their module actions really are the specified ones. I read the relevant Stacks proetale.tex statements for 09AA, 09BM, 09BN, 09AG and 09AH and the proofs of 09BM and 09AH; these are carried by the existing excision/transport nodes, not directly used as uncited facts in the assembly. Both off-unit black-box uses remain declared in split_report.tool_uses.

Step 3 cites the new criterion whose statement explicitly retains every model and supplies the zero complement. I verified its parameters twice: first h=j,k=i,M=F,H=j_!F, then h=i,k=j,M=G,H=i_*G. The qcqs hypotheses, finite extended constructible strata and exact restriction isomorphisms are already established in steps 1–2, and the fixed old model witnesses were chosen in step 1. No prime invertibility, torsion, reducedness, field base, finiteness of a trivializing cover or scheme-theoretic complement assumption has been added. The two applications prove every constructibility and adapted-stratification clause; exactness comes from step 2. citations.json quotes the full literal statements, preventing either application from borrowing unadvertised facts from a cited proof.

I tested empty T, empty U, empty Z, identity immersions, an empty source partition, and empty strata retained in the finite partition. All partitions still cover their target with disjoint images; the stipulated extra empty stratum is allowed by def-constructible-stratification. I tested the zero coefficient ring, the zero scalar module and zero sheaf: the rank-zero presentation remains valid with no nontriviality assumption. For nonreduced Z the geometry retains the given scheme and the ringed counit applies as stated. Infinite trivializing covers and non-Noetherian cover members cause no issue: the geometry assumptions concern only T,U,Z, and no compactness assertion is made for cover members. The general criterion has no Noetherian hypothesis; it instead assumes the ambient strata are constructible, so it does not falsely infer constructibility of arbitrary locally closed subsets of a qcqs scheme.

B: both new nodes are self-contained statement-only tasks, with empty proof and proof_deps, precise sources, cited notions, searched ancestry and honest logged searches. C: all six parent citations were read and their hypotheses and exact conclusions checked; no off-unit theorem is smuggled into a definition citation. D: neither new node is an open/closed conclusion relabelled, neither contains the whole theorem, and the parent still performs the two parameter substitutions and the internal/ringed comparison. E: the small cases and all geometric/coefficient hypotheses are accounted for above. Each parent step is below 1000 characters, so there is no unreviewed long step hiding a further lemma. The two new nodes have no dependency on their parent, and the server dry-run will verify the whole DAG closure.

## Unfinished work

The two new nodes are intentionally unsplit, with no proof steps: other workers can take their independent arguments. No mathematical gap or statement dispute was found in this one-level repair. Server dry-run and delivery results are recorded after running the required tool.

## Retained original argument (verbatim)

The following is the entire live six-step proof before this repair. It is retained without shortening or blurring so every assigned argument is available to later workers.

### Former step 1

First the source schemes are qcqs. The open subscheme $U$ is Noetherian by [lem-weil-pbc-noetherian-open-subscheme-noetherian]. The closed immersion $i$ is of finite type by clause (a) of [lem-weil-pbc-closed-immersion-proper], so $Z$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. Both are quasi-compact by the meaning of Noetherian, and quasi-separated by [lem-weil-pbc-locally-noetherian-quasi-separated]. Thus [sk-def-sfb-constructible] supplies finite adapted stratifications $s_a:U_a\hookrightarrow U$ for a constructible module $F$ on $U$, and $t_b:Z_b\hookrightarrow Z$ for a constructible module $G$ on $Z$, with covers and finitely presented scalar modules witnessing every local model. Fix these witnesses; no change to their covers or scalar modules will be needed.

Uses: lem-weil-pbc-noetherian-open-subscheme-noetherian, lem-weil-pbc-closed-immersion-proper, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, sk-def-sfb-constructible

### Former step 2

The minimal-closed-subset property of [lem-weil-pbc-noetherian-scheme-closed-subsets-minimal] implies the descending-chain condition: a descending chain has a minimal member among its members, after which every member is equal. Thus $|T|$ is Noetherian. By [lem-sfb-noetherian-space-compact-subsets], every subset of $|T|$ is quasi-compact. In particular, $j$ is quasi-compact: over an affine open $W\subseteq T$, its inverse image is homeomorphic to $j(U)\cap W$ by [def-weil-open-immersion], hence is quasi-compact. By the immersion clause (e) of [lem-weil-pbc-proper-fp-permanence], each $j\circ s_a$ and $i\circ t_b$ is an immersion. The families $(j\circ s_a)_a$ together with $i$, and $(i\circ t_b)_b$ together with $j$, have pairwise disjoint images covering $T$. They are finite stratifications by [def-constructible-stratification]. Each image is locally closed, hence constructible in this Noetherian space by [def-weil-constructible-subset].

Uses: lem-weil-pbc-noetherian-scheme-closed-subsets-minimal, lem-sfb-noetherian-space-compact-subsets, def-weil-open-immersion, lem-weil-pbc-proper-fp-permanence, def-constructible-stratification, def-weil-constructible-subset

### Former step 3

Apply [lem-weil-pbc-proetale-ringed-open-closed] with ring sheaf $R_T$ (reconstructed as a section-ring sheaf) and the quasi-compact open complement verified in step 2. The Cartesian isomorphisms of [sk-prop-sfb-cartesian-coefficients] identify the inverse-image rings with $R_U$ and $R_Z$. The exact equivalences and operation/adjunction comparisons of [lem-sfb-internal-module-operations-transport] transfer the ringed-site assertions to the specified internal module functors, including their units and counits. We obtain $j^*j_!F\cong F$, $i^*j_!F=0$, $i^*i_*G\cong G$ and $j^*i_*G=0$, and exactness of $j_!$ and $i_*$. The comparisons preserve the module actions, so these are isomorphisms of modules over the identified coefficient rings.

Uses: lem-weil-pbc-proetale-ringed-open-closed, sk-prop-sfb-cartesian-coefficients, lem-sfb-internal-module-operations-transport

### Former step 4

For an old open-side stratum, the module-pullback composition isomorphism in [sk-def-sfb-module-pushforward-pullback] gives $(j\circ s_a)^*j_!F\cong s_a^*(j^*j_!F)\cong s_a^*F$, using step 3. On every original trivializing cover member $v:V\to U_a$, pull this isomorphism back once more. The fixed input model therefore gives $v^*(j\circ s_a)^*j_!F\cong R_V\otimes_{\Lambda(*)}P_{a,v}$. Thus exactly the old cover and the old finitely presented scalar module certify the model on that stratum [sk-def-sfb-constructible]. No extension functor has been applied to a presentation matrix.

Uses: sk-def-sfb-module-pushforward-pullback, sk-def-sfb-constructible

### Former step 5

On the additional closed stratum, $i^*j_!F=0$ by step 3. It has a finite constant model on the identity pro-etale cover, with scalar module $P=0$: the presentation $\Lambda(*)^0\to\Lambda(*)^0\to0\to0$ is finite, and $R_Z\otimes_{\Lambda(*)}0=0$ (equivalently its matrix presentation is the zero map between free modules of rank zero). Combining this model with step 4 and the first stratification of step 2 gives constructibility of $j_!F$ directly by [sk-def-sfb-constructible].

Uses: sk-def-sfb-constructible

### Former step 6

For an old closed-side stratum, composition of module pullbacks [sk-def-sfb-module-pushforward-pullback] and step 3 give $(i\circ t_b)^*i_*G\cong t_b^*(i^*i_*G)\cong t_b^*G$. On each original cover member $w:V\to Z_b$, this identifies the restricted extension with its original model $R_V\otimes_{\Lambda(*)}Q_{b,w}$. On the additional open stratum, $j^*i_*G=0$ by step 3; use its identity cover and the rank-zero scalar presentation from step 5. The second stratification of step 2 therefore makes $i_*G$ constructible by [sk-def-sfb-constructible], retaining every original local model and adding only the zero model on $U$. Together with the exactness proved in step 3 this proves all assertions.

Uses: sk-def-sfb-module-pushforward-pullback, sk-def-sfb-constructible
