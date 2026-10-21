# Stage-1 repair: sk-def-sfb-dc-setting

1. Files written:
   - `dag/nodes/sec-six-functors-basics/sk-def-sfb-dc-setting.json`: existing definition, statement unchanged, proof reassembled in five steps (2632 characters, formerly 3555).
   - `dag/nodes/sec-six-functors-basics/lem-sfb-compactification-middle-over-base.json`: new statement, status unsplit, no proof or proof dependencies, no Mathlib match.
   - `dag/units/sk-def-sfb-dc-setting.json`: only realized and realized_by filled.
   - `citations.json`: verbatim statement quotations for every step/cited-node pair.
2. Attachments: none. This is the explicitly assigned deliberate re-split, not an attachment or a stale re-push. Project interfaces were read, not compiled.
3. WANTED: none; all sources were available.
4. The returned split carried 3555 characters in six steps. The repair extracts the separate middle-scheme/base-compatibility argument; it does not alter the statement, coefficient category, existence route, or choice. The sandbox initially contained only launcher markers, no delivered JSON/report/searches, so the current read-only repository node is the retained returned baseline. All baseline proof, source citations, searches and metadata were retained in the item or reproduced below. No direct git, Lean writing, compiler, Lake or agent invocation was used.
5. Remaining work: proof of the new unsplit lemma is intentionally left to another stage-1 worker, as the return requires. Delivery validation is recorded below.

## Why this is a re-split

The new node isolates the argument of returned steps 4–5, not compactification existence or the whole setting. It starts with an arbitrary already supplied compactification over any qcqs scheme S; X need not be separated or finite type over S, and S need not be a field. It constructs the base structure, checks separatedness, local finite type, quasi-compactness and base equations together. The parent still performs its coefficient specialization, field-base and quasi-compactness verification, Nagata existence and fixed-choice identification. This extraction is the specific human-requested distribution of the existing argument, rather than an unsolicited new elementary node. No proof sketch is stored in the new statement-only node.

## Review by Q155

I read the current main-20261015 chapter, unit and item source, including the third statement paragraph (the current file has no separate proof paragraph). I compared the live item's six proof steps with that source and kept its statement byte-for-byte. The item's layer is internal modules over the pulled-back condensed ring object; it is not a fixed external module category or a completed coefficient theory. The prime/characteristic assumptions are retained even though the geometric argument does not need them. The final sentence only fixes the compactification used later; it asserts no adjoint or constructibility preservation for arbitrary condensed coefficients.

For the new lemma I read Stacks schemes.tex, Tag 01KU/lemma-separated-permanence (composition of separated maps), and morphisms.tex, Tag 01T3/lemma-composition-finite-type (both local finite type and finite type), as well as the definitions in schemes.tex Tag 01JX/definition-base-change and morphisms.tex Tag 01W1/definition-proper. The generalization needs a qcqs base for the exact quasi-compactness argument retained below. The uniqueness is forced by the condition that p be over S: any candidate must equal a_Y composed with p. The new lemma does not claim that a compactification exists without Nagata's hypotheses.

Parent step 1 uses the statements of sk-def-sfb-pulled-back-coefficients (commutative ring object Lambda_X), sk-def-sfb-module-objects (clause 3 defines precisely this module category) and sk-def-sfb-bounded-constructible (full subcategory, bounded cohomology, ordinary derived morphisms). I opened all three and checked that specialization to abelian sheaves imposes no new coefficient restriction. It is elementary definition substitution.

Parent step 2 uses lem-weil-pbc-affine-scheme-qcqs for Spec k, def-weil-finite-type-morphism for quasi-compact structure maps, and clause (2) of lem-weil-pbc-qcqs-morphism-permanence for quasi-compactness of Y. I read their statements: (2) requires both a quasi-compact morphism and a quasi-compact target, both available. Parent step 3 uses exactly the existence statement of lem-sfb-compactification-over-base: S is qcqs, X separated finite type, Y separated with quasi-compact structure morphism, and f is an S-map. Unpacking sk-def-nagata-sketch-data also supplies the quasi-compactness of the open immersion. These are non-elementary steps and remain so.

Parent step 4 uses the new lemma's stated conclusion, not an argument hidden in a definition: every hypothesis follows from step 2, the setting, and step 3. It yields the specific structure map, both over-base equations, and separated finite type of the middle. Parent step 5 uses def-sfb-compactification-over-field, whose statement fixes precisely a compactification under these geometric hypotheses and asserts no uniqueness or functoriality of choice; step 4 applies to that choice too. Every citation is backed by the verbatim quotation in citations.json. The new node has no proof steps and makes no unsupported citations in a proof.

I also opened the geometric statements used in the extracted argument: def-weil-proper-morphism includes separated and finite type; def-weil-finite-type-morphism is local finite type plus quasi-compact; lem-weil-pbc-proper-fp-permanence (e) states separated and local-finite-type composition; lem-weil-pbc-qcqs-morphism-permanence (1),(2) supply the two quasi-compactness implications. The over-base equation is exactly def-weil-scheme-over-base. Thus none of the extracted arguments is justified merely by a similarly named node.

I searched the whole DAG and blueprint for compactification, middle scheme, compactification over, structure morphism, and the shared Stacks tags. The pairs below distinguish all nonmerged existing nodes sharing the new node's source tags. I searched project Lean for the blueprint tag, compactificationOverField, HasCompactification and overObj/overI/overG. NagataCompactification.lean:255–283 and BoundedConstructible.lean:394–399 give existing interfaces for existence/choice; Compactification/Over.lean:109–150 gives partial interfaces for the middle object, factor maps, composition and individual properties. No single declaration states the new quantified unique-lift assertion including quasi-compactness of the middle scheme, so these are recorded as partial related interfaces, not a new sorry-free attachment claim. The human explicitly requires this already-stated item's re-split.

All seven searches in searches.jsonl were run with msearch.py for this extraction and read. LeanSearch and both LeanFinder phrasings returned properness, valuative criteria, isOver_iff and related facts, not the full compactification lift. Loogle returned proper-to-local-finite-type and separated composition; the source grep returned locallyOfFiniteType_comp at FiniteType.lean:68 and quasiCompact_comp at QuasiCompact.lean:69. I read those sources and Separated.lean:75: they are individual permanence properties already represented by existing DAG leaves, not the compactification construction/unique slice lift. The Mathlib grep for Compactification/overObj had no hits. This is why the new node is unsplit, not a purported Mathlib leaf. No failed service is recorded as absence.

Small cases checked: identity factorization gives the original Y structure; empty X allows a nonempty proper middle and does not require density; an empty middle forces empty X and gives the unique empty structure. Proper p need not be finite (e.g. projective-line middle), so the finite-morphism permanence node cannot replace this lemma. A general qcqs non-field base satisfies the same composition and quasi-compactness argument; no affine, Noetherian, perfection, or finite-field hypothesis is used. The new statement imposes no condition on X beyond its supplied S-map and compactification. No statement dispute was found.

I checked delivery-errors B–E against the files: the new statement introduces every object, uses single TeX escapes and genuine notion dependencies, has no proof sketch/steps and has complete blueprint provenance; the source labels/tags were read. Citations use statement conclusions with their hypotheses checked, no proof-internal object, route change or cycle. The parent still has distinct non-elementary existence and middle-scheme steps, so the whole conclusion has not moved into one node. No step exceeds 2000 characters. The original argument is preserved below for the worker who receives the new lemma.

## Preserved returned argument and work allocation

Steps 1–3 stay verbatim in the parent. Steps 4–5 move to the new lemma; the only change in old step 6 is the cross-reference from “steps 4–5” to the new parent step 4. The assembly step specializes the extracted lemma. The full returned proof is reproduced here, including every argument and citation, to prevent loss of work:

### Returned step 1

For the commutative condensed ring $\Lambda$, use [sk-def-sfb-pulled-back-coefficients] to read $\Lambda_X=p_X^*\Lambda$ as a commutative ring object in abelian sheaves on $X_{\mathrm{proét}}$. The category $\Mod_{\Lambda_X}$ is exactly the module-object category of [sk-def-sfb-module-objects]. Specialize the definition [sk-def-sfb-bounded-constructible] to this ring object and to abelian sheaves: its objects are the bounded complexes with constructible cohomology, and its morphisms are the ambient derived morphisms. The notation $D_{\mathrm{cons}}(X,\Lambda)$ abbreviates this full subcategory. This introduces notation, with no additional condition on $\Lambda$.

Uses: sk-def-sfb-pulled-back-coefficients, sk-def-sfb-module-objects, sk-def-sfb-bounded-constructible.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-dc-setting/_section.md, Statement, paragraphs 1–2 and the first display (the coefficient-category notation).

### Returned step 2

Put $S=\operatorname{Spec}k$ and write $a_X:X\to S$ and $a_Y:Y\to S$ for the structure morphisms. The affine-scheme lemma [lem-weil-pbc-affine-scheme-qcqs] makes $S$ quasi-compact and quasi-separated. By [def-weil-finite-type-morphism], finite type of $a_X$ and $a_Y$ includes quasi-compactness. Also $Y$ is quasi-compact as a scheme: apply clause (2) of [lem-weil-pbc-qcqs-morphism-permanence] to the quasi-compact map $a_Y$ and the quasi-compact base $S$. Thus $X$ is separated and of finite type over $S$, and $Y$ is separated and quasi-compact over $S$, as required in the next step.

Uses: lem-weil-pbc-affine-scheme-qcqs, def-weil-finite-type-morphism, lem-weil-pbc-qcqs-morphism-permanence.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-dc-setting/_section.md, Statement, paragraph 3, compactification-existence assertion; imported proof first sentence, with the quasi-compactness hypotheses made explicit.

### Returned step 3

Apply [lem-sfb-compactification-over-base] with this $S$, these structure morphisms, and the given $S$-morphism $f:X\to Y$. Every hypothesis was checked in step 2, so a compactification $c=(X\xrightarrow{i}Z\xrightarrow{p}Y)$ exists. Unpacking [sk-def-nagata-sketch-data], $i$ is a quasi-compact open immersion, $p$ is proper, and $p\circ i=f$. In particular the open-immersion clause in the statement holds with the stronger quasi-compactness included in the referenced definition.

Uses: lem-sfb-compactification-over-base, sk-def-nagata-sketch-data.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-dc-setting/_section.md, Statement, paragraph 3, first sentence; imported proof application of lem-sfb-compactification-over-base.

### Returned step 4

For any such $c$, give $Z$ the structure morphism $a_Z=a_Y\circ p$. By [def-weil-proper-morphism], properness of $p$ includes separatedness and finite type. By [def-weil-finite-type-morphism], $p$ and $a_Y$ are locally of finite type and quasi-compact. Apply clause (e) of [lem-weil-pbc-proper-fp-permanence] to $p$ and $a_Y$: their composite $a_Z$ is separated and locally of finite type. To check its quasi-compactness using only the cited statements, first apply clause (2) of [lem-weil-pbc-qcqs-morphism-permanence] to $p$ and the quasi-compact scheme $Y$ of step 2; this makes $Z$ quasi-compact. Its map $a_Z$ to the quasi-separated scheme $S$ is then quasi-compact by clause (1) of that same node. The definition of finite type now gives that $a_Z$ is of finite type. Consequently $Z$ belongs to the setting.

Uses: def-weil-proper-morphism, def-weil-finite-type-morphism, lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-qcqs-morphism-permanence.

Source: literature/stacks-project/schemes.tex, Tag 01KU (lemma-separated-permanence), composition clause; morphisms.tex Tags 01W1 (definition-proper) and 01T3 (lemma-composition-finite-type). Quasi-compactness is checked via the two clauses of the cited permanence node.

### Returned step 5

With $a_Z=a_Y\circ p$, the equality saying that $p$ is over $k$ is its definition. The equality saying that $i$ is over $k$ is $a_Z\circ i=(a_Y\circ p)\circ i=a_Y\circ(p\circ i)=a_Y\circ f=a_X$: the middle identity uses the compactification equality in [sk-def-nagata-sketch-data], and the last identity is precisely the hypothesis that $f$ is a $k$-morphism in [def-weil-scheme-over-base]. Thus both maps stay over the same field, without imposing any additional hypothesis.

Uses: sk-def-nagata-sketch-data, def-weil-scheme-over-base.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-dc-setting/_section.md, Statement, paragraph 3, sentence that i and p are k-morphisms; imported proof last sentence, with the structure morphism and equality written out.

### Returned step 6

The definition [def-sfb-compactification-over-field] fixes one compactification $c_f$ for precisely these hypotheses on $X$, $Y$ and $f$. Here $Y$ is quasi-compact over $k$ by step 2. Use that already specified choice for the displayed $c_f$; steps 4–5 apply to it as to every compactification. The last sentence of the item records which compactification subsequent shriek constructions use; it does not construct a shriek functor or assert preservation of constructibility or existence of an adjoint for every condensed ring.

Uses: def-sfb-compactification-over-field.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-dc-setting/_section.md, Statement, final display and the naming of the chosen compactification; imported proof reference to def-sfb-compactification-over-field.

For the new lemma over S, start the extracted step 4 by obtaining quasi-compactness of Y from the finite-type structure map and quasi-compact S using clause (2) of lem-weil-pbc-qcqs-morphism-permanence (exactly as old step 2 does). Then run old steps 4–5 with that general S. The equality a_Z=a_Y composed with p also proves uniqueness immediately, since any structure making p an S-map must satisfy that equality. This additional explicit uniqueness sentence does not replace or suppress the original quasi-compactness or associativity arguments.

## Not duplicates

lem-sfb-compactification-middle-over-base vs lem-sbc-composite-fibre-local-models: describes local rings and pointed fibres of a composite, not lifting a supplied compactification over its base.

lem-sfb-compactification-middle-over-base vs lem-fd-finite-ring-compact-support-finiteness: proves finite-coefficient compact-support constructibility and bounds over a field, not the relative middle-scheme construction over an arbitrary qcqs base.

lem-sfb-compactification-middle-over-base vs lem-sfb-finite-type-composition-base-change: states finite-type composition and base change only, not a compactification lift, separatedness, the over-base factorization or uniqueness.

lem-sfb-compactification-middle-over-base vs lem-weil-pbc-proper-fp-permanence: states generic permanence properties, but no construction of a middle S-scheme from a compactification or uniqueness of the lifted factorization.

lem-sfb-compactification-middle-over-base vs lem-weil-pbc-separated-base-change: proves separatedness after base change, not the lift and finiteness properties of a supplied compactification.

lem-sfb-compactification-middle-over-base vs lem-weil-pbc-finite-over-separated-finite-type: assumes a finite map; a proper compactification map need not be finite, and it does not construct or characterize the over-base factorization.

lem-sfb-compactification-middle-over-base vs lem-weil-pbc-qcqs-morphism-permanence: states qcqs implications for a given morphism, not the compactification lift, separated finite type or unique base structure.

lem-sfb-compactification-middle-over-base vs lem-weil-pbc-separated-lqf-base-change: concerns separated and locally quasi-finite base change, not compactification middle schemes.

lem-sfb-compactification-middle-over-base vs lem-weil-pbc-etale-splits-off-isolated-points-technical: constructs an etale neighbourhood and finite fibre pieces at isolated points, not the relative structure on an arbitrary compactification.

lem-sfb-compactification-middle-over-base vs lem-weil-pbc-qcqs-over-affine: deduces qcqs of a source over an affine target; the new result uses an arbitrary qcqs base and constructs the compactification middle structure and maps.

lem-sfb-compactification-middle-over-base vs lem-pod-separated-finite-type-base-change: is a base-change permanence statement, not the supplied compactification lift or its uniqueness.

lem-sfb-compactification-middle-over-base vs lem-sc-separated-over-affine-scheme-separated: deduces absolute separatedness from an affine base; it states no relative finite-type or compactification construction.

lem-sfb-compactification-middle-over-base vs lem-sfb-compactification-over-base: the existing result proves existence from hypotheses on X,Y,S; the new result starts with a supplied compactification, requires no finiteness or separatedness on X, and proves its unique lift and middle-scheme properties. Neither replaces the other.

lem-sfb-compactification-middle-over-base vs def-sfb-compactification-over-field: the existing definition fixes a choice over a field, while the new statement concerns every supplied compactification over a qcqs base and proves middle-scheme closure and the lift, without existence or choice.

lem-sfb-compactification-middle-over-base vs sk-def-sfb-dc-setting: the parent introduces a coefficient-derived-category setting, proves existence over a field and fixes choices; the extracted statement is just the relative lifting/closure argument over arbitrary qcqs S, with no coefficient, field, existence or choice conclusion.

## Validation

Required server dry run completed successfully: `deliver.py Q155 sk-def-sfb-dc-setting --no-push` exited 0 and printed `OK (not pushed) deliver/Q155/sk-def-sfb-dc-setting at a514d048078: preflight passed`. This validates the repaired split with the server delivery preflight. After recording this result, the final unchanged node set and updated report are dry-run again before the direct push. No compiler or local DAG/preflight check was run.
