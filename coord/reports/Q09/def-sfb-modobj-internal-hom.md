# Stage-1 split: def-sfb-modobj-internal-hom

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-modobj-internal-hom.json`: existing definition; split into ten explicit steps. No Mathlib match for the full statement.
- `citations.json`: 14 checked verbatim quotations, one for each node citation in the ten steps; its complete contents are also embedded below because the delivery tool does not copy this standalone file.
- `searches.jsonl`: twelve retained search-log entries, also embedded below for the same reason.
- `dag/chapters/sec-proetale-coefficients.json` and `dag/units/sk-prop-sfb-module-category.json`: exact copies of the current maintained route records, included in the sandbox for review. Their complete contents are embedded below; no maintained source or binding is changed.
- `report.md`: this report. `repair.py` is a sandbox-only reproducibility aid; it is not a delivered project file.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves are reused.

## Attachments

None. In particular, do not repeat the previously rejected attachment. I read `WeilConjectures/CategoryTheory/Monoidal/Mod/InternalHom.lean`, especially lines 38--152, 154--195, 225--284 and 310--376, and `Mod/Tensor.lean`, lines 139--151. The concrete construction `CategoryTheory.Mod.ihom'Adjunction` at line 351 supplies the adjunction for `P ↦ P ⊗_A M`. It does not itself assert the final monoidal closed structure with `M ⊗_A -` in the blueprint. Step 10 now explicitly uses the natural descended symmetry supplied by the existing DAG node. No source declaration is advertised as a complete proof of this item, and no declaration from upstream master is used as evidence of completion.

## WANTED

None. All sources used for this split were available locally.

## Problems found and corrected

The earlier sandbox was still a copy of the imported node, with two unjudged proof steps and no report. The imported argument omitted construction of the action on the equalizer, verification of the module axioms, the two separate linearity tests under currying, and the final switch between the two tensor orientations. These are written out. The statement and all its hypotheses are unchanged; there is no statement dispute.

The repaired sandbox item explicitly carries the required chapter and unit metadata. Source-derived chapter and unit records are prepared under `dag/chapters/` and `dag/units/`, with verbatim text from main-20261015. The chapter matches the shared base, and the unit record is present in current delivery worktrees. The item remains subject to maintainer-owned chapter/unit fields in delivery. Clause 3 of `sk-prop-sfb-module-category` is the closed-structure clause realized by this item.

The initial grep searches incorrectly named directories where Mathlib has files. They are explicitly recorded as inconclusive, and a corrected search of `CategoryTheory/Monoidal/Mod.lean` was run. No empty result from an incorrect path is used as evidence of absence. The exact queries and results are in `searches.jsonl` and the item's `mathlib_searches`.

## Unfinished work

The route metadata is repaired in this sandbox and the mathematical split is complete. The existing relative-tensor and symmetric-tensor nodes remain their own work items. No Lean was written, compiled or built, and nothing in the shared repository or launcher was edited. The delivery is left for the required fresh second reader after the dry run.

## Not duplicates

No new nodes. I searched the whole DAG by internal-hom, closed-monoidal and module-object concepts and by `homModObj`, `ihom'Adjunction`, `tensorRight_linear_iff`, and `coequalizes_iff`. I ran `tools/blueprint_refs.py search 'internal hom'`, `search 'module objects'`, `search 'adjoint preserves colimits'`, and `ancestor def-sfb-modobj-internal-hom`. The sheaf/presheaf and derived-Hom nodes refer to other categories or derived constructions; none states this general equalizer adjunction. The module-category unit has this as one clause of a larger conjunction, not a duplicate of this individual definition. The generic preservation theorem already exists as `lem-weil-pbc-left-adjoint-preserves-colimits`, so no new preservation node is created.

## Review by Q09

I read sections B--E of `coord/delivery-errors.md` in full and checked the split against the current blueprint node and the chapter/unit source above. The blueprint node fixes the equalizer, target action, and adjunction but its current Markdown has no separate proof section; the inherited three-paragraph proof is present in the DAG. The detailed expansion is therefore honestly marked agent-written. I also read the project's concrete internal-hom construction as a check on the two linearity conditions, rather than treating its docstring as a proof of all the blueprint's claims. For the only general categorical theorem invoked, I opened Stacks `categories.tex`, label `lemma-adjoint-exact`, Tag 0038, lines 3471--3507, and its proof. It states precisely preservation of existing colimits by a left adjoint. No SGA source is used.

For step 1 I opened all five cited node statements. `def-sp-grothendieck-abelian` supplies small colimits. `lem-weil-pbc-left-adjoint-preserves-colimits` supplies preservation for each adjunction and a small index category. The right-tensor adjunction is obtained explicitly by symmetry from the assumed left-tensor adjunction. `def-sfb-modobj-relative-tensor` supplies the specified coequalizer monoidal product, `def-sfb-modobj-symmetric-tensor` supplies its descended natural symmetry, and `lem-sfb-modobj-abelian` requires additive tensor and finite-colimit preservation of R tensor -, both verified here. No abelian theorem is being inferred from a mere definition node.

In step 2 the quoted `def-sp-abelian` includes kernels, so the equalizer is explicitly the kernel of p-q. Its defining relation (B) is obtained by applying the given adjunction bijection, whose naturality and injectivity are part of the adjunction definition. In step 3 `sk-def-sfb-module-objects` supplies the exact unit and associativity equations; the two uncurried composites are displayed, so no theorem about constructing an action on an internal hom is imported without a node.

For step 4 the only cited definition is again `sk-def-sfb-module-objects`, for associativity of the target action. The equalizer relation is step 2, not a fact allegedly contained in that node. The five-term computation specifies morphisms on R tensor R tensor M tensor E; commutativity of R is an actual hypothesis and is used exactly at the scalar interchange. This is tensor-slot notation for morphism composition, not a claim that objects of an arbitrary category have enough elements. Factoring the resulting map uses the equalizer's defining universal property. Step 5 checks the two module laws by cancelling its monic inclusion, and postcomposition and functoriality by uniqueness of the same lifts. The cited module-object definition actually states all the module-morphism equations used there.

For step 6 I reread `def-sfb-modobj-relative-tensor`, whose statement specifies both the parallel pair (including the right action through the symmetry) and the action through the first module. It supplies exactly the coequalizer used, not just existence of an unrelated tensor. The preservation leaf is cited again for R tensor pi: the finite parallel-pair index meets its smallness hypothesis. Uniqueness in a coequalizer proves it is epi. The module-morphism definition gives linearity, and the text explicitly proves its equivalence with linearity through L by precomposing with that epi. Balance plus this condition yields linearity through M by substituting equal expressions, without any flatness hypothesis.

Step 7 has no imported theorem: it displays the uncurried equation identifying the equalizer condition with linearity through M. Step 8 cites the same module-morphism definition for linearity in L, displays its uncurried composites, and uses monicity of i to reflect the linearity equation back to its lift. This reflection does not assume R tensor i is monic. Step 9 writes both inverse maps and the pre/postcomposition identities proving naturality. It uses inverse bijections and universal-property uniqueness, not a further tensor-Hom theorem. Step 10 cites `def-sfb-modobj-symmetric-tensor` for precisely its natural module isomorphism and precomposes with it; this repairs the orientation issue that invalidated the old attachment. Each of these is a short computation from the already constructed maps and definitions, so the steps are marked elementary; the non-elementary preservation result is explicitly cited in steps 1 and 6.

I tested the construction on the zero module M, the zero module N, the regular module R, and the tensor unit as coefficient monoid. For M=0, Hom(0,N) is the zero object in an additive closed category, since its maps from every L correspond to maps 0 to N; the tensor and hom-set formulas both give singletons. For N=0 the same applies by the terminal-object adjunction. For M=R the equalizer condition forces an R-linear map to be determined by its value at the unit, and the adjunction reduces to the unit constraint and the identity functor. For R the tensor unit, the two equalizer arrows agree by the action/unit laws and the adjunction is the given ambient adjunction. The zero monoid object in an additive category permits only zero modules by the unital action law, so the degenerate case causes no exception. No assertion uses flatness, faithful elements, exactness of tensor, an essentially small ambient category, or an unmentioned preservation of monomorphisms.

All node citations are backed by verbatim quotes in `citations.json`. No proposed child is elementary, a duplicate, a relocated clause, or an unsearched Mathlib fact, since no child is created. The elementary computations remain in the item where their argument can be reviewed. Mathlib searches used only the required `msearch.py` entry point, with two semantic phrasings read; the returned ordinary-module and representation categories do not specialize to an arbitrary Grothendieck abelian monoidal category. The generic hom-set currying identities used here are the natural bijections already assumed in the statement's adjunction, not an uncited independent existence theorem.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against blueprint node `def-sfb-modobj-internal-hom` in `literature/blueprint/main-20261015/.../def-sfb-modobj-internal-hom.md`; the closed symmetric monoidal, Grothendieck abelian, commutative monoid, equalizer, action, and adjunction clauses agree hypothesis by hypothesis.
- Step 1: checked against `def-sp-grothendieck-abelian`, `lem-weil-pbc-left-adjoint-preserves-colimits`, `def-sfb-modobj-relative-tensor`, `def-sfb-modobj-symmetric-tensor`, and `lem-sfb-modobj-abelian`; all cited statements supply the colimits, preservation, tensor structures, and abelian conclusion used.
- Step 2: checked against `def-sp-abelian`; kernels give the equalizer and the displayed adjunction calculation gives relation (B), with the closed adjunction already part of the item hypotheses.
- Step 3: checked against `sk-def-sfb-module-objects`; the transpose construction and the two uncurried module-law calculations use exactly the stated unit and associativity equations.
- Step 4: checked against `sk-def-sfb-module-objects` and step 2; the slot calculation uses target associativity, commutativity of the scalar monoid, and the equalizer universal property to define the action.
- Step 5: checked against `sk-def-sfb-module-objects` and the equalizer action from steps 2--4; monicity and uniqueness establish module laws, functoriality, and target linearity.
- Step 6: checked against `def-sfb-modobj-relative-tensor`, `lem-weil-pbc-left-adjoint-preserves-colimits`, and `sk-def-sfb-module-objects`; the coequalizer gives balance, tensor preservation gives the epimorphism used for descent, and the module equations give both linearity conditions.
- Step 7: checked directly from the two equalizer arrows in the item statement; the displayed uncurrying identifies the equalizer condition with linearity through $M$ and is an elementary rearrangement.
- Step 8: checked against `sk-def-sfb-module-objects` and the action definition in step 3; the transpose calculation identifies linearity through $L$, and monicity of the equalizer inclusion reflects it.
- Step 9: checked directly from the adjunction bijection and the equalizer/coequalizer universal properties; the explicit forward and reverse maps are inverse and their naturality follows by pre/postcomposition.
- Step 10: checked against `def-sfb-modobj-symmetric-tensor`; its descended natural symmetry supplies the orientation change from $L\otimes_{\mathcal R}M$ to $M\otimes_{\mathcal R}L$ and completes the adjunction.
- New nodes: none; the whole DAG was searched for internal-hom, module-object, equalizer, and closed-monoidal statements, and Mathlib searches are recorded in `searches.jsonl`; no child node is needed.

Changes made during this reading: removed the uncited Stacks Tag `0038` parenthetical from step 1 (the existing preservation node is the citation and the tag was not carried by a cited statement), then added this source-by-source second-reading record. No statement, hypothesis, dependency, or construction was otherwise changed.

## Repair of return 2026-10-16, head 59f289837e

This repair supersedes the earlier missing-unit and lock-timeout reports. I compared the retained ten-step split with the current main item by reading their JSON, without running git in the shared repository. The current item remains imported and has the same statement; the retained split changes only its permitted split fields. The return quotes that the mathematics and all ten proof steps were checked; I preserved that argument and reopened all seven direct cited statements against the current base.

1. **Chapter/unit metadata and records.** The item's `chapter` is `sec-proetale-coefficients` and its `unit` is `sk-prop-sfb-module-category`, in both the sandbox and current base. Both maintained records now exist on the base, including the prerequisite unit `sk-def-sfb-module-objects`. The copied records in this sandbox are refreshed to exactly those maintained records. In particular the stale sandbox unit with `steps: []` and `realized.steps: []` was replaced by the actual six-step record, retaining all six empty realization slots and `realized_by: null`. I did not remove its inherited proof paragraphs because the main-20261015 Markdown has no separate proof section. I read both the chapter and unit Markdown and the maintained unit's six steps. The fixed chapter route is preserved.

   The unit's fourth proof paragraph (Part 3) names `[def-sfb-modobj-internal-hom]` explicitly for closedness. This split carries that component: step 1 applies the earlier abelian/tensor clauses, steps 2--5 construct the equalizer action, and steps 6--10 establish the tensor-Hom adjunction. It uses only this unit, its declared module-object prerequisite, and definition/Mathlib tools. It neither asserts nor substitutes for the Grothendieck and flat-resolution components of Part 3 or the other parts of the unit. The item is not the unit's key node; therefore its worker does not fill a binding asserting realization of the whole unit or overwrite any maintained binding. The full records and their actual current bindings are reproduced below so review does not depend on missing packet files.

2. **Evidence files missing from the old packet.** `citations.json` and `searches.jsonl` exist as validation inputs in the sandbox. The delivery tool reads them but does not copy them as standalone committed files. Their complete contents are therefore embedded below in this report, which the tool does commit. I make no claim that the packet contains separate evidence files. All 14 `(step,node)` citation pairs have exactly one verbatim quotation from the current cited statements, with no missing or extra pair. The nine retained search log records are genuine earlier `msearch.py` results; none has been invented or represented as rerun by this repair. No new mathematical node is created, so no new-node search is needed.

I rechecked B--E on the unchanged mathematics: the module and module-morphism equations are in the cited module-object definition; the relative-tensor statement specifies the coequalizer and target action used in step 6; the symmetry statement gives exactly the orientation-changing module isomorphism of step 10. The two ambient-category definition tools give kernels and colimits. The preservation theorem applies only to small diagrams, here finite parallel pairs. Steps 2--10 contain the actual transpose, linearity, module-law and universal-property calculations; no clause is relocated into a new node. Commutativity is used in step 4 and is assumed in the item. No flatness or monicity preservation is assumed. The zero-module, regular-module, unit-coefficient and zero-coefficient checks in Review by Q09 remain valid. No statement correction is required and no forbidden SGA route is used.

The generic instruction about repairing a definition with `@[no_expose]` does not describe a stage-1 file or compiler diagnostic here. The retained failure was a delivery-lock wait. This packet contains no Lean file, and the explicit stage-1 restriction prohibits Lean writing and compilation. The prescribed delivery command alone packages a fresh-base worktree and runs the source-only stage-1 preflight; it is run without a 60-second external cutoff. Nothing is pushed by this worker.

## Citation evidence (complete citations.json)

```json
[
 {
  "step": 1,
  "node": "def-sp-grothendieck-abelian",
  "quote": "A Grothendieck abelian category is an *abelian category* [def-sp-abelian]\nwhich has small colimits, a generator, and exact filtered colimits."
 },
 {
  "step": 1,
  "node": "lem-weil-pbc-left-adjoint-preserves-colimits",
  "quote": "Let $L:\\mathcal C\\to\\mathcal D$ and $R:\\mathcal D\\to\\mathcal C$ be functors with an adjunction $L\\dashv R$, i.e. bijections $\\operatorname{Hom}_{\\mathcal D}(LX,Y)\\cong\\operatorname{Hom}_{\\mathcal C}(X,RY)$ natural in $X\\in\\mathcal C$ and $Y\\in\\mathcal D$. Let $I$ be a small category and $M:I\\to\\mathcal C$ a diagram having a colimit $(\\varinjlim_IM,(\\iota_i)_i)$ in $\\mathcal C$ [def-weil-pbc-category-colimit]. Then $(L(\\varinjlim_IM),(L\\iota_i)_i)$ is a colimit of $L\\circ M$ in $\\mathcal D$. In particular, when $L\\circ M$ has a chosen colimit, the canonical morphism $\\varinjlim_I(L\\circ M)\\to L(\\varinjlim_IM)$ induced by the $L\\iota_i$ is an isomorphism."
 },
 {
  "step": 1,
  "node": "def-sfb-modobj-relative-tensor",
  "quote": "Let $\\mathcal C$ be a braided monoidal category with braiding $\\beta$ and with\ncoequalizers, such that $X\\otimes-$ and $-\\otimes X$ preserve colimits for every $X$. Let\n$\\mathcal R$ be a commutative monoid object. For $\\mathcal R$-module objects $M$ and $N$,\nthe *relative tensor product* $M\\otimes_{\\mathcal R}N$ is the tensor product over\n$\\mathcal R$ ([lem-sfb-symmetric-bimod-tensor]) of the symmetric bimodules attached to $M$\nand $N$ ([lem-sfb-modobj-symmetric-bimodules]), viewed as a left module:\n$$\nM\\otimes_{\\mathcal R}N=\\operatorname{coeq}\\Bigl(M\\otimes\\mathcal R\\otimes N\n\\rightrightarrows M\\otimes N\\Bigr)\n$$\nof $(\\gamma_M\\beta_{M,\\mathcal R})\\otimes N$ and $(M\\otimes\\gamma_N)\\alpha_{M,\\mathcal R,N}$,\nwith $\\mathcal R$ acting through $M$. With unit the regular module $\\mathcal R$, and with\nthe associator and unitors induced from those of bimodules, this is a monoidal structure\non $\\Mod_{\\mathcal R}(\\mathcal C)$."
 },
 {
  "step": 1,
  "node": "def-sfb-modobj-symmetric-tensor",
  "quote": "Let $\\mathcal C$ be a symmetric monoidal category with coequalizers such that $X\\otimes-$\nand $-\\otimes X$ preserve colimits for every $X$, and let $\\mathcal R$ be a commutative\nmonoid object. The braiding $\\beta_{M,N}\\colon M\\otimes N\\to N\\otimes M$ of $\\mathcal C$\ndescends to an isomorphism of $\\mathcal R$-module objects\n$$\nM\\otimes_{\\mathcal R}N\\xrightarrow{\\ \\sim\\ }N\\otimes_{\\mathcal R}M\n$$\nfor the relative tensor product of [def-sfb-modobj-relative-tensor]. These isomorphisms\nmake $(\\Mod_{\\mathcal R}(\\mathcal C),\\otimes_{\\mathcal R},\\mathcal R)$ a symmetric\nmonoidal category."
 },
 {
  "step": 1,
  "node": "lem-sfb-modobj-abelian",
  "quote": "Let $\\mathcal C$ be an abelian monoidal category whose tensor product is additive in each\nvariable. Let $\\mathcal R$ be a monoid object of $\\mathcal C$ such that $\\mathcal R\\otimes-$\npreserves finite colimits. Then $\\Mod_{\\mathcal R}(\\mathcal C)$\n([sk-def-sfb-module-objects]) is an abelian category."
 },
 {
  "step": 2,
  "node": "def-sp-abelian",
  "quote": "An *abelian category* is a preadditive category with a zero object and finite\nbiproducts, which admits kernels and cokernels, in which every monomorphism\nis a kernel and every epimorphism is a cokernel."
 },
 {
  "step": 3,
  "node": "sk-def-sfb-module-objects",
  "quote": "Let $(\\mathcal C,\\otimes,\\mathbf 1)$ be a monoidal category with associator $\\alpha$ and\nleft unitor $\\lambda$. Let $\\mathcal R$ be a monoid object of $\\mathcal C$, with\nmultiplication $\\mu\\colon\\mathcal R\\otimes\\mathcal R\\to\\mathcal R$ and unit\n$\\eta\\colon\\mathbf 1\\to\\mathcal R$. When $\\mathcal C$ is a category of abelian sheaves with\nits tensor product, these are the ring objects of [sk-def-sfb-ring-object].\n\n1. A *(left) $\\mathcal R$-module object* is an object $M$ of $\\mathcal C$ with an\n   *action* $\\gamma_M\\colon\\mathcal R\\otimes M\\to M$ that is unital and associative:\n   $$\n   \\gamma_M\\circ(\\eta\\otimes M)=\\lambda_M,\\qquad\n   \\gamma_M\\circ(\\mu\\otimes M)=\\gamma_M\\circ(\\mathcal R\\otimes\\gamma_M)\\circ\\alpha_{\\mathcal R,\\mathcal R,M}.\n   $$\n2. A *morphism of $\\mathcal R$-module objects* $f\\colon M\\to N$ is a morphism of\n   $\\mathcal C$ with $f\\circ\\gamma_M=\\gamma_N\\circ(\\mathcal R\\otimes f)$. With the\n   composition of $\\mathcal C$, the $\\mathcal R$-module objects form a category\n   $\\Mod_{\\mathcal R}(\\mathcal C)$. It has a forgetful functor\n   $\\Mod_{\\mathcal R}(\\mathcal C)\\to\\mathcal C$, $(M,\\gamma_M)\\mapsto M$. The *regular\n   module* is $\\mathcal R$ itself with action $\\mu$.\n3. Let $X$ be a scheme with small pro-étale site $X_{\\mathrm{proét}}$\n   ([def-weil-pbc-proetale-site]). Give $\\Sh(X_{\\mathrm{proét}},\\Ab)$ the tensor product of\n   [sk-def-sfb-sheaf-tensor]. Let $\\Lambda$ be a condensed ring and let\n   $\\Lambda_X=p_X^*\\Lambda$ be its pullback, a ring object of $\\Sh(X_{\\mathrm{proét}},\\Ab)$\n   ([sk-def-sfb-pulled-back-coefficients]). The category of *sheaves of\n   $\\Lambda_X$-modules* is\n   $$\n   \\Mod_{\\Lambda_X}:=\\Mod_{\\Lambda_X}\\bigl(\\Sh(X_{\\mathrm{proét}},\\Ab)\\bigr).\n   $$"
 },
 {
  "step": 4,
  "node": "sk-def-sfb-module-objects",
  "quote": "Let $(\\mathcal C,\\otimes,\\mathbf 1)$ be a monoidal category with associator $\\alpha$ and\nleft unitor $\\lambda$. Let $\\mathcal R$ be a monoid object of $\\mathcal C$, with\nmultiplication $\\mu\\colon\\mathcal R\\otimes\\mathcal R\\to\\mathcal R$ and unit\n$\\eta\\colon\\mathbf 1\\to\\mathcal R$. When $\\mathcal C$ is a category of abelian sheaves with\nits tensor product, these are the ring objects of [sk-def-sfb-ring-object].\n\n1. A *(left) $\\mathcal R$-module object* is an object $M$ of $\\mathcal C$ with an\n   *action* $\\gamma_M\\colon\\mathcal R\\otimes M\\to M$ that is unital and associative:\n   $$\n   \\gamma_M\\circ(\\eta\\otimes M)=\\lambda_M,\\qquad\n   \\gamma_M\\circ(\\mu\\otimes M)=\\gamma_M\\circ(\\mathcal R\\otimes\\gamma_M)\\circ\\alpha_{\\mathcal R,\\mathcal R,M}.\n   $$\n2. A *morphism of $\\mathcal R$-module objects* $f\\colon M\\to N$ is a morphism of\n   $\\mathcal C$ with $f\\circ\\gamma_M=\\gamma_N\\circ(\\mathcal R\\otimes f)$. With the\n   composition of $\\mathcal C$, the $\\mathcal R$-module objects form a category\n   $\\Mod_{\\mathcal R}(\\mathcal C)$. It has a forgetful functor\n   $\\Mod_{\\mathcal R}(\\mathcal C)\\to\\mathcal C$, $(M,\\gamma_M)\\mapsto M$. The *regular\n   module* is $\\mathcal R$ itself with action $\\mu$.\n3. Let $X$ be a scheme with small pro-étale site $X_{\\mathrm{proét}}$\n   ([def-weil-pbc-proetale-site]). Give $\\Sh(X_{\\mathrm{proét}},\\Ab)$ the tensor product of\n   [sk-def-sfb-sheaf-tensor]. Let $\\Lambda$ be a condensed ring and let\n   $\\Lambda_X=p_X^*\\Lambda$ be its pullback, a ring object of $\\Sh(X_{\\mathrm{proét}},\\Ab)$\n   ([sk-def-sfb-pulled-back-coefficients]). The category of *sheaves of\n   $\\Lambda_X$-modules* is\n   $$\n   \\Mod_{\\Lambda_X}:=\\Mod_{\\Lambda_X}\\bigl(\\Sh(X_{\\mathrm{proét}},\\Ab)\\bigr).\n   $$"
 },
 {
  "step": 5,
  "node": "sk-def-sfb-module-objects",
  "quote": "Let $(\\mathcal C,\\otimes,\\mathbf 1)$ be a monoidal category with associator $\\alpha$ and\nleft unitor $\\lambda$. Let $\\mathcal R$ be a monoid object of $\\mathcal C$, with\nmultiplication $\\mu\\colon\\mathcal R\\otimes\\mathcal R\\to\\mathcal R$ and unit\n$\\eta\\colon\\mathbf 1\\to\\mathcal R$. When $\\mathcal C$ is a category of abelian sheaves with\nits tensor product, these are the ring objects of [sk-def-sfb-ring-object].\n\n1. A *(left) $\\mathcal R$-module object* is an object $M$ of $\\mathcal C$ with an\n   *action* $\\gamma_M\\colon\\mathcal R\\otimes M\\to M$ that is unital and associative:\n   $$\n   \\gamma_M\\circ(\\eta\\otimes M)=\\lambda_M,\\qquad\n   \\gamma_M\\circ(\\mu\\otimes M)=\\gamma_M\\circ(\\mathcal R\\otimes\\gamma_M)\\circ\\alpha_{\\mathcal R,\\mathcal R,M}.\n   $$\n2. A *morphism of $\\mathcal R$-module objects* $f\\colon M\\to N$ is a morphism of\n   $\\mathcal C$ with $f\\circ\\gamma_M=\\gamma_N\\circ(\\mathcal R\\otimes f)$. With the\n   composition of $\\mathcal C$, the $\\mathcal R$-module objects form a category\n   $\\Mod_{\\mathcal R}(\\mathcal C)$. It has a forgetful functor\n   $\\Mod_{\\mathcal R}(\\mathcal C)\\to\\mathcal C$, $(M,\\gamma_M)\\mapsto M$. The *regular\n   module* is $\\mathcal R$ itself with action $\\mu$.\n3. Let $X$ be a scheme with small pro-étale site $X_{\\mathrm{proét}}$\n   ([def-weil-pbc-proetale-site]). Give $\\Sh(X_{\\mathrm{proét}},\\Ab)$ the tensor product of\n   [sk-def-sfb-sheaf-tensor]. Let $\\Lambda$ be a condensed ring and let\n   $\\Lambda_X=p_X^*\\Lambda$ be its pullback, a ring object of $\\Sh(X_{\\mathrm{proét}},\\Ab)$\n   ([sk-def-sfb-pulled-back-coefficients]). The category of *sheaves of\n   $\\Lambda_X$-modules* is\n   $$\n   \\Mod_{\\Lambda_X}:=\\Mod_{\\Lambda_X}\\bigl(\\Sh(X_{\\mathrm{proét}},\\Ab)\\bigr).\n   $$"
 },
 {
  "step": 6,
  "node": "def-sfb-modobj-relative-tensor",
  "quote": "Let $\\mathcal C$ be a braided monoidal category with braiding $\\beta$ and with\ncoequalizers, such that $X\\otimes-$ and $-\\otimes X$ preserve colimits for every $X$. Let\n$\\mathcal R$ be a commutative monoid object. For $\\mathcal R$-module objects $M$ and $N$,\nthe *relative tensor product* $M\\otimes_{\\mathcal R}N$ is the tensor product over\n$\\mathcal R$ ([lem-sfb-symmetric-bimod-tensor]) of the symmetric bimodules attached to $M$\nand $N$ ([lem-sfb-modobj-symmetric-bimodules]), viewed as a left module:\n$$\nM\\otimes_{\\mathcal R}N=\\operatorname{coeq}\\Bigl(M\\otimes\\mathcal R\\otimes N\n\\rightrightarrows M\\otimes N\\Bigr)\n$$\nof $(\\gamma_M\\beta_{M,\\mathcal R})\\otimes N$ and $(M\\otimes\\gamma_N)\\alpha_{M,\\mathcal R,N}$,\nwith $\\mathcal R$ acting through $M$. With unit the regular module $\\mathcal R$, and with\nthe associator and unitors induced from those of bimodules, this is a monoidal structure\non $\\Mod_{\\mathcal R}(\\mathcal C)$."
 },
 {
  "step": 6,
  "node": "lem-weil-pbc-left-adjoint-preserves-colimits",
  "quote": "Let $L:\\mathcal C\\to\\mathcal D$ and $R:\\mathcal D\\to\\mathcal C$ be functors with an adjunction $L\\dashv R$, i.e. bijections $\\operatorname{Hom}_{\\mathcal D}(LX,Y)\\cong\\operatorname{Hom}_{\\mathcal C}(X,RY)$ natural in $X\\in\\mathcal C$ and $Y\\in\\mathcal D$. Let $I$ be a small category and $M:I\\to\\mathcal C$ a diagram having a colimit $(\\varinjlim_IM,(\\iota_i)_i)$ in $\\mathcal C$ [def-weil-pbc-category-colimit]. Then $(L(\\varinjlim_IM),(L\\iota_i)_i)$ is a colimit of $L\\circ M$ in $\\mathcal D$. In particular, when $L\\circ M$ has a chosen colimit, the canonical morphism $\\varinjlim_I(L\\circ M)\\to L(\\varinjlim_IM)$ induced by the $L\\iota_i$ is an isomorphism."
 },
 {
  "step": 6,
  "node": "sk-def-sfb-module-objects",
  "quote": "Let $(\\mathcal C,\\otimes,\\mathbf 1)$ be a monoidal category with associator $\\alpha$ and\nleft unitor $\\lambda$. Let $\\mathcal R$ be a monoid object of $\\mathcal C$, with\nmultiplication $\\mu\\colon\\mathcal R\\otimes\\mathcal R\\to\\mathcal R$ and unit\n$\\eta\\colon\\mathbf 1\\to\\mathcal R$. When $\\mathcal C$ is a category of abelian sheaves with\nits tensor product, these are the ring objects of [sk-def-sfb-ring-object].\n\n1. A *(left) $\\mathcal R$-module object* is an object $M$ of $\\mathcal C$ with an\n   *action* $\\gamma_M\\colon\\mathcal R\\otimes M\\to M$ that is unital and associative:\n   $$\n   \\gamma_M\\circ(\\eta\\otimes M)=\\lambda_M,\\qquad\n   \\gamma_M\\circ(\\mu\\otimes M)=\\gamma_M\\circ(\\mathcal R\\otimes\\gamma_M)\\circ\\alpha_{\\mathcal R,\\mathcal R,M}.\n   $$\n2. A *morphism of $\\mathcal R$-module objects* $f\\colon M\\to N$ is a morphism of\n   $\\mathcal C$ with $f\\circ\\gamma_M=\\gamma_N\\circ(\\mathcal R\\otimes f)$. With the\n   composition of $\\mathcal C$, the $\\mathcal R$-module objects form a category\n   $\\Mod_{\\mathcal R}(\\mathcal C)$. It has a forgetful functor\n   $\\Mod_{\\mathcal R}(\\mathcal C)\\to\\mathcal C$, $(M,\\gamma_M)\\mapsto M$. The *regular\n   module* is $\\mathcal R$ itself with action $\\mu$.\n3. Let $X$ be a scheme with small pro-étale site $X_{\\mathrm{proét}}$\n   ([def-weil-pbc-proetale-site]). Give $\\Sh(X_{\\mathrm{proét}},\\Ab)$ the tensor product of\n   [sk-def-sfb-sheaf-tensor]. Let $\\Lambda$ be a condensed ring and let\n   $\\Lambda_X=p_X^*\\Lambda$ be its pullback, a ring object of $\\Sh(X_{\\mathrm{proét}},\\Ab)$\n   ([sk-def-sfb-pulled-back-coefficients]). The category of *sheaves of\n   $\\Lambda_X$-modules* is\n   $$\n   \\Mod_{\\Lambda_X}:=\\Mod_{\\Lambda_X}\\bigl(\\Sh(X_{\\mathrm{proét}},\\Ab)\\bigr).\n   $$"
 },
 {
  "step": 8,
  "node": "sk-def-sfb-module-objects",
  "quote": "Let $(\\mathcal C,\\otimes,\\mathbf 1)$ be a monoidal category with associator $\\alpha$ and\nleft unitor $\\lambda$. Let $\\mathcal R$ be a monoid object of $\\mathcal C$, with\nmultiplication $\\mu\\colon\\mathcal R\\otimes\\mathcal R\\to\\mathcal R$ and unit\n$\\eta\\colon\\mathbf 1\\to\\mathcal R$. When $\\mathcal C$ is a category of abelian sheaves with\nits tensor product, these are the ring objects of [sk-def-sfb-ring-object].\n\n1. A *(left) $\\mathcal R$-module object* is an object $M$ of $\\mathcal C$ with an\n   *action* $\\gamma_M\\colon\\mathcal R\\otimes M\\to M$ that is unital and associative:\n   $$\n   \\gamma_M\\circ(\\eta\\otimes M)=\\lambda_M,\\qquad\n   \\gamma_M\\circ(\\mu\\otimes M)=\\gamma_M\\circ(\\mathcal R\\otimes\\gamma_M)\\circ\\alpha_{\\mathcal R,\\mathcal R,M}.\n   $$\n2. A *morphism of $\\mathcal R$-module objects* $f\\colon M\\to N$ is a morphism of\n   $\\mathcal C$ with $f\\circ\\gamma_M=\\gamma_N\\circ(\\mathcal R\\otimes f)$. With the\n   composition of $\\mathcal C$, the $\\mathcal R$-module objects form a category\n   $\\Mod_{\\mathcal R}(\\mathcal C)$. It has a forgetful functor\n   $\\Mod_{\\mathcal R}(\\mathcal C)\\to\\mathcal C$, $(M,\\gamma_M)\\mapsto M$. The *regular\n   module* is $\\mathcal R$ itself with action $\\mu$.\n3. Let $X$ be a scheme with small pro-étale site $X_{\\mathrm{proét}}$\n   ([def-weil-pbc-proetale-site]). Give $\\Sh(X_{\\mathrm{proét}},\\Ab)$ the tensor product of\n   [sk-def-sfb-sheaf-tensor]. Let $\\Lambda$ be a condensed ring and let\n   $\\Lambda_X=p_X^*\\Lambda$ be its pullback, a ring object of $\\Sh(X_{\\mathrm{proét}},\\Ab)$\n   ([sk-def-sfb-pulled-back-coefficients]). The category of *sheaves of\n   $\\Lambda_X$-modules* is\n   $$\n   \\Mod_{\\Lambda_X}:=\\Mod_{\\Lambda_X}\\bigl(\\Sh(X_{\\mathrm{proét}},\\Ab)\\bigr).\n   $$"
 },
 {
  "step": 10,
  "node": "def-sfb-modobj-symmetric-tensor",
  "quote": "Let $\\mathcal C$ be a symmetric monoidal category with coequalizers such that $X\\otimes-$\nand $-\\otimes X$ preserve colimits for every $X$, and let $\\mathcal R$ be a commutative\nmonoid object. The braiding $\\beta_{M,N}\\colon M\\otimes N\\to N\\otimes M$ of $\\mathcal C$\ndescends to an isomorphism of $\\mathcal R$-module objects\n$$\nM\\otimes_{\\mathcal R}N\\xrightarrow{\\ \\sim\\ }N\\otimes_{\\mathcal R}M\n$$\nfor the relative tensor product of [def-sfb-modobj-relative-tensor]. These isomorphisms\nmake $(\\Mod_{\\mathcal R}(\\mathcal C),\\otimes_{\\mathcal R},\\mathcal R)$ a symmetric\nmonoidal category."
 }
]
```

## Search evidence (complete searches.jsonl)

```jsonl
{"t": "2026-10-16T11:50:19Z", "tool": "grep", "query": "monoidalClosed|ihomAdjunction|ihomObj", "sub": "CategoryTheory/Monoidal/Mod", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-16T11:50:20Z", "tool": "leansearch", "query": "The category of modules over a commutative monoid object is monoidal closed with internal hom equalizer", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["CategoryTheory.ihom", "CategoryTheory.MonoidalClosed.closed", "CategoryTheory.MonoidalClosed", "Rep.instMonoidalClosed", "CategoryTheory.MonoidalClosed.ofEquiv", "ModuleCat.instMonoidalClosed", "CategoryTheory.Functor.functorCategoryMonoidalClosed", "ModuleCat.monoidalClosed_curry"], "digest": "6b91c792605e7086"}
{"t": "2026-10-16T11:50:20Z", "tool": "loogle", "query": "\"Mod\", \"ihom\"", "sub": "", "ok": true, "n_hits": 4, "note": "", "top": ["ModuleCat.ihom_map_apply", "ModuleCat.ihom_coev_app", "ModuleCat.ihom_ev_app", "FGModuleCat.ihom_obj"], "digest": "7bcd0bdb752b38d8"}
{"t": "2026-10-16T11:50:22Z", "tool": "leanfinder", "query": "The category of module objects over a commutative monoid in a symmetric monoidal closed category is monoidal closed with internal hom given by an equalizer", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["ModuleCat.instMonoidalClosed", "LightCondensed.instMonoidalClosedLightCondMod", "FGModuleCat.instIsMonoidalClosedModuleCatIsFG", "ModuleCat.monoidalClosed_uncurry", "ModuleCat.monoidalClosed_curry", "ModuleCat.monoidalClosed_pre_app", "ModuleCat.monoidalClosedHomEquiv", "ModuleCat.ihom_ev_app"], "digest": "f359073ee8045b2e"}
{"t": "2026-10-16T11:50:32Z", "tool": "grep", "query": "internalHom|ihom|Closed|equalizer", "sub": "CategoryTheory/Monoidal/Mod_", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-16T11:50:36Z", "tool": "leanfinder", "query": "Internal Hom for modules over a monoid object via equalizer of two currying maps", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["ModuleCat.instMonoidalClosed", "ModuleCat.ihom_ev_app", "FGModuleCat.ihom_obj", "Rep.ihom_obj_V_isModule", "ModuleCat.ihom_map_apply", "ModuleCat.monoidalClosed_uncurry", "ModuleCat.monoidalClosed_curry", "Rep.ihom_obj_V_carrier"], "digest": "36461ed07a9a9d4d"}
{"t": "2026-10-16T11:50:57Z", "tool": "grep", "query": "ihom|closed|equalizer", "sub": "CategoryTheory/Monoidal/Mon_", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-16T11:50:57Z", "tool": "loogle", "query": "CategoryTheory.Mod_", "sub": "", "ok": true, "n_hits": 1, "note": "", "top": ["CategoryTheory.Mod_"], "digest": "50c1ea273c6f4a14"}
{"t": "2026-10-16T11:51:56Z", "tool": "grep", "query": "ihom|closed|equalizer", "sub": "CategoryTheory/Monoidal/Mod.lean", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-16T14:35:50Z", "tool": "grep", "query": "MonoidalClosed|Closed|equalizer|ihom", "sub": "--sub", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
{"t": "2026-10-16T14:35:51Z", "tool": "leanfinder", "query": "A commutative algebra object in a cocomplete symmetric closed tensor category has a closed category of left modules", "sub": "", "ok": true, "n_hits": 8, "note": "", "top": ["ModuleCat.instMonoidalClosed", "LightCondensed.instMonoidalClosedLightCondMod", "FGModuleCat.instIsMonoidalClosedModuleCatIsFG", "CategoryTheory.IsGrothendieckAbelian.instIsLeftAdjointModuleCatMulOppositeEndTensorObj", "CategoryTheory.IsGrothendieckAbelian.tensorObj", "ModuleCat.instMonoidalLinear", "LightCondensed.instMonoidalCategoryLightCondMod", "ModuleCat.monoidalCategory"], "digest": "49c91960fe482ec6"}
{"t": "2026-10-16T14:36:18Z", "tool": "grep", "query": "MonoidalClosed|Closed|equalizer|ihom", "sub": "CategoryTheory/Monoidal/Mod.lean", "ok": true, "n_hits": 0, "note": "", "top": [], "digest": "4f53cda18c2baa0c"}
```

## Current chapter record (verbatim copy)

```json
{
 "id": "sec-proetale-coefficients",
 "kind": "chapter",
 "title": "The Pro-étale Site and Coefficients",
 "uses": [
  "sec-abelian-varieties",
  "sec-nagata-compactification",
  "sec-picard-framework"
 ],
 "key_theorem": null,
 "reference": null,
 "text": "**Content.** The pro-étale site of a scheme and the coefficient categories built on it, as in\n§2–§3 of the notes on condensed coefficients and six functors. Weakly étale, ind-étale and\npro-étale morphisms define the small pro-étale site ([sk-def-pe-site]), whose topos has enough\nweakly contractible affine objects ([sk-thm-pe-weakly-contractible-basis]). Consequently it is\nreplete, products and sequential limits are exact, and unbounded complexes are left complete.\nThe comparison morphism with the étale site identifies classical sheaves, bounded-below\ncohomology, direct images, constructible complexes and complexes of finite Tor amplitude on the\ntwo sites ([sk-thm-pe-classical-sheaves], [sk-thm-pe-constructible-comparison]). The pro-étale\ngeometric point computes continuous Galois cohomology, and the open–closed operations and\nderived completion prepare the adic coefficients.\n\nThe second part fixes the coefficient rings $A$, $\\Zl$, $\\cO_E$, $\\Ql$, $E$, $\\Qlb$ as condensed\nrings, compares them with completed coefficients, and defines Tate twists, rationalization,\nconstructible complexes $\\Dbc$ and $\\Dctf$ ([sk-def-sfb-constructible]) and the localizing\nclosure $\\Loc(\\Dctf)$ on which the exceptional inverse image is constructed in\n§[sec-six-functors-basics].",
 "source": "literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/_section.md"
}
```

## Current unit record and realized bindings (verbatim copy)

```json
{
 "id": "sk-prop-sfb-module-category",
 "kind": "unit",
 "chapter": "sec-proetale-coefficients",
 "title": "Structure of $\\Mod_{\\mathcal R}(\\mathcal C)$",
 "lean": [
  "CategoryTheory.Mod.instFaithfulForget_weilConjectures",
  "CategoryTheory.Mod.isLimitKernelFork",
  "CategoryTheory.Mod.isColimitCokernelCofork",
  "CategoryTheory.Mod.instAbelian_weilConjectures",
  "CategoryTheory.Mod.instPreservesFiniteLimitsForget_weilConjectures",
  "CategoryTheory.Mod.instPreservesFiniteColimitsForget_weilConjectures",
  "CategoryTheory.Mod.fullyFaithfulToBimod",
  "Bimod.IsSymmetric.iso",
  "Bimod.IsSymmetric.tensorBimod",
  "CategoryTheory.Mod.monoidalCategory",
  "CategoryTheory.Mod.symmetricCategory",
  "CategoryTheory.Mod.braidedCategory",
  "CategoryTheory.Mod.monoidalClosed",
  "CategoryTheory.Mod.isGrothendieckAbelian",
  "CategoryTheory.Mod.hasFunctorialFlatResolution"
 ],
 "uses": [
  "sk-def-sfb-module-objects"
 ],
 "statement": "Let $\\mathcal C$ be a monoidal category and $\\mathcal R$ a monoid object of $\\mathcal C$,\nwith module objects as in [sk-def-sfb-module-objects]. The forgetful functor\n$\\Mod_{\\mathcal R}(\\mathcal C)\\to\\mathcal C$ is faithful.\n\n1. **Abelian structure.** Let $\\mathcal C$ be abelian with $\\otimes$ additive in each\n   variable, and let $\\mathcal R\\otimes-$ be right exact. Then $\\Mod_{\\mathcal R}(\\mathcal C)$\n   is abelian, and kernels and cokernels are computed in $\\mathcal C$. More precisely, the\n   kernel (cokernel) in $\\mathcal C$ of a morphism of module objects carries a unique action\n   of $\\mathcal R$ that makes it the kernel (cokernel) in $\\Mod_{\\mathcal R}(\\mathcal C)$. The\n   forgetful functor is exact.\n2. **Relative tensor product.** Let $\\mathcal C$ be braided, with braiding $\\beta$, and\n   have coequalizers. Assume $X\\otimes-$ and $-\\otimes X$ preserve colimits for every $X$,\n   and let $\\mathcal R$ be commutative. Every $\\mathcal R$-module object $M$ is then also a\n   right module, via $\\gamma_M\\circ\\beta_{M,\\mathcal R}\\colon M\\otimes\\mathcal R\\to M$. This\n   identifies $\\Mod_{\\mathcal R}(\\mathcal C)$ with a full subcategory of the\n   $\\mathcal R$-$\\mathcal R$-bimodules, the *symmetric* bimodules. The *relative tensor\n   product* is the coequalizer\n   $$\n   M\\otimes_{\\mathcal R}N:=\\operatorname{coeq}\\Bigl(M\\otimes\\mathcal R\\otimes N\n   \\rightrightarrows M\\otimes N\\Bigr)\n   $$\n   of $(\\gamma_M\\beta_{M,\\mathcal R})\\otimes N$ and\n   $(M\\otimes\\gamma_N)\\circ\\alpha_{M,\\mathcal R,N}$, with $\\mathcal R$ acting through $M$.\n   It makes $\\Mod_{\\mathcal R}(\\mathcal C)$ a monoidal category with unit $\\mathcal R$. If\n   $\\mathcal C$ is symmetric, the braiding of $\\mathcal C$ descends to $\\otimes_{\\mathcal R}$\n   and makes $\\Mod_{\\mathcal R}(\\mathcal C)$ symmetric monoidal.\n3. **Closed Grothendieck structure.** Let $\\mathcal C$ be a closed symmetric monoidal\n   Grothendieck abelian category with $\\otimes$ additive in each variable, and let\n   $\\mathcal R$ be commutative. Then $\\Mod_{\\mathcal R}(\\mathcal C)$, with\n   $\\otimes_{\\mathcal R}$, is a closed symmetric monoidal Grothendieck abelian category.\n   Call an object $F$ *flat* if $F\\otimes-$ and $-\\otimes F$ are exact. A *functorial flat\n   resolution* is a functor $P$ to flat objects with a natural epimorphism $P(M)\\to M$. If\n   $\\mathcal C$ has one, so does $\\Mod_{\\mathcal R}(\\mathcal C)$, given by\n   $$\n   \\mathcal R\\otimes P(M)\\to\\mathcal R\\otimes M\\xrightarrow{\\gamma_M}M .\n   $$\n4. **Sheaves of modules.** In particular, let $\\Lambda$ be a commutative condensed ring\n   and $X$ a scheme. Then $\\Mod_{\\Lambda_X}$ is a closed symmetric monoidal Grothendieck\n   abelian category with unit $\\Lambda_X$ and functorial flat resolutions. Its forgetful\n   functor to $\\Sh(X_{\\mathrm{proét}},\\Ab)$ is exact and faithful.",
 "steps": [
  {
   "text": "Faithfulness is [lem-sfb-modobj-forget-faithful]."
  },
  {
   "text": "Part 1. Kernels and cokernels are computed in $\\mathcal C$ by\n[lem-sfb-modobj-kernels] and [lem-sfb-modobj-cokernels]. The category is abelian by\n[lem-sfb-modobj-abelian]. The forgetful functor is left exact by\n[lem-sfb-modobj-forget-left-exact] and right exact by\n[lem-sfb-modobj-forget-right-exact]."
  },
  {
   "text": "Part 2. Module objects are the symmetric bimodules by\n[lem-sfb-modobj-symmetric-bimodules] and [def-sfb-symmetric-bimod-module-iso]. Symmetric bimodules are stable under the tensor\nproduct of bimodules by [lem-sfb-symmetric-bimod-tensor]. The monoidal structure is\n[def-sfb-modobj-relative-tensor], and the symmetric structure is\n[def-sfb-modobj-symmetric-tensor]."
  },
  {
   "text": "Part 3. Since $\\mathcal C$ is closed, $X\\otimes-$ is a left adjoint. By the symmetry, so is\n$-\\otimes X$. Hence both preserve colimits, and in particular $\\mathcal R\\otimes-$ is right\nexact. An abelian category has coequalizers. So parts 1 and 2 apply. Closedness is\n[def-sfb-modobj-internal-hom]. The Grothendieck property is\n[lem-sfb-modobj-grothendieck], and the flat resolutions are\n[lem-sfb-modobj-flat-resolutions]."
  },
  {
   "text": "Part 4. Take $\\mathcal C=\\Sh(X_{\\mathrm{proét}},\\Ab)$ with the tensor product of\n[sk-def-sfb-sheaf-tensor]. It is closed symmetric monoidal. Its tensor product preserves\ncolimits in each variable, so in particular it is additive. It is a Grothendieck abelian\ncategory:\n- filtered colimits are exact, because sheafification is exact and filtered colimits of\n  presheaves of abelian groups are exact;\n- the sheafified free abelian sheaves $\\mathbf Z_U$ on the objects $U$ form a generating\n  family, and $X_{\\mathrm{proét}}$ is essentially small."
  },
  {
   "text": "It has functorial flat resolutions. $\\mathbf Z_U\\otimes F$ is the sheafification of\n$V\\mapsto\\bigoplus_{\\Hom(V,U)}F(V)$, which is exact in $F$. Hence $\\mathbf Z_U$ is flat,\nand so are direct sums of such sheaves. The canonical map\n$\\bigoplus_{U,\\ s\\in M(U)}\\mathbf Z_U\\to M$ is a functorial epimorphism. Finally,\n$\\Lambda_X=p_X^*\\Lambda$ is a commutative monoid object because $p_X^*$ is braided\n([sk-def-sfb-pulled-back-coefficients]). Now apply parts 3 and 1."
  }
 ],
 "source": "literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-sfb-module-category/_section.md",
 "realized": {
  "statement": [],
  "steps": [
   [],
   [],
   [],
   [],
   [],
   []
  ]
 },
 "realized_by": null
}
```

## Dry-run validation

Required command:

```text
python3 /home/ubuntu/weil-launcher-nt/deliver.py Q09 def-sfb-modobj-internal-hom --no-push
```

The actual stdout and exit result are retained in the sandbox as `dry-run-repair.log`. A READY handoff requires this invocation to print `OK (not pushed)` after preflight; neither the earlier timeout nor elapsed lock-wait time counts as success. The command uses the current remote base and preserves maintained fields. No compiler or Lake command is part of this stage-1 validation.


## Second reading by Q09

This is a fresh independent reading of the retained split, not the earlier reading quoted above. I opened the main-20261015 blueprint definition `def-sfb-modobj-internal-hom.md`, its `sk-prop-sfb-module-category/_section.md` (clause 3), the chapter Markdown, every direct cited node statement, and Stacks `categories.tex`, Tag 0038, label `lemma-adjoint-exact` (including its proof and the tag index). The item statement agrees verbatim with the blueprint: closed symmetric monoidal Grothendieck abelian ambient category, additive tensor, commutative monoid, the two specified equalizer arrows, target action, and the stated orientation of the adjunction. No missing hypothesis or statement dispute was found. The source has no proof section; the expanded proof is correctly marked agent-written. No SGA route is used.

- Step 1: checked the small-colimit clause of `def-sp-grothendieck-abelian`, the exact preservation statement of `lem-weil-pbc-left-adjoint-preserves-colimits` against Stacks 0038, and the hypotheses of `def-sfb-modobj-relative-tensor`, `def-sfb-modobj-symmetric-tensor`, and `lem-sfb-modobj-abelian`; PASS, with symmetry explicitly producing the second ambient adjunction and preservation of finite colimits verified before applying the abelian lemma.
- Step 2: checked kernels in `def-sp-abelian` and both transposes in the blueprint definition; PASS, since a map factors through ker(p-q) exactly when its composites with p and q agree, and uncurrying gives the displayed relation (B).
- Step 3: checked the unit and associativity equations in `sk-def-sfb-module-objects`; PASS, because both uncurried equations are the corresponding equations for the target N, with the tensor permutations specified explicitly.
- Step 4: checked relation (B), target associativity in `sk-def-sfb-module-objects`, and the item's commutativity hypothesis; PASS, with each of the four equalities in the scalar-slot computation accounted for and the equalizer lift defining the action. Slot notation denotes morphism composites, so no element-detection assumption is made.
- Step 5: checked both module equations and the morphism equation in `sk-def-sfb-module-objects`; PASS, since postcomposing the equations with the monic equalizer inclusion gives the equations already proved on H, and postcomposition by a linear target map respects (B) and the target action. Functoriality is uniqueness of those lifts.
- Step 6: checked the actual parallel pair and first-factor action in `def-sfb-modobj-relative-tensor`, colimit preservation in `lem-weil-pbc-left-adjoint-preserves-colimits`, and the linearity equation in `sk-def-sfb-module-objects`; PASS, since tensoring the coequalizer projection remains a coequalizer and hence epi. Balance plus first-factor linearity is exactly the displayed second-factor linearity, with no flatness assumption.
- Step 7: checked the displayed uncurried equation against the two arrows p and q of the item's source; PASS, giving precisely second-factor linearity after the stated symmetry. This uses the equalizer universal property and the assumed ambient adjunction only.
- Step 8: checked the module-morphism equation in `sk-def-sfb-module-objects` and the action defined in step 3; PASS, with currying turning first-factor linearity into linearity of h and monicity of i reflecting that equation to its lift. No preservation of monomorphisms by tensor is used.
- Step 9: checked the forward/reverse formulas against steps 6--8 and naturality of the given ambient adjunction; PASS, since the symmetry squares to the identity, the two universal properties give inverse lifts, and the written pre/postcomposition identities give naturality in both variables.
- Step 10: checked the natural module isomorphism asserted by `def-sfb-modobj-symmetric-tensor`; PASS, since precomposition changes the adjunction for L tensor_R M to the required one for M tensor_R L, with its inverse and naturality explicitly specified.
- New nodes: none; B1--B7 introduce no new obligations. A fresh DAG search found `lem-weil-pbc-module-relative-tensor-adjoint` (existence of a right adjoint only), `def-sfb-derived-hom-modules` (derived category), and restriction/coextension nodes (change of coefficients); none substitutes for the specified ambient equalizer and target action, and none needs to be recreated.

Edge cases checked independently: over a field k in ordinary k-vector spaces the equalizer is the subspace of R-linear maps, with (r f)(m)=r f(m), and the formulas are the usual bilinear adjunction, including M=0 and N=0. With R equal to the tensor unit both equalizer arrows agree and the result is the given ambient adjunction. With M=R, evaluation at the unit identifies the internal hom with N. The zero coefficient monoid has only zero modules by its unit law. The empty-scheme sheaf category is the zero category, where the construction and both hom-set bijections are unique. These checks require neither a nonzero coefficient ring nor a nonempty scheme.

I also read the concrete upstream `Mod/InternalHom.lean` construction and `Mod/Tensor.lean` lines 139--151 as a check, without compiling or changing any Lean. Its `ihom'Adjunction` uses `tensorLeft M` whose object is P tensor_R M; it is not advertised as an exact attachment for the item's full specified symmetric closed structure. Upstream sorry declarations are not evidence of completion.

Changes made and why:

- Retained the statement and all ten mathematical steps: the independent source and hypothesis checks found no mathematical repair needed.
- Ran a fresh LeanFinder search using algebra-object/closed-tensor vocabulary and a grep of Mathlib's actual `CategoryTheory/Monoidal/Mod.lean`. The returned ordinary-module and light-condensed instances do not apply to arbitrary internal module objects; the Gabriel-Popescu construction has a different source category. The first new grep invocation accidentally passed `--sub` as a positional directory and is explicitly inconclusive; the corrected invocation was run immediately. All twelve raw search records are retained, and the two valid fresh searches with their actual results and verdicts are appended to the item's `mathlib_searches`. The complete embedded log above is refreshed so the committed report retains the evidence.
- Rechecked every one of the fourteen citation pairs against its current full statement; `citations.json` remains correct without changes. The sandbox chapter/unit records still equal the current maintained records, including all realization slots, so the earlier structural return is repaired without changing the unit route or claiming realization of its other clauses.

Validation: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q09 def-sfb-modobj-internal-hom --no-push` exited 0 and printed `OK (not pushed) deliver/Q09/def-sfb-modobj-internal-hom at ad887e6db6: preflight passed`. The actual output is retained in `dry-run-second-reading.log`. The normal delivery command reruns preflight before pushing; no Lean was written or compiled.
