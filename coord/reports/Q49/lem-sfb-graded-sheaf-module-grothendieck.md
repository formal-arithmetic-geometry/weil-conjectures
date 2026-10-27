## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-graded-sheaf-module-grothendieck.json`: the item, split into five steps; statement unchanged; existing searches retained and Q49 searches appended.
- `dag/nodes/sec-six-functors-basics/lem-sfb-graded-open-extension-adjunction.json`: one new statement-only node, unsplit, not found in Mathlib after two semantic phrasings, Loogle, LeanSearch and source grep.
- `citations.json`: ten verbatim statement quotations, one for every step/node pair.

Attachments: none. Searching `lean/WeilConjectures/` by the item tag, graded sheaves/modules, and extension-by-zero terminology found no completed declaration of the item or the new node. AlgebraicGeometry/GradedSheafStructures concerns graded quasi-coherent scheme data, not this category or its adjunction.

WANTED: none. The sources used are available in `literature/stacks-project/`.

The inherited item had no proof. No statement dispute was found. Its left-module conventions require an explicit sign in the shifted free-module evaluation; copying the unsigned right-module formula would be incorrect. Step 4 writes that sign and its inverse calculation. Step 5 proves faithfulness on distinct maps, rather than only copying the source's detection of zero objects. The existing dg extension adjunction does not apply to arbitrary graded modules by simply ignoring a differential: such modules need not carry a compatible differential at all. A separate graded adjunction is necessary.

Nothing remains unfinished in this one-level split. The new input is intentionally statement-only and joins the stage-1 queue. No Lean was written or compiled, no build command or repository git command was run, and all writes were confined to this sandbox.

## New nodes

`lem-sfb-graded-open-extension-adjunction`: a functor on arbitrary graded modules over a graded sheaf algebra, constructed by degreewise sheafification of the open-extension presheaf, with the restriction adjunction. Source: Stacks 0FRA, `sdga-lemma-extension-by-zero-graded`, and its preceding construction. Definition-gm is 0FQZ. The new node is strictly an input to the generator construction, not abelianness, AB5, existence of colimits, or the generator clause restated.

## Searches and blueprint

Whole-DAG searches covered tags 0FR0, 0FRD, 0FRA, the label `extension-by-zero-graded`, and titles/statements about graded modules, module generators, extension by zero and tensor colimits. Whole imported-blueprint searches via `tools/blueprint_refs.py search` used `graded`, `graded module`, `graded modules`, `graded sheaf`, `extension-by-zero-graded`, `0FRA`, `tensor colimits`, and `Grothendieck abelian`. No imported blueprint node states the graded extension adjunction or the item. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and the recorded chapter/unit. The supporting ringed-space argument stays below the unit and follows the inherited source chain. The ancestry command returns null for the inherited chain; I retained that value and prepended the item to the new node's `via` list.

Every Mathlib query was run through the required Q49 `msearch.py` command and is recorded verbatim from `searches.jsonl`. Both phrasings for the item and both phrasings for the new adjunction were inspected. None of the services used here was unavailable. LeanFinder and LeanSearch return ordinary `SheafOfModules` sheafification/colimit constructions, `Sheaf.instIsGrothendieckAbelian`, and `Gmodule` on families of types. I read Mathlib `CategoryTheory/Abelian/GrothendieckAxioms/Sheaf.lean:64-84`, `Algebra/Category/ModuleCat/Sheaf/Abelian.lean:34-42`, `Algebra/Module/GradedModule.lean:39-54`, `Algebra/Category/ModuleCat/Presheaf/Sheafification.lean:85-137` and `AlgebraicGeometry/Modules/Sheaf.lean:425-437`. Ordinary sheafification is not the graded action lift, and the scheme restriction adjunction is restriction left adjoint to pushforward, not extension by zero left adjoint to restriction. No hit is an exact match or a one-line specialization. There are zero new Mathlib leaves.

## Not duplicates

lem-sfb-graded-open-extension-adjunction vs lem-sfb-sheaf-dg-open-extension-adjunction: the existing statement requires dg algebras, dg modules and chain maps; the new statement has arbitrary graded algebras/modules with no differential and all degree-zero graded maps. Forgetting a differential does not produce its adjunction.

lem-sfb-graded-open-extension-adjunction vs lem-sfb-sheaf-dg-open-extension-calculus: the existing conclusion is an adjunction on localized dg derived categories, with homotopies, quasi-isomorphisms and coherence; it does not state the adjunction on arbitrary graded modules before any localization.

lem-sfb-graded-open-extension-adjunction vs lem-sfb-sheaf-dg-grothendieck: the existing statement concerns the Grothendieck category of dg modules and its underlying-complex functor; it does not state a graded open-extension functor or its Hom bijection.

lem-sfb-graded-open-extension-adjunction vs lem-sfb-sheaf-dg-binary-gluing: the existing statement glues dg objects and arrows on two opens using a signed overlap cone, not arbitrary graded modules and the open-extension adjunction.

lem-sfb-graded-open-extension-adjunction vs lem-sp-module-extension-zero-independent-ring: the existing statement gives ordinary module extension and restriction over one ring sheaf; it has no graded algebra action mixing degrees. The graded action lift and its action-preserving Hom correspondence are additional content.

## Tool uses

`lem-pur-ringed-site-grothendieck-abelian` supplies the ordinary module abelian category, its small colimits and exact filtered colimits. `lem-weil-pbc-independent-sheaf-tensor-colimits` supplies fixed-factor tensor preservation of small colimits, also for the quotient actions. Both are generic inputs explicitly underlying Stacks 0FR0, not a different proof route for the constructibility unit. They are declared in `split_report.tool_uses`; no maintainer-owned `tool_uses` field was set. Their dependency closures do not reach the item.

## Review by Q49

I read the item against `sdga.tex`, 0FR0 (`lemma-gm-abelian`) and 0FRD (`lemma-gm-grothendieck-abelian`), and read all of the new node's source 0FRA (`lemma-extension-by-zero-graded`) including the construction and action-compatibility proof. I also read 0FQZ (`definition-gm`) and its explicit allowance of left modules. The source assumes a ringed site; the item's topological open site is a permissible specialization in its chosen universe. The source's algebra is graded; forgetting the dg differential imposes no extra hypothesis. Commutativity is required only for the base sheaf O, not for the graded algebra. No boundedness, flatness, quasi-coherence, finite-type or compactness assumption is used.

Step 1 uses the actual statement of `lem-pur-ringed-site-grothendieck-abelian` for ordinary abelianness, `def-weil-sheaf-of-modules-category` for sectionwise kernels and sheafified cokernels (it states those facts explicitly), and the actual fixed-factor preservation statement of `lem-weil-pbc-independent-sheaf-tensor-colimits`. The last preserves the cokernel diagram and hence gives the quotient action without assuming that tensor is left exact. Associativity is checked after epimorphic tensor quotient maps, twice where necessary. The coimage/image inverse is checked for action preservation, not merely asserted as a graded inverse. Componentwise kernels/cokernels then detect exactness.

Step 2 uses ordinary small colimits from the same Grothendieck statement and tensor preservation from the same tensor node. The index category is small in the coefficient universe, and the open site is small there. The displayed equation defines the action from the colimit universal property. The two associativity maps agree on every structure map after tensoring twice; the factorization into any cocone is likewise tested on those structure maps. This proves the graded colimit property rather than presupposing it, and includes the empty diagram.

Step 3 uses the exact-filtered-colimit clause in the ordinary Grothendieck node's statement, with the exactness detection and colimit constructions already proved in steps 1 and 2. It does not take any unstated fact from that node's proof and does not claim that arbitrary section evaluation commutes with filtered colimits.

Step 4 uses the signed shift formula explicitly stated in `def-sfb-sheaf-dg-module-localization`, and the new graded Hom adjunction's statement. Its ordinary inverse evaluation is written out: for the shift [-n], b maps to (-1)^(n|b|)bm; applying the shifted action gives cancellation of the two n|a| signs. The formula is natural in restrictions and target maps. Ignoring the differential on the shifted regular module is allowed here because every object of Gr(A) has no differential. The new adjunction is then applied with this specific graded free source. This is elementary after the cited adjunction and shift conventions; no general representability or projection-formula theorem is hidden in the step.

Step 5 uses `def-weil-size-convention` to bound the open indexing set and `def-sp-grothendieck-abelian` for the concluding definition. The family includes every integer degree and every open; two distinct maps differ on some section. Extending the corresponding test map by zero on all other summands proves faithful Hom(G,-), the actual generator condition. This avoids relying on a weak zero-object detector as if it were automatically a generator. Only the elementary coproduct universal property is used here beyond the earlier steps.

For the new node I checked B1-B7 directly: its proof and proof dependencies are empty, it introduces X, O, A, U, L and M independently, it defines graded algebras/modules in the statement, its module and sheafification notions cite their actual definition nodes, TeX is singly escaped, and the source has the correct stable tag and label. It states no source-dependent shorthand for its meaning. Searches and the same-tag comparisons above address B8-B10 and C5. C1-C4 are checked by the ten verbatim quotations in citations.json and the step-by-step readings above. No citation points to a proof-only construction. The new adjunction is an independent input, not a clause of the conclusion or an intermediate assertion first proved and then cited; the actual Grothendieck argument remains in the item, addressing D1-D5.

I tested the new adjunction on U empty (both the extended object and source Hom are zero), U=X (the identity restriction), the zero ring, the zero module, and a one-point space with a noncommutative graded algebra. Its open-extension presheaf has well-defined zero restriction maps when a large open is not contained in U; its restriction to U is already L. The statement imposes no differential, which is essential for these graded tests. For the item's signed evaluation I checked n=0, odd n and odd |a| over characteristic different from two, characteristic two where signs become trivial, and negative degrees. The empty space gives the zero category and generator zero; an empty colimit is zero, not an excluded case. No assumption of exact products or of sectionwise surjectivity of sheaf epimorphisms occurs. All five steps are below 2000 characters (1200, 976, 489, 901, 740), and each was read for hidden independent inputs regardless of its length.

Corrections during self-review: the source's unsigned right-shift evaluation was translated to the actual signed left convention; the generator argument was made faithful on maps; the dg-only adjunction was excluded as an invalid citation; and the ordinary tensor-colimit node was cited explicitly for both quotient and colimit actions. There was no earlier delivery or return to repair. The item statement and all maintainer-owned fields are preserved.
