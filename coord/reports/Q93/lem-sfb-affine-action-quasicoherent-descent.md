# Stage-1 delivery: lem-sfb-affine-action-quasicoherent-descent

## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-action-quasicoherent-descent.json`: 11 proof steps, statement unchanged, with explicit antipode convention, arbitrary scalar-extension charts, algebra equivalence, surjections and global sections.
- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-qcqs-atlas-affine-diagonal.json`: statement-only general geometric lemma; no Mathlib match.
- `citations.json`: one verbatim statement quote for every node used in every step. Searches are retained in `searches.jsonl`.

Attachments: none. Searches of `lean/WeilConjectures/` for the exact blueprint tag, quotient stacks, groupoids, equivariant quasi-coherence and affine actions found no declaration of the item. `Mathlib/AlgebraicGeometry/ColimitsOver` in the project constructs scheme quotients of abstract monoid actions, not the torsor stack or the algebra/descent dictionary, so is not an attachment.

WANTED: none. All supporting mathematics used here was read in the local Stacks TeX sources.

The live item had an empty proof. Its source and statement were retained. The finite-generation assumption in `lem-sfb-affine-action-stack-presentation` and `lem-sfb-flat-affine-action-algebra-descent` cannot be silently removed; nor can finite locally free arrows in `lem-sfb-affine-groupoid-quasicoherent-algebra-descent` be used for this smooth positive-dimensional group. The latter's newly landed supporting node `lem-sfb-groupoid-module-descent-tensor-cokernel` DOES give the general module statement needed, and is used directly. I checked its complete statement, including its big-fppf site, tensor constraints and ambient cokernel clauses, before using it. No proposed smooth-affine module-descent node was written; that would duplicate the landed node. This reduced the delivery to one new geometric lemma.

Nothing is left unfinished in the split. The new geometric lemma is intentionally unsplit, with empty proof/proof_deps and no proof sketch in its statement. Its later proof follows the surjection lemma and the affine-diagonal test cited below. No Lean was written or compiled. No repository or launcher files were written and no repository git commands were run.

## Source and route

I read `GOAL.md`, the three permitted blueprint levels in `SETUP.md`, the chapter and unit DAG records, and the current files under `literature/blueprint/latest/blueprint/sec-six-functors-basics/`: the chapter, `sk-thm-sf-ctf-stability/_section.md`, its proof, and the direct-image proof. This item is the inherited supporting affine quotient calculation beneath alteration/direct-image proof (3), not a unit's key node. No unit record is edited. The recorded unit/chapter metadata mismatch and null nearest blueprint ancestor pre-exist: `tools/blueprint_refs.py ancestor` returns None. I retained the inherited full via chain and specific place instead of inventing a blueprint ancestor. Whole-blueprint searches for 06WT, 06WV, 050X, 075S, 04YC, module descent, smooth groupoid, affine groupoid, smooth surjective and quasi-compact diagonal found no matching blueprint theorem; the affine-diagonal hit was an injective-restriction acyclicity theorem, not this geometric criterion.

Sources opened:
- `stacks-sheaves.tex`, Tag 06WT, `proposition-quasi-coherent`, including both directions of its construction and its descent isomorphism orientation. Also Tag 06WV, `lemma-quasi-coherent-algebraic-stack`, and Tag 06WN, `lemma-qc-colimits`, for tensor products and ambient cokernels; the latter is important because the big-site inclusion is not left exact in general.
- `spaces-groupoids.tex`, Tag 0441, `definition-groupoid-module`, and Tag 077X, `lemma-colimits`, whose proof computes colimits on U; `groupoids.tex`, Tag 03LF, `definition-equivariant-module`, for the identity and cocycle conventions.
- `algebraic.tex`, Tag 04TK, `theorem-smooth-groupoid-gives-algebraic-stack`; the existing smooth quotient node includes the atlas and the arrow fibre product. The existing torsor comparison cites `examples-stacks.tex` Tag 04WM and explicitly allows arbitrary schemes as action targets.
- `stacks-morphisms.tex`, Tag 050X, `lemma-surjection-from-quasi-compact`, the actual surjection descent statement; Tag 04YW, `definition-separated`, clause (4), whose quasi-separated diagonal condition matches our predicate; and Tag 075S, `lemma-quasi-compact-quasi-separated-permanence`, to compare the newer general permanence node. Also `stacks-properties.tex`, Tag 04YC, for the atlas convention.
- `morphisms.tex`, Tag 01S7, `lemma-affine-separated`, for affine morphisms being separated and quasi-compact, and `schemes.tex`, Tags 01IB, `lemma-equivalence-quasi-coherent`, 01I8, `lemma-widetilde-constructions`, and 01I9, `lemma-widetilde-pullback`, for the affine dictionary. The nodes for these comparisons already exist and are reused.

The new geometric criterion is the relative form actually needed: for f:Z→Y, qc of the atlas composite descends through its surjection by 050X. An affine relative diagonal has affine scheme base changes; 01S7 gives their quasi-compactness and separatedness, hence quasi-separatedness. This is 04YW(4). It applies without finite type, Noetherianity or a Deligne--Mumford condition, and is smaller than the action-quotient theorem: there is no group, coaction, algebra object, base-change quotient, or invariant computation in it. These source statements supply every hypothesis and conclusion of the new statement.

## Mathlib and duplicate search

Every new search was run through the mandated `msearch.py Q93 lem-sfb-affine-action-quasicoherent-descent` command. Results and exact query texts are in the node and log. Both semantic services, Loogle and source grep ran successfully. A second semantic phrasing was tried for the item, module descent and the geometric criterion. The hits were read: general `SheafOfModules.QuasicoherentData` only defines local quasi-coherence; `pushforwardPushforwardEquivalence` (source opened at lines 372–400) assumes an equivalence of underlying sites and does not prove quotient groupoid descent; representation invariants are for abstract groups; the affine diagonal and qcqs lemmas in `Mathlib/AlgebraicGeometry/Morphisms/` have schemes as objects, not Artin stacks. No exact match or one-line specialization gives the new stack criterion, so it remains unsplit rather than a Mathlib leaf.

Before writing the new node I searched all DAG nodes by tag and concept, the whole blueprint with `blueprint_refs.py search`, and the project Lean by concept. Existing scheme qcqs, DM atlas, finite-type stack atlas and general stack permanence statements were opened. None proves the precise atlas-composite criterion. There are no new definition nodes. The new node names every notion it uses through existing definition nodes, including arbitrary algebraic stacks and representable affine relative diagonals.

## Not duplicates

lem-sfb-stack-qcqs-atlas-affine-diagonal vs def-sfb-stack-qcqs-morphism: The existing node defines the predicates and proves no atlas descent or implication from an affine relative diagonal.

lem-sfb-stack-qcqs-atlas-affine-diagonal vs lem-a1-etale-affine-finite-fibre-refinement: The existing node concerns etale scheme covers of affine schemes and locally quasi-finite composites, yielding finite-fibre refinements; it gives no stack diagonal or atlas criterion.

lem-sfb-stack-qcqs-atlas-affine-diagonal vs lem-sfb-affine-action-quasicoherent-descent: The item is a specific affine group action/coaction and arbitrary-algebra descent dictionary with a scalar-extension and section formula; the new node is a general geometric atlas/relative-diagonal criterion and asserts no coaction, algebra equivalence or invariant-section formula.

lem-sfb-stack-qcqs-atlas-affine-diagonal vs lem-sfb-algebraic-stack-qcqs-permanence: The existing node assumes the source stack is already quasi-compact and absolutely quasi-separated; the new criterion instead assumes a quasi-compact atlas composite and an affine relative diagonal, and establishes the relative predicates without assuming absolute quasi-separatedness of the source or target.

lem-sfb-stack-qcqs-atlas-affine-diagonal vs lem-weil-pbc-affine-morphism-permanence: This is a scheme-only theorem for an affine morphism; our morphism need not be representable or affine, and its quasi-compactness descends from a smooth atlas composite.

lem-sfb-stack-qcqs-atlas-affine-diagonal vs lem-weil-pbc-etale-limit-tail-open-geometry: The existing node concerns qcqs open subschemes in inverse systems with affine transitions, not smooth stack presentations.

lem-sfb-stack-qcqs-atlas-affine-diagonal vs lem-weil-pbc-finite-over-separated-finite-type: The existing node concerns finite scheme morphisms composed with separated finite-type morphisms and gives finite-type/separated conclusions, not a general Artin-stack atlas criterion.

## Review by Q93

I reread delivery-errors B–E with the statements and the source paragraphs open. This is my direct-delivery review; no second worker or agent was started.

Step 1 uses the group scheme's pointwise group laws, affine spectrum contravariance and the affine fibre-product formula; the smooth/etale calculus node explicitly gives base-change stability. Thus the right action and its inverse left action have exactly the convention written in the item, and both s and t are smooth. It does not assume a cocommutative Hopf algebra or test only k-rational group points.

Step 2 uses the full conclusions of the smooth-groupoid quotient node: representable diagonal, smooth surjective atlas and identification of the arrow fibre product. The torsor comparison explicitly permits arbitrary V and sends g to right translation by g inverse, matching our left torsors. I did not cite the finite-type affine-action presentation node for arbitrary D.

Step 3 constructs psi rather than citing a quotient's categorical property not present in a node. The torsor definition gives fppf trivializations; the fppf-to-fpqc node and representable morphism descent node state exactly the covering conversion and unique gluing used. Invariance is a direct equation on j(a), so the local maps agree; uniqueness proves compatibility with arrows and pullbacks.

Step 4 computes the RELATIVE diagonal over A. The affine fibre-product statement makes its source and target affine and identifies the tensor projections. This also proves every map of affine schemes is affine by affine test base changes; the existing affine-morphism permanence node then supplies qc of the atlas composite. Algebraicity supplies relative isomorphism spaces, so the representable locality node applies to this diagonal, not to psi itself. The cover U×_A U is smooth and surjective by the cited chartwise calculus, which also supplies flatness and local finite presentation required by fppf locality. The new geometric lemma is applied only after both its hypotheses (qc composite and affine relative diagonal) are verified. Earlier I had phrased qc via a finite principal-open covering; I replaced that with the cited affine-base-change and permanence argument to leave no implicit topology lemma.

Step 5 uses only the two fibre-product universal properties and torsor definition; it writes both functors. Invariant j(A) is exactly what makes the tensor coaction balanced, and no flatness of C/A is assumed. Compatibility in the 2-fibre product keeps the specified isomorphism; the scheme target is discrete, so its isomorphism condition is equality of structural A-maps.

Step 6 uses general module descent, not a definition of quasi-coherence as a theorem. Its tensor and unit clauses, the affine tensor theorem, affine tilde equivalence and affine pullback-section comparison give multiplication and unit on the chart. Fullness descends them and faithfulness checks each algebra law. Every cited node states the precise module/tensor fact used; no new node simply restates the item's algebra clause.

Steps 7 and 8 spell out the affine calculation from the descent isomorphism to rho_B and back. The balanced tensor source uses the target map rho_E, the target uses the source map e↦e⊗1, and evaluating on b⊗1 gives the coaction. Coassociativity is the displayed pair of triple tensors. The inverse uses the antipode and both group inverse identities, so invertibility is proved rather than presumed. The tensor and group scheme definitions are sufficient for these elementary calculations. Inverting the isomorphism from the s-to-t convention of the module node is explicitly allowed. No sign or inverse is hidden in “transport”.

Step 9 uses the cokernel clause of the module descent statement and affine tilde equivalence; it concludes both directions of surjectivity. The sheaf surjection notion is local lifting as defined in the algebra definition. I checked that the proof needs only cokernels/right exactness, never the false blanket assertion that all big-site module inclusions are exact.

Step 10 uses full faithfulness from the SAME module descent theorem on maps out of its unit object, not only a fully faithful Yoneda embedding or the proof of another node. An O-linear map O→B is a compatible section by multiplication, and its affine representative E→B is given by b. The compatibility equation on 1 is exactly rho_B(b)=b⊗1. Ring operations and the structural map C→E are explicitly identified.

Step 11 uses the affine pullback-section comparison and tensor universal property. It writes the coaction, section restriction and associativity formulas after C→C'. Invariants need not commute with nonflat scalar extension; only the restriction b↦b⊗1 and the chart/algebra dictionary are asserted. This matches the statement's restriction language and avoids adding an incorrect base-change isomorphism.

Small-case checks: G trivial gives ordinary affine quasi-coherent algebras and B^G=B. D=k with trivial action gives BG with arbitrary rational representation algebras; this shows why no DM or finite locally free arrow assumption is permitted (take G=G_m). For G_m acting on k[t] with rho(t)=t⊗z, the left action is t↦z^{-1}t, and our reparametrization recovers the original right coaction. The Hopf inverse calculation works for noncommutative groups because no cocommutativity was used. Zero D or C gives the empty quotient and zero coordinate algebra; zero modules and unit maps are handled by the same formulas. Infinite polynomial algebras and arbitrary, even nonflat, C/A are allowed throughout. The new geometric lemma handles identity atlases, empty atlases and BG_m→Spec k (qc atlas composite and affine diagonal, although this morphism is not representable). Thus its assertion is not being specialized from a scheme-only theorem.

B1–B9: the only new node is statement-only and self-contained, TeX is singly escaped, its sources carry checked Stacks tags and labels, its blueprint origin has the same computed null ancestor as the item and the inherited via chain, and searches reflect actual successful service outputs. C1–C8: every non-elementary input is named, each quote in citations.json is verbatim from its statement, proof_deps is exactly the union of uses, and generic off-unit scheme tools are declared in split_report.tool_uses. The cited general module-descent node has no edge to this item, so this reuse creates no cycle. D1–D5: the argument assembles several independent inputs and gives the affine/Hopf and section calculations itself; only the generic qcqs criterion is new. E1–E7: hypotheses and small cases were checked above; no statement correction or source error was found. All steps are shorter than 2000 characters. No proof route at unit or chapter level is replaced.
