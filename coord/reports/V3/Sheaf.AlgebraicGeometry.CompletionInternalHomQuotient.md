## What changed

The target theorem now combines two strictly smaller finite-level lemmas: annihilation of the ideal product after postcomposition with the quotient, and the internal-Hom isomorphism induced by source quotienting. Added proof-only imports and two new statement modules.

## Proved and sorry left

Closed in the item: `AlgebraicGeometry.completion_internal_hom_quotient`
(node `lem-weil-pbc-completion-internal-hom-quotient`), by conjunction introduction.
Added holes: `AlgebraicGeometry.completion_internal_hom_quotient_annihilation`
(node `lem-weil-pbc-completion-internal-hom-quotient-annihilation`) and
`AlgebraicGeometry.completion_internal_hom_quotient_isIso`
(node `lem-weil-pbc-completion-internal-hom-quotient-isIso`).

This is a decomposition: one upper hole closed, two strictly smaller component
holes added; net holes closed minus added is -1, not a completed finite-level
proof. The target still depends on `sorryAx` through these two components.
No data definitions or arbitrary choices from unproved existence were added.

## No longer needed

No modules or imports pruned. The old direct proof dependencies
`def-weil-pbc-coherent-formal-module`, `def-pur-sheaf-tensor-product`, and
`def-pur-sheaf-hom` are replaced in the item node by the two component nodes.
All three remain needed transitively by those components; the two original
public imports remain necessary for the statements. The added component imports
are proof-only. No unit statement or realized step is bypassed or removed.

## Where the brief, the DAG or earlier work was wrong

The planned proof requires substantial local cokernel and sheaf-factorization theory absent from available declarations, so it was split into the two component statements above.

## New nodes

`lem-weil-pbc-completion-internal-hom-quotient-annihilation` records the annihilation component. `lem-weil-pbc-completion-internal-hom-quotient-isIso` records the quotient-induced internal-Hom isomorphism.

## Earlier second reading (a previous round; superseded)

The target proof compiles and preserves its original signature. The two new component statements are strictly smaller parts of the target and have matching DAG nodes; both remain open for subsequent workers.

## Second reading by V3

1. Compared the item with the repository using `diff`: its existing signature,
visibility, definitions and mathematical docstring are unchanged; only two plain
proof imports and the conjunction proof are added. No change record is needed.
The repository refreshed during review: it initially showed this delivery already
present, but now the item again has `sorry` and the components are new. The
initial duplicate-delivery rejection was superseded by the next dry run.

2. All three modules compiled with `lcompile.py --all` (each about two seconds).
The two named component theorems are the only remaining holes. No axiom, unsafe,
opaque, implemented_by, extern, hollow definition or data choice was introduced.
The axiom probe reports only propext, Classical.choice, Quot.sound and sorryAx.
The upper theorem therefore has a checked reduction, not an axiom-free proof.

3. Read the cokernel definitions in `CoherentFormalModule` and the internal-Hom
map in `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`; read
Stacks Tag 0882 online. That tag proves the completion comparison under coherence
and Noetherian hypotheses; these finite-level preliminary assertions have the
explicit local arguments recorded here and require neither hypothesis. Checked
n = 0 (target quotient is zero), n = m (ordinary quotient factorization), zero
ideal at positive n (identity quotients), and the unit ideal (zero quotients).
Both statements hold. The first component removes the irrelevant m and n ≤ m;
the second isolates unique source factorization. Neither restates the whole
conjunction, but together they only decompose it and increase the hole count.
Repeated search with `msearch.py` for an internal-Hom functor sending cokernels
to kernels, plus rg for homObj/cokernel/kernel and ideal products, found no
existing finite-level result. LeanFinder returned abelian-category and free
presentation lemmas, not either component. Loogle could not resolve the short
identifier cokernel, so that query gives no absence evidence. The general
cokernel universal property alone does not supply the missing annihilation.
Added full natural-language proofs and precise source context to both component
docstrings, including local lifts rather than surjectivity on arbitrary opens.

4. The reduction is the shortest conjunction proof once the two components are
available. Its mathematical content remains open; neither component was closed
in this review. All four item imports are necessary, with the two component
imports plain rather than public. Reviewed `dag/units/sk-thm-p1.json`: the item's
finite-level refinement is below its fixed realized nodes, none of which changed.
No longer needed now names every replaced old direct proof dependency and
explains why these definitions stay needed transitively. No module is pruned.

5. The original item node was wrong: it still described the unsolved local
argument and did not cite the component nodes the Lean proof applies. Replaced
its proof, proof_deps and proof_origin with the actual conjunction reduction.
Both new nodes have source, three search records, creation provenance, blueprint,
chapter/unit and verbatim Lean signatures. Their proof texts now contain the
complete arguments from their docstrings. Existing statement fields are unchanged.

Changes by the second reader: completed both component/module docstrings;
corrected the three nodes' proof descriptions and the item's direct dependencies;
made the report explicit about decomposition, the two added holes and net -1.
