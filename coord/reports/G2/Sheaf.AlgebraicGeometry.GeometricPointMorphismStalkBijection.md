## What changed

The existing statement and docstring of `geometricPointMorphism_stalk_bijection` are
unchanged. Its proof combines the category-equivalence, set-stalk and additive-stalk
components. The second reader proved the latter two using Mathlib's canonical
`colimit.pre`, its formula `colimit.ι_pre`, and the final-functor isomorphism instance.
Uniqueness follows from `Point.presheafFiber_hom_ext`. For sets, `isIso_iff_bijective`
converts the isomorphism to a bijection. All added imports are proof-only.

The three new component modules and nodes are included. Their circular proof plans
were repaired, their blueprint origins corrected to this item, and their docstrings
now contain full proofs in words. The existing item's node now records the actual
three-component reduction. Removed the unused proof import of
`Sheaf.AlgebraicGeometry.SpecFieldPointResidueField` from the target and components.

## Proved and sorry left

Original holes closed (one):

- `AlgebraicGeometry.Scheme.geometricPointMorphism_stalk_bijection`
  (`lem-weil-pbc-geometric-point-morphism-stalk-bijection`).

New proved declarations (no direct sorry):

- `AlgebraicGeometry.Scheme.geometricPointMorphism_set_stalk`
  (`new-geometric-point-morphism-set-stalk`).
- `AlgebraicGeometry.Scheme.geometricPointMorphism_addCommGrp_stalk`
  (`new-geometric-point-morphism-addcommgrp-stalk`).

New holes added / all sorry left in this delivery (one):

- `AlgebraicGeometry.Scheme.geometricPointMorphism_category_equivalence`
  (`new-geometric-point-morphism-category-equivalence`). Its source and full proof
  in words are in its docstring and node. It is only the first conjunct of the item.

This is a decomposition: one original hole closed and one strictly simpler hole
added, net zero before import pruning. Neither the assembled item nor its stalk
components are axiom-free yet: they depend on the remaining equivalence hole.
The second reading closed the first worker's two stalk-component holes. No hole
was moved into a definition, and no arbitrary data was chosen from an unproved
existence statement. The comparison morphism is the canonical colimit comparison.

## No longer needed

Removed redundant proof imports of `Mathlib.CategoryTheory.Limits.Final` from the
new stalk modules; EtalePoint already provides the required API transitively.

Removed import/module: `Sheaf.AlgebraicGeometry.SpecFieldPointResidueField`. The
field-map representation uses Mathlib's `Spec.homEquiv` instead. This describes
pruning for this item's proof; it does not claim that no other target imports it.

Every old direct `proof_deps` entry is replaced in the item's node by the three
component nodes:

- `lem-weil-pbc-morphism-from-spec-field`
- `lem-weil-pbc-residue-field-point-naturality`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-spec-field-point-residue-field`
- `def-weil-residue-field`
- `def-weil-geometric-point`
- `def-weil-pbc-etale-site`
- `def-weil-pbc-pointed-etale-neighbourhoods`
- `lem-weil-pbc-etale-residue-field-extension-separable`
- `def-weil-pbc-separable-algebraic-extension`
- `def-weil-algebraic-closure`
- `lem-weil-pbc-algebraic-over-algebraically-closed-subfield`
- `def-weil-pbc-geometric-stalks`
- `def-weil-pbc-abelian-etale-sheaves`
- `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`

The category component retains the geometric argument's dependencies except
`lem-weil-pbc-spec-field-point-residue-field`, which is replaced by `Spec.homEquiv`.
The stalk components use `def-weil-pbc-geometric-stalks` through Mathlib's colimit
API. `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered` is not needed as a
separate proof step: colimit comparison along an equivalence works in any category
with the required colimits. `def-weil-pbc-abelian-etale-sheaves` remains a statement
dependency, not a proof dependency. No unit-realizing node is removed.

## Where the brief, the DAG or earlier work was wrong

The initial report called the target proved without identifying the decomposition's
hole count. The three new nodes used the target itself as their proof dependency,
creating a circular mathematical plan, and copied an unrelated blueprint origin.
Their docstrings lacked proofs in words, and the target node had not been updated.
The set and additive components did not require fresh geometric arguments: Mathlib
already supplies the colimit comparison and invertibility along an equivalence.
No mathematical error in the target statement or unit route was found.

## New nodes

`new-geometric-point-morphism-category-equivalence` is the remaining geometric
component (steps 1–4 of the original argument), strictly weaker than the item.
Its node is
`dag/nodes/sec-proper-base-change/new-geometric-point-morphism-category-equivalence.json`.

`new-geometric-point-morphism-set-stalk` is the now-proved set-valued colimit
comparison (step 5), using the geometric equivalence and Mathlib colimit APIs.
Its node is `dag/nodes/sec-proper-base-change/new-geometric-point-morphism-set-stalk.json`.

`new-geometric-point-morphism-addcommgrp-stalk` is the now-proved additive colimit
comparison (step 5), by the same categorical argument directly in AddCommGrpCat.
Its node is
`dag/nodes/sec-proper-base-change/new-geometric-point-morphism-addcommgrp-stalk.json`.

No change record is needed: no existing signature, definition or public import changed.

## Second reading by G2

1. Compared the delivered target with the repository using `diff -u`: only proof
   imports and the proof body changed. Its declaration signature is byte-for-byte
   unchanged, and its existing docstring is unchanged. No other existing Lean
   module is delivered. Verdict: pass.
2. All four delivered modules compile through `lcompile.py --all` without errors
   or warnings. The only textual sorry is the whole proof of the named category
   equivalence theorem; no forbidden declaration mechanism or hollow definition
   occurs. Explicit `#print axioms` on a scratch copy lists only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` for all four declarations.
   The latter comes from the remaining geometric equivalence. Verdict: pass as
   a decomposition, not as a completed axiom-free proof.
3. The three statements are exactly the three strict conjuncts, with no added
   hypotheses. Only the first is left open. Its field-embedding proof was checked:
   algebraicity of étale residue extensions ensures that lifts factor uniquely
   through the algebraically closed subfield. Checked the identity morphism case
   by a scratch Lean proof independent of the open theorem; empty étale objects
   have empty lift sets, and empty/zero stalks satisfy the colimit argument.
   Non-surjective field embeddings are allowed and no IsIso assumption on a is
   used. Repeated leanfinder, loogle and grep searches with field-extension/lift
   and colimit-comparison queries; inspected Mathlib Point.Basic, Elements,
   Limits.Final, EtalePoint, and searched both library roots. Found and used the
   generic Mathlib colimit APIs; found no direct geometric-equivalence theorem.
   A leansearch query was attempted but its service returned Internal Server Error;
   this unavailability is recorded without a mathematical verdict in each node.
   Verdict: pass after closing the two stalk holes and fixing the docstrings.
4. The proof now isolates the geometric step and uses the shortest general
   categorical comparison for the stalks, instead of separate new holes.
   Imports needed only for proofs use plain import. Pruning is listed above.
   Read `dag/units/sk-thm-p1.json` and its realized route; neither this item nor
   the removed leaf is a realized unit step. The chapter/unit route is retained.
   Verdict: pass.
5. Read each delivered node against its Lean declaration. The existing node's
   proof dependencies now name the actual three components. The new nodes have
   self-contained statements, source, search records, creation records, matching
   Lean records, and the item's chapter/unit; their proof-dependency unions are
   exact and no longer circular. Blueprint origins refer to this item's actual
   steps. Verdict: pass after metadata repair.

Second reading changed: proved the set and additive stalk components, supplied
full component docstring proofs, removed the unused SpecFieldPointResidueField
import, repaired circular DAG dependencies and copied blueprint origins, updated
the target node, and corrected the report's hole accounting.
