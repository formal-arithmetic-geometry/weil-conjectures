## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.AffineChartDirectedRingModel` with
an unchanged-signature proof from two independent geometric parts of its existing plan.
Added proof-only imports of `Sheaf.AlgebraicGeometry.AffineOpenDirectedRingSystem` and
`Sheaf.AlgebraicGeometry.AffineChartTensorComparison`. The original public imports remain
because they supply the original statement's scheme, étale, pullback, colimit and tensor API.

The first new theorem constructs spectrum presentations for the base open and its inverse
images, compatible with the initial ring, stage maps and colimit coprojection. It contains
no chart morphism. The second constructs a finitely presented chart algebra map and,
for any compatible affine base open, an arrow isomorphism between the restricted chart
morphism and its tensor-product spectrum map. It contains no inverse system or limit,
and does not assert étaleness. These are respectively steps 1–2 and steps 1/3 of the
original argument; neither is the original conclusion under another name.

The assembly applies the second theorem first to the colimit presentation and then to
every stage presentation. A fully proved private helper uses Mathlib's `postcomp_iff`
and `arrow_mk_iso_iff` to transfer étaleness along the target-chart open inclusion and
the arrow isomorphism. The stage clause uses the reverse implication of this equivalence.
Updated the original node's proof, proof dependencies and proof origin to describe this
actual assembly. No existing statement, definition, target or unit record changes.

## Proved and sorry left

Proved `AlgebraicGeometry.exists_affineChart_directedRingModel`
(node `lem-weil-pbc-affine-chart-directed-ring-model`) from the two new statements.
Also proved the private helper `AlgebraicGeometry.etale_iff_of_chart_factorization`.
There is no sorry left in the item's module.

The only sorries added by this delivery are:

- `AlgebraicGeometry.exists_affineOpen_directedRingSystem`
  (`lem-weil-pbc-affine-open-directed-ring-system`, new module
  `Sheaf.AlgebraicGeometry.AffineOpenDirectedRingSystem`).
- `AlgebraicGeometry.exists_affineChart_tensorComparison`
  (`lem-weil-pbc-affine-chart-tensor-comparison`, new module
  `Sheaf.AlgebraicGeometry.AffineChartTensorComparison`).

Each has exactly `:= by sorry`, a source, a complete natural-language proof in its
docstring, and a matching node. All three modules compile together with no warnings.
This is a reduction, not an axiom-free closure of the original theorem: the two new
geometric theorems remain proof items.

## No longer needed

No module or transitive proof ingredient is pruned, and no original import is removed.
The original statement needs its public imports; the two added imports serve only its proof.
The following old direct proof dependencies are no longer used directly by the assembly;
they are retained in the two new geometric nodes (so they must not be removed from the
transitive DAG closure):

- `pqf-def-affine-morphism`
- `lem-weil-pbc-affine-open-spec-points`
- `lem-weil-pbc-morphism-into-affine-scheme`
- `lem-weil-pbc-lfp-affine-opens-finite-presentation`
- `lem-weil-pbc-limit-cone-affine-projections-opens`
- `lem-weil-pbc-spec-colimit-limit`
- `def-weil-pbc-category-colimit`
- `def-pc-fibre-product`
- `lem-weil-pbc-open-fibre-product`
- `lem-weil-pbc-fibre-product-affine-spectra`

The étale composition/cancellation node remains a direct dependency. The new ring-system
statement imports affine morphisms and ring colimits; it does not import the larger
affine-transition limit module merely to state its conclusion.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The module's original imports provide Mathlib ingredients,
rather than declarations implementing its full multi-step affine reduction; there is no
existing library theorem directly assembling these exact comparison squares. Searches
found `isLimitOpensCone`, `pullbackSpecIso`, and `arrowIsoSpecΓOfIsAffine` as ingredients.
The diagram reindexing/limit comparison and the open-pullback/tensor naturality comparison
are the substantial glue now explicitly isolated, with all their compatibility hypotheses.

Checked the new statements against empty base opens and empty source/target charts:
zero coordinate rings and their tensor products give empty spectra, so the statements
remain valid. The ring-system statement does not need compactness of the original
schemes, since the restricted stages are affine. An arbitrary preorder causes no issue:
its upper-tail opposite is equivalent to the over category even without antisymmetry,
and i₀ supplies nonemptiness. The chart comparison requires the displayed square over
Spec R; arbitrary incompatible algebra structures would not suffice, so this hypothesis
is retained explicitly.

Read Stacks 01YX, 01YW, 01JR, 01I4, 01TQ and the affine-reduction proof of 07RP
from the local Stacks source copy. The item is not in `dag/units/sk-thm-p1.json`'s
`realized` lists. This splitting changes no step or statement of that unit and keeps
all the existing argument's geometric ingredients. No change record is needed.

## New nodes

`lem-weil-pbc-affine-open-directed-ring-system`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-open-directed-ring-system.json`,
Lean module `Sheaf.AlgebraicGeometry.AffineOpenDirectedRingSystem`. It isolates the
base-open diagram and compatible spectrum presentations, including the limit comparison.
Its source is Stacks 01YX/01YW; its proof dependencies are the existing affine-open,
affine-projection and Spec-colimit lemmas. The statement and complete proof are also
in the Lean docstring. Actual LeanFinder, Loogle and grep searches are recorded, together with an unavailable
LeanSearch attempt (HTTP Internal Server Error).

`lem-weil-pbc-affine-chart-tensor-comparison`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-chart-tensor-comparison.json`,
Lean module `Sheaf.AlgebraicGeometry.AffineChartTensorComparison`. It isolates construction
of the fixed finitely presented algebra map and its uniform geometric arrow comparisons.
Its source is the open/affine fibre-product formulas 01JR/01I4 and finite presentation
on affine opens 01TQ, filling the affine reduction omitted in 07RP. Its dependencies
are the existing chart-coordinate, finite-presentation and fibre-product nodes.
Actual LeanFinder, Loogle and grep searches are recorded, together with an unavailable
LeanSearch attempt (HTTP Internal Server Error). No change records were added.

## Second reading by V2

1. **Unchanged interface — pass.** Read the diff of the existing module against the
   repository: its existing theorem signature and docstring are byte for byte unchanged.
   Only two plain proof imports, a private proved helper and the replacement proof are
   added. The existing node differs only in `proof`, `proof_deps` and `proof_origin`.
   No existing definition, target, unit or public import changes; no change record is needed.
2. **Kernel proof and axioms — pass as a reduction.** Compiled all three modules locally
   in import order, with no errors or warnings. Explicit `#print axioms` on a scratch copy
   checked the original theorem, both new theorems and the private helper. The helper uses
   only `propext`, `Classical.choice`, `Quot.sound`; the other three additionally use
   `sorryAx`, accounted for by the two named open lemmas. There are exactly two literal
   `sorry`s, both in the reported public theorems with source/proof docstrings and nodes.
   No forbidden declaration or hollow definition occurs. The étale equivalence has the
   correct orientation, and the stage clause uses its reverse implication.
3. **Split statements — pass.** Read both Lean signatures clause by clause against their
   nodes and proofs, and read the cited arguments in `/home/ubuntu/c1-stacks-review/`
   (`limits.tex`, `schemes.tex`, `morphisms.tex`). The ring-system statement concerns only
   the base open; the tensor statement concerns one fixed chart with arbitrary compatible
   affine base change. Neither restates the item. Checked the empty base/source/target
   opens, the singleton index system, and a preorder with equivalent distinct indices.
   The compatibility square in the tensor lemma fixes the required algebra structure.
   Independently searched LeanFinder for naturality of the affine spectrum equivalence
   and for sections on inverse-image opens in a cofiltered limit; Loogle for Spec/colimit
   and Spec/pullback maps; and grep for spectrum naturality, connected pullback limits,
   and tensor/pullback comparisons, plus `rg` on both source roots. Found ingredients
   (`pullbackSpecIso`, `isPullback_SpecMap_of_isPushout`, `isLimitOpensCone`, spectrum
   naturality), no exact combined theorem. Neither open statement has a short closure
   from one of these ingredients: diagram reindexing and compatible pullback transport
   remain substantial proof work.
4. **Shortest route, imports and unit — pass after report correction.** The item combines
   the two independent geometric constructions and Mathlib étale composition/cancellation
   and arrow invariance. Its public imports supply signature syntax/classes/instances;
   the new lemma imports are correctly plain. Inspected `dag/units/sk-thm-p1.json`:
   the item is not a realized unit statement or step, and no unit route is bypassed.
   Corrected `No longer needed` to enumerate every replaced old direct proof dependency
   while explaining that all remain needed transitively; no node/module is pruned.
5. **DAG agreement — pass.** The existing node describes the actual Lean assembly.
   Both new nodes include their complete statements, sources, proof steps, search records,
   creation/provenance, chapter/unit and verbatim Lean signatures. For all three nodes,
   `proof_deps` equals the union of proof-step `uses`. Checked every referenced dependency
   against its existing Lean declaration or Mathlib match. The new open proofs specify
   the natural spectrum presentations, algebra transport and projection equalities needed
   to prove the signatures, without assuming the original étale conclusion.

Changes by the second reader: corrected and completed the dependency accounting in
`No longer needed`, and added this independent review. The Lean proofs and node records
required no repair. Scratch axiom-check files are excluded from the delivery.
