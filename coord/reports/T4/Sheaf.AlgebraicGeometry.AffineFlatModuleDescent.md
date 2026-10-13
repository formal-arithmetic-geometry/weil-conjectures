## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.exists_eventually_flat_of_finitePresentation`
(`Sheaf.AlgebraicGeometry.AffineFlatModuleDescent`) by a complete Lean proof from two
separate intermediate theorems. The original signature and visibility are unchanged.
The proof obtains a flat finite-presentation model at the limit, compares this model
with every sufficiently late prescribed stage, installs the model's flatness, and
uses `Module.Flat.baseChange` through instance synthesis and
`Module.Flat.of_linearEquiv` to transport flatness to the prescribed module.

The two new modules are `Sheaf.RingTheory.FlatModuleTensorModel` and
`Sheaf.RingTheory.FpModuleTensorModelComparison`. Their statements separate the
original DAG's steps 1–7 from step 8. The comparison theorem assumes no flatness;
the flat-model theorem mentions no directed system or eventual stage. Thus neither
new statement is the original eventual-flatness theorem with its hypotheses repackaged.
No object is defined by choosing an arbitrary witness of an unproved existence theorem:
all model witnesses are eliminated locally inside a proposition proof.

The original node now records the three actual steps: flat model, comparison,
and tensor base change followed by linear-equivalence transport. Each new node
records its own proof dependencies, source and complete proof plan.

Validation: all three delivered modules compile together with the prescribed
`lcompile.py --all` command. The two holes below are intentional whole public theorem
proofs; the original module has no hole.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.exists_eventually_flat_of_finitePresentation`
(node `lem-pc-affine-flat-module-descent`). This is a decomposition, not a
sorry-free proof of the mathematics.

Added 2 holes, one public theorem in each new module:

- `AlgebraicGeometry.exists_flat_module_tensor_model`
  (node `lem-pc-flat-module-tensor-model`, module
  `Sheaf.RingTheory.FlatModuleTensorModel`): the flat model and its compatible
  algebra and module base-change isomorphisms, Stacks Tag 02JO (1).
- `AlgebraicGeometry.exists_eventually_tensor_model_equiv`
  (node `lem-pc-fp-module-tensor-model-comparison`, module
  `Sheaf.RingTheory.FpModuleTensorModelComparison`): finite-presentation descent
  of the two comparison isomorphisms, Stacks Tag 02JO (3), final paragraph.

No `sorry` remains in the item's module. Net direct holes in this delivery:
1 closed minus 2 added = -1. The report makes no claim of a positive ledger net.

The new statements were checked on these edge cases:

- Zero module: take the zero model module L; both tensor modules are zero,
  and flatness is automatic. The algebra model still has to be descended.
- Zero top algebra: its module is zero. A zero model top algebra and zero L
  satisfy the comparison requirements; no nontrivial-ring assumption is needed.
- Zero limit coefficient ring: the limit modules are zero. In the comparison
  argument a finite unit relation, including 1 = 0 when necessary, descends.
  This avoids incorrectly inferring that an arbitrary existing stage is zero.
- Empty presentations: tensor cancellation and inverse identities still apply;
  there is a fixed index i, so an upper-tail starting index always exists.
- A directed preorder need not be antisymmetric. The arguments use common upper
  bounds and the unique preorder arrows, not antisymmetry. The existing module
  descent statement uses a partial order, so its future application must either
  pass to the poset reflection or use the corresponding categorical finite-
  presentation argument; the new comparison statement does not add antisymmetry.
- A constant diagram with its identity model has identity comparison maps and
  permits j0 = i. A nonflat model is also allowed by the comparison theorem:
  flatness is used only in the final proof in the item's module.

## No longer needed

The following direct proof imports were removed from the item's module and moved
under the intermediate theorem whose argument uses them:

- `Sheaf.Algebra.FinitePresentationColimit`
- `Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`
- `Sheaf.Paper.DirectedColimitBaseChangeElementwise`
- `Sheaf.RingTheory.ColimitCategoryFpAlgebras`
- `Sheaf.RingTheory.ColimitEventuallyFlat`
- `Sheaf.RingTheory.FilteredColimitAlgebrasUnderlyingModule`
- `Sheaf.RingTheory.FlatModuleAtPrime`
- `Sheaf.RingTheory.LimitModuleFinitePresentation`
- `Sheaf.RingTheory.OpenFlatLocus`

They remain reachable through the two new modules. None is claimed as pruned
from the targets' import closure. The original node's former direct proof
 dependencies have likewise been distributed to the new nodes; they remain
needed by the argument. No whole node or module is pruned. No unit statement
or realized proof step is bypassed.

The second reading also removed the unused public import
`Mathlib.RingTheory.RingHom.Flat` from the new comparison module, whose
statement and proof do not use flatness.

For completeness, these former direct `proof_deps` are no longer direct
dependencies of the item (they remain in the new nodes' statement/proof
dependencies, and no pruning from the target closure is claimed):

- `def-weil-pbc-category-colimit`
- `def-weil-pbc-finitely-presented-algebra`
- `def-weil-pbc-localization-at-prime`
- `lem-pc-affine-flat-module-local-criterion`
- `lem-pc-affine-sections-flat-over-base`
- `lem-pc-fp-module-base-change`
- `lem-pc-fp-module-map-descent-affine`
- `lem-sc-noetherian-finite-module-finite-presentation`
- `lem-weil-pbc-colimit-category-fp-algebras`
- `lem-weil-pbc-colimit-eventually-flat`
- `lem-weil-pbc-directed-colimit-base-change-elementwise`
- `lem-weil-pbc-filtered-colimit-algebras-elementwise`
- `lem-weil-pbc-filtered-colimit-algebras-underlying-module`
- `lem-weil-pbc-filtered-colimit-localization-at-prime`
- `lem-weil-pbc-filtered-colimit-modules-criterion`
- `lem-weil-pbc-filtered-colimit-rings-zero`
- `lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`
- `lem-weil-pbc-finite-presentation-base-change-composition`
- `lem-weil-pbc-finite-presentation-over-finite-type-algebra`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-finite-type-noetherian-finite-presentation`
- `lem-weil-pbc-flat-over-localization`
- `lem-weil-pbc-limit-module-finite-presentation`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-localization-tensor-over-base`
- `lem-weil-pbc-localization-tensor-product`
- `lem-weil-pbc-openness-of-flatness`
- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original statement was found. The planned local
flatness, Noetherian approximation and finite-presentation descent lemmas are
usable parts of the argument, but none of their existing statements supplies
the complete flat module model or the simultaneous algebra/module comparison.
The already stated ring-only model and stage-comparison results are insufficient
for arbitrary modules: flatness of M over A does not imply flatness of B over A.
Using the ring-only result would therefore introduce an unjustified hypothesis.

The local `literature/stacks-project/algebra.tex` is absent on this machine.
The source was read at https://stacks.math.columbia.edu/tag/02JO instead: part (1)
constructs the flat model, and the final paragraph of part (3) descends its
algebra and module comparisons. The nodes retain the project's canonical source
path and cite the verified tag, not an unverified TeX label.

LeanSearch returned HTTP 500 for both new statements and is recorded as
unavailable. Logged LeanFinder searches gave flat factorization, smooth-flatness,
and finitely presentable ring-map candidates, but no matching module-model theorem.
Logged Mathlib grep found no flat-model or model-stage theorem. The upstream
flat approximation code in `RelativeComponentFlatApprox` and
`Mathlib/RingTheory/Finiteness/Descent` was also read; its theorems concern the
ring module and do not cover the module M of this item.

## New nodes

`lem-pc-flat-module-tensor-model`:
`dag/nodes/sec-picard-framework/lem-pc-flat-module-tensor-model.json`, with module
`lean/Sheaf/RingTheory/FlatModuleTensorModel.lean`. This is the flat-model portion
of the original proof, independently of any prescribed directed system.

`lem-pc-fp-module-tensor-model-comparison`:
`dag/nodes/sec-picard-framework/lem-pc-fp-module-tensor-model-comparison.json`, with
module `lean/Sheaf/RingTheory/FpModuleTensorModelComparison.lean`. This is the
comparison-isomorphism portion, independently of any flatness hypothesis.

No change record is needed: no existing definition, theorem signature, public
import or visibility changed, and no other existing module was adapted.

## Second reading by T4

1. Pass: compared the only existing delivered module with the repository using
   `diff -u`; its declaration signature, docstring and visibility are byte for
   byte unchanged. Only proof imports and the theorem body differ. No existing
   definition or statement changes, and no change record is required.
2. Pass: all three modules compile using `lcompile.py --all`. Scratch copies
   with `#print axioms` for all three declarations give only `propext`,
   `Classical.choice`, `Quot.sound` and `sorryAx`. The latter comes from the
   two explicitly reported whole public theorem holes. No forbidden declaration
   form, partial sorry, definition or data construction was introduced. The
   existential witnesses are eliminated within a proposition proof, not chosen
   to define exported data.
3. Pass: independently read https://stacks.math.columbia.edu/tag/02JO. Part (1)
   applied to X=C tensor_R A, Y=C tensor_R B and T=Y tensor_B M gives the first
   statement; finite presentation of B over A and tensor cancellation verify
   its prerequisites. The final comparison paragraph, without its subsequent
   use of flatness, gives the second statement. Both are strictly separate
   parts of the argument, not renamed versions of the original item. The
   zero-module, zero-ring and constant-system cases satisfy these statements;
   i supplies a nonempty cofinal tail, and directedness supplies finite common
   upper bounds without antisymmetry. Both holes have source-backed docstrings
   and exact matching node statements. Fresh logged LeanFinder queries on
   Noetherian module approximation and eventual isomorphism descent, a Loogle
   query on Module.FinitePresentation and Module.Flat, and repository searches
   found no theorem closing either hole directly. The flat-ring model and
   RelativeComponentFlatApprox specialize to the top ring and cannot replace
   the general module result. Neither hole can be closed in a few minutes.
4. Pass: the proof opens the original target hole, separates flat approximation
   from finite-presentation comparison, and finishes with Mathlib tensor
   flatness and linear-equivalence transport. The old proof imports remain
   under the corresponding new statements, and every removed old direct
   proof dependency is now explicitly listed above. No module is pruned from
   the target closure. Read dag/units/sk-thm-picard-semicon.json: its realized
   fields and the unit route are untouched; this reduction remains inside
   the existing affine descent argument. This is a decomposition, with one
   original hole closed and two holes added, not a sorry-free proof or positive
   ledger progress.
5. Pass: each node's proof_deps is exactly the union of its proof steps' uses.
   The existing node records the two actual theorem applications and tensor
   flatness transport. The new nodes' Lean signatures match the new files
   verbatim; source, creation, blueprint ancestry, unit/chapter and searches
   are present. The comparison node and docstring now explicitly explain the
   poset-reflection step needed to apply the existing PartialOrder module-map
   descent result to a directed preorder.

Changed in this reading: removed the unused public flatness import from the
new comparison module; expanded its docstring and node proof to explain
poset reflection; completed the list of former direct DAG dependencies in
this report. The original Lean proof and all theorem signatures are retained.
