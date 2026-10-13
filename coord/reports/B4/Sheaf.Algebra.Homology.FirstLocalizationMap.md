## What changed

Replaced the sole proof hole in
`RingTensorCohomology.exists_firstLocalization_iso` with a complete Lean reduction.
The statement, universes, visibility, definitions, and existing docstrings are unchanged.
Added the proof-only import
`Sheaf.Algebra.Homology.FirstLocalizationCohomologyBaseChange` and the proved private
helper `extendScalars_eqToIso_one_tmul` for transport of extension generators across
an equality of coefficient ring maps.

The proof obtains the cohomology localization isomorphism over `Aq ⊗[R] B` from
the new intermediate theorem. It proves, by tensor induction and the five given
scalar towers, that the induced map `A ⊗[R] B → Aq ⊗[R] B → D` is the original
map to D. Equality transport, `ModuleCat.extendScalarsComp`, and extension of the
intermediate isomorphism then construct the required D-linear isomorphism.
The equality-transport helper, the associativity generator formula, and
`ModuleCat.ExtendScalars.map_tmul` prove its exact required generator formula.

Updated the item's node proof and dependencies to this reduction. The new node
contains the remaining cohomology step and keeps the balanced-model and exact
localization route of the original plan. No realized unit step is bypassed:
`dag/units/sk-thm-picard-semicon.json` has no realization bindings for this node.

Validation: both sandbox modules compile in dependency order through lcompile.py
with no warnings. The clean run took 5.6 seconds for the lower statement and
9.8 seconds for the item. An earlier dependent rewrite exhausted heartbeats; the
final proof uses explicit equations instead, without raising compiler limits.

## Proved and sorry left

Closed the existing hole in `RingTensorCohomology.exists_firstLocalization_iso`
(node `lem-pc-first-localization-map`). No sorry remains in the item's module.

Added one hole, the whole proof of the public theorem
`RingTensorCohomology.exists_firstLocalization_cohomology_baseChange`
(node `lem-pc-first-localization-cohomology-base-change`), in its own new module
`Sheaf.Algebra.Homology.FirstLocalizationCohomologyBaseChange`.
It has its source and complete natural-language proof in the docstring and node.

This is a decomposition, not a sorry-free proof: one upper hole closed and one
lower hole added, net zero. The strictly smaller remaining step is cohomology
localization over the tensor coefficient ring, before any extension to D. It
neither assumes the five compatibility towers to D nor asserts the upper
D-linear isomorphism. The compatibility and final extension steps are real
proved Lean code, not another statement of the upper theorem.

## No longer needed

No existing import was removed. No module or mathematical dependency was pruned.
The item's direct proof dependencies on `lem-pc-balanced-derived-tensor-model`,
`lem-pc-derived-tensor-action-naturality`, `lem-weil-pbc-localization-flat`,
`lem-weil-pbc-localization-module-exact`, and
`lem-weil-pbc-localization-tensor-product` move to the new lower node; they remain
needed there. They are not claimed as globally pruned. The two existing
statement-module imports and the localization import remain for statements.

## Where the brief, the DAG or earlier work was wrong

The original plan does not directly provide a Lean declaration comparing
arbitrary BaseDerivedTensorCohomologyModel instances under first-factor
localization. The existing balanced-model and action-naturality declarations
provide tensor computations and actions but not this exact comparison. The new
node states this missing cohomology step explicitly, with the counit-compatible
model comparison fixed rather than an unspecified isomorphism.

Read the existing dependency nodes, their Lean signatures, and the unit record.
Read Stacks Tags 06Y6 and 0DJ8 through their public pages because this clone holds
only the literature index, not the fetched documents. Sources:
https://stacks.math.columbia.edu/tag/06Y6 and
https://stacks.math.columbia.edu/tag/0DJ8 (the affine localization identity in its proof).
Searches through msearch found generic module localization and scalar-extension
lemmas, not an exact derived cohomology comparison. LeanSearch returned an internal
server error, recorded as unavailable. A blueprint search found no exact duplicate.

Edge cases checked in the new statement: identity localization leaves the unique
model comparison; zero in S makes Aq and its tensor coefficient ring zero, so both
modules in the intermediate isomorphism are zero. No faithful localization,
flatness of D, flatness of A over R, boundedness, or K-flatness of Q is assumed.
No data are chosen by a new definition from the holed theorem; its witness is
used only inside the proof of the original existence theorem.

## New nodes

`lem-pc-first-localization-cohomology-base-change`, at
`dag/nodes/sec-picard-framework/lem-pc-first-localization-cohomology-base-change.json`,
states the cohomology localization isomorphism over `Aq ⊗[R] B`, with its exact
unit/counit generator formula. Its Lean theorem is in
`lean/Sheaf/Algebra/Homology/FirstLocalizationCohomologyBaseChange.lean`.
Its proof uses the original balanced-model, scalar-action, and exact-localization
steps. It is strictly the cohomology step of the argument; final coefficient-map
compatibility and extension to D have been proved in the original module.
No existing interface changed and no change record or forced adaptation is needed.

## Second reading by B4

1. PASS: compared the delivered item with the repository using diff and the
   declaration parser. Every existing signature, universe, visibility, definition,
   and docstring is byte-for-byte unchanged. Only the proof-only import, a private
   proved helper, and the existing theorem proof were added. There are no forced
   adaptations or interface changes requiring a change record.
2. PASS as a decomposition: both modules compiled locally in import order, with
   no errors or warnings. The item has no sorry; the new module has exactly the
   one named theorem listed above. No axiom, unsafe, opaque, implemented_by, extern,
   or holed definition was introduced. A scratch copy with #print axioms checked
   firstLocalizationUnit, firstLocalizationCohomologyMap, IsFirstLocalizationMap.ext,
   exists_firstLocalization_iso, the lower existence theorem, and the private
   equality-transport helper. Only propext, Classical.choice, Quot.sound occur,
   plus sorryAx in the two existence theorems. The private helper has no sorryAx.
3. PASS: the new statement isolates cohomology localization over Aq tensor_R B;
   it omits the five D-compatibility towers and the final extension to D. The
   upper proof genuinely proves those remaining compatibility and extension steps.
   Its exact generator formula prevents arbitrary model-comparison choices.
   Checked identity localization, zero in S, the zero complex, and the nonflat
   second factor R=A=Z, B=Z/p with p inverted in Aq: both localized cohomologies
   vanish, without assuming B flat. Inspected the model's universal counit and
   cohomologyIso_smul to verify that arbitrary supplied models have the required
   coefficient action. Independently searched leanfinder for flat base change of
   unbounded derived tensor cohomology, loogle for IsLocalization and TensorProduct,
   and grep for mapHomologyIso, flat scalar extension, and tensorProduct_tensorProduct.
   Also searched repository Sheaf and upstream homology modules. The matches are
   generic exactness and tensor-localization tools, not this model comparison;
   downstream localization results already depend on this item and cannot replace
   it. Re-read Stacks Tags 06Y6 and 0DJ8. The new theorem has its source, complete
   proof docstring, and matching node; it is not a renamed restatement of the item.
4. PASS: followed the proof from the upper existence theorem downward. Tensor
   induction establishes equality of ring maps; equality transport and Mathlib's
   extendScalarsComp give the isomorphism; map_tmul and the lower generator formula
   give its characterization. Imports are for signatures or the one used proof
   theorem. No existing import was removed. The five old direct proof dependencies
   listed under No longer needed are absent from the upper node and retained in
   the lower plan, so no global pruning is claimed. The unit's realized statement
   and step arrays are empty; no realized unit route is bypassed. Closing the
   remaining derived comparison requires substantial construction, not a short
   application of a found lemma; one hole closed and one added remains net zero.
5. PASS after documentation repair: the existing node changes only proof,
   proof_deps, and proof_origin. Both Lean statement strings are verbatim, and
   each proof_deps is exactly the union of the proof steps' uses. The new node
   contains the required source, searches, creation, blueprint, chapter, unit,
   status, and Lean fields. Its proof agrees with the stated reduction.

Second reading changed the lower theorem's proof docstring and new node's first
proof step to explain the B-action correctly: an arbitrary R-K-flat resolution
of B need not carry a strict B-action. Multiplication on B[0] acts through the
balanced derived bifunctor; transport through the K-flat computation and
naturality identify the coefficient action and its compatibility with localization.
No Lean proof, signature, definition, import, or hole count was changed.
