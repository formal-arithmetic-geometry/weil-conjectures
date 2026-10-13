## What changed

Replaced the hole in `AlgebraicGeometry.coherentFormalModule_affine_limit_model` with
an unchanged-signature proof. It constructs the local comparison using uniqueness
of limiting cones, proves naturality by checking every projection, and composes
that comparison with a termwise restriction comparison.

Added three modules, each with one public theorem and a matching node:
`CoherentFormalModuleAffineLimitComparison`,
`CoherentFormalModuleAffineLimitEquivalence`, and
`CoherentFormalModuleAffineSpecTransport`, all under `Sheaf.AlgebraicGeometry`.
The first two are proved. Only canonical affine Spec transport remains a hole.
The equivalence theorem uses the existing `coherentFormalModules_affine`,
postcomposes its cones with the transported section comparison, transports their
universal property, and proves projection naturality from the two supplied
naturality equations. The restriction comparison constructs real linear maps
from `restrictAppIso` and equality-induced presheaf transport, including its
scalar equation and naturality.

Updated the original node's proof and dependencies and added the three nodes.
The blueprint unit route stays unchanged. No existing interface, definition,
target signature, or other group's module is changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.coherentFormalModule_affine_limit_model`
(node `lem-weil-pbc-formal-affine-limit-model`). No hole remains in the item.

Also proved the new declarations
`AlgebraicGeometry.coherentFormalModule_affine_limit_comparison`
(node `lem-weil-pbc-formal-affine-limit-comparison`) and
`AlgebraicGeometry.coherentFormalModule_affine_limit_equivalence`
(node `lem-weil-pbc-formal-affine-limit-equivalence`).

Added exactly one hole:
`AlgebraicGeometry.coherentFormalModule_affine_spec_transport`
(node `lem-weil-pbc-formal-affine-spec-transport`). Its proof is exactly `:= by sorry`.
It concerns only geometric transport and section diagrams, with no completed ring,
finite completed module, limit, or global restriction functor in its conclusion.
This is a decomposition: one original hole closed, one strictly lower hole added,
net zero holes. Existing holes reached through `coherentFormalModules_affine` remain
in their existing modules and are not altered or added by this delivery.

The remaining theorem was checked on empty V, J=0, and J=A: the canonical affine
isomorphism, ideal extension, restriction and scalar transport remain valid in
all cases. Its docstring supplies the ideal calculation, termwise functors,
unit/counit construction, and natural scalar-compatible section comparison.

All four modules compiled in import order with no warnings using `lcompile.py`.
No data is defined by choosing an arbitrary witness of an unproved existence
statement. The local uses of transport concern section diagrams determined up
to the natural isomorphism provided in its statement, and the existing affine
cones determine the underlying completed module up to the equality used here.

## No longer needed

Removed direct proof-only imports of
`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine` and
`Sheaf.AlgebraicGeometry.FormalSystemsPullback` from the item. The first is used
in the new equivalence theorem; the second is retained in the transport module
for its stated proof. Neither node nor module is globally pruned: their content
is still needed below this decomposition. All four former direct proof dependencies are accounted for:
`def-weil-pbc-coherent-formal-module` remains a definition dependency and is used
in the transport plan; `lem-weil-pbc-formal-systems-pullback` moves to the transport
plan; `lem-weil-pbc-coherent-formal-modules-affine` moves to the proved equivalence;
`lem-weil-pbc-coherent-formal-modules-restriction-objects` moves to the comparison
and remains necessary for the restriction functor in the original statement.
The main node's direct proof dependencies are now the proved local-equivalence
and restriction-comparison nodes. Definition dependencies remain unchanged.

Second reading removed unused `Mathlib.Algebra.Category.ModuleCat.Limits` and
`Mathlib.RingTheory.AdicCompletion.Algebra` imports from each of the new comparison
and Spec-transport modules. The new equivalence module now publicly imports
`Sheaf.AlgebraicGeometry.CoherentFormalModule` instead of the unnecessary
`Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects`. These changes
prune redundant direct imports, not any globally reachable module.

## Where the brief, the DAG or earlier work was wrong

The original affine theorem already contains natural limiting cones, so no new
completion theorem or inverse-limit theorem is needed. The existing
`coherentFormalModules_iso_equivalence` gives only an abstract equivalence, with
no inclusion equation or section comparison in its public statement; it cannot
supply the natural affine model by itself. The remaining transport node records
precisely the additional functor-level information required by original steps
1 and 2. The compiled proof realizes original steps 3 and 4.

The cited local `literature/stacks-project/coherent.tex` was not present in this
clone. Read the official [087W](https://stacks.math.columbia.edu/tag/087W) and
[087X](https://stacks.math.columbia.edu/tag/087X) pages instead; the transport
argument is explicitly recorded as written by R1 from their affine-reduction
step and the existing formal pullback construction. LeanSearch returned an
internal server error, recorded as unavailable. Loogle, LeanFinder, Mathlib grep,
source-library grep, and blueprint searches were performed and recorded.

## New nodes

`lem-weil-pbc-formal-affine-spec-transport`: the remaining geometric part of
original steps 1 and 2, including the scalar-compatible diagram comparison.
It has no completion or limit assertion. Its generic pullback-composition
node `lem-pc-module-pullback-identity-composition` is a tool already used by the
existing isomorphism-equivalence proof; it does not replace a unit-level step.

`lem-weil-pbc-formal-affine-limit-equivalence`: original step 3, proved by
composing transport with the existing affine completed-module equivalence and
transporting its natural limiting cones.

`lem-weil-pbc-formal-affine-limit-comparison`: the restriction/sections part of
original step 4, proved from explicit linear section isomorphisms and presheaf
naturality. The remaining uniqueness-of-limits part is proved in the item.

All node files are under `dag/nodes/sec-proper-base-change/`. No change record
is necessary: existing signatures and visibility are unchanged.


## Second reading by R1

1. PASS: Compared every delivered module with the read-only repository. Only the
   original module exists there; its theorem signature is byte for byte unchanged,
   as is its docstring, and its existing public imports remain unchanged. The
   other three modules are new. No definition, target statement, hypothesis or
   conclusion of an existing declaration changed; no change record is required.

2. PASS, relative to open dependencies: Independently compiled all four modules
   in import order with `lcompile.py`, both before and after import cleanup.
   There is exactly one explicit `sorry`, in the named public Spec-transport
   theorem, whose entire proof is `by sorry`. No prohibited declarations or
   attributes occur, and the private section-isomorphism definition constructs
   actual additive and linear equivalences without a hole. Scratch-copy
   `#print axioms` checks on all four public theorems showed only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`; the private `sectionsIso`
   showed only the three permitted axioms. The latter holes are inherited from
   open declarations, including the explicitly reported transport theorem;
   this delivery does not claim an axiom-free completed target. Existential
   elimination takes place inside theorem proofs, not in a new definition
   choosing arbitrary data from an unproved existence statement.

3. PASS: The sole new open statement is affine Spec transport with a natural
   section-diagram comparison. Its conclusion contains no completion, limiting
   cone or section-limit functor, so it is strictly below the original item,
   rather than its conclusion renamed. Its named docstring and node give the
   ideal calculation, termwise pullback functors, inverse comparisons and linear
   section comparison. Checked the direction of the scalar maps against
   `IsAffineOpen.isoSpec_inv_appTop`, `ideal_comap_of_isOpenImmersion`, and the
   definition of `moduleSpecΓFunctor`. For empty V all rings and modules are
   zero; for J=0 isomorphism pullback preserves the ordinary coherent towers;
   for J=A all formal terms are zero. None of the constructions assumes a
   proper ideal or a nonempty spectrum. Re-read the official Stacks
   [087W](https://stacks.math.columbia.edu/tag/087W) and
   [087X](https://stacks.math.columbia.edu/tag/087X) sources. Repeated independent
   LeanFinder, Loogle and Mathlib grep searches with different queries and
   searched both project and upstream sources. Existing
   `coherentFormalModules_iso_equivalence` lacks its functor/section comparison;
   the existing affine equivalence and Mathlib cone-transport lemma are already
   used. No duplicate statement or shorter ready-made proof was found.

4. PASS after cleanup: Read the proof from the target downward. The original
   natural isomorphism follows by uniqueness of limiting cones, naturality on
   projections, and the explicit termwise restriction isomorphism. The new
   equivalence transports the existing affine cones; it introduces no further
   completion theorem. Removed unused imports from the new modules and replaced
   the equivalence's unnecessarily broad public restriction import. The revised
   No longer needed section accounts for every old proof dependency, including
   those moved into the new modules. No module is globally pruned. Read
   `dag/units/sk-thm-p1.json`, including `realized`: none of its realized nodes
   or steps is bypassed or changed, and the original affine route is realized
   by the decomposition.

5. PASS: The existing node differs only in `proof`, `proof_deps` and
   `proof_origin`. Its recorded Lean statement is unchanged (its pre-existing
   formatting is a single line). Each new node's Lean statement agrees verbatim
   with its theorem, has source, provenance, search records, creation record,
   blueprint origin, chapter and unit, and the union of its proof-step uses
   equals its `proof_deps`. Read the dependencies' Lean declarations and checked
   the DAG route against the actual cone and section-comparison proofs.

Second reading changed only redundant imports in the three new modules and
expanded the dependency and review documentation. No proof body, existing
signature, definition, new statement, or DAG proof route needed repair. One
original hole is closed and one strictly lower hole is added: decomposition,
net zero holes, with two additional proved intermediate declarations.
