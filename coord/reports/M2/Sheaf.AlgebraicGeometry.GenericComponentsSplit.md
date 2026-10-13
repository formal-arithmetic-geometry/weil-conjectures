## What changed

The signature of `AlgebraicGeometry.exists_finite_etale_geometric_component_extension`
in `Sheaf.AlgebraicGeometry.GenericComponentsSplit` is unchanged. Its proof now:

1. Uses Mathlib to show the pullback to `SeparableClosure k` is noetherian and has
   finitely many irreducible components.
2. Uses the new finite component-descent statement to obtain an intermediate field `L`.
3. Proves its spectrum map finite and étale using module finiteness, separability,
   `IsFinite.SpecMap_iff`, `Algebra.FormallyEtale.of_isSeparable`, and finite presentation
   over a noetherian field.
4. Applies the proved subset criterion to each component's irreducible inverse image.

The added proof imports are `Mathlib.AlgebraicGeometry.Noetherian`,
`Mathlib.RingTheory.Etale.Field`, `Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent`,
and `Sheaf.AlgebraicGeometry.SubsetGeometricIrreducibility`.
The two new modules each have one public theorem and their own DAG node.
The original node's proof, proof dependencies, and proof origin follow this argument.

The subset criterion is proved, including the pullback construction and set-image identity.
A private proved helper derives geometric irreducibility of a field spectrum map over a
separably closed field from `IsSepClosed.field_tensor_unique_minimalPrime`. For a test
field, `Field.exists_common_extension` supplies a common overfield. The comparison to the
separably closed base change is an explicit pullback lift; its pullback property follows
by pasting and cancellation. Geometric irreducibility and openness give irreducibility of
the subset inverse image. The surjective projection to the test base change then gives
exactly the desired subset as its continuous image.

All three modules compile without warnings through `lcompile.py --all`. No existing
module other than the assigned module was adapted, and no definition was added or changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_finite_etale_geometric_component_extension`
(node `lem-sbc-generic-components-split`) by reduction to finite component descent.
There are no sorries left in the assigned module.

Added one hole:
`AlgebraicGeometry.exists_finite_intermediateField_component_preimages`
(node `lem-sbc-components-finite-separable-descent`), in
`Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent`.
Its whole proof is `by sorry`, with the source and full argument in its docstring.
This statement only descends components over a fixed separable closure; it does not
assert irreducibility after arbitrary field extensions or that the spectrum map is
finite étale. Those parts are established by the delivered Lean proofs.

Proved the new theorem
`AlgebraicGeometry.isIrreducible_preimage_of_isSepClosed_extension`
(node `lem-sbc-subset-geometric-irreducibility`) in
`Sheaf.AlgebraicGeometry.SubsetGeometricIrreducibility`, and its private helper
`geometricallyIrreducible_field_specMap`, without new holes. This proof uses the existing
field-tensor theorem and common-extension theorem with their existing proof dependencies.
It is not claimed to remove any pre-existing holes in those imported dependencies.

Accounting: one upper hole closed and one lower hole added; this is a decomposition,
not a net decrease of holes. The geometric irreducibility step has a complete Lean proof.

## No longer needed

No existing import, node, or module is pruned: the original node had no proof dependencies
and the assigned module had only its two statement imports, both retained.
The reduced closed subscheme construction and its base-change identification from the
old prose plan are unnecessary: the subset criterion works for arbitrary subsets.
`Mathlib.AlgebraicGeometry.PullbackCarrier` was tested and removed as an unnecessary
explicit proof import from the new subset module; its required APIs are already imported.
No pruning of that module from the targets' import closure is claimed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old node provided a prose proof but no declared proof
steps to import, so the component descent step needed a new statement. Searches through
Mathlib, the source library, and DAG found no existing component-descent statement with
this interface. LeanSearch returned an internal server error; this is recorded as
unavailable, not as a negative result. LeanFinder, Loogle, and local searches ran, and the
local library search found the existing field-tensor and common-extension results used
in the proved subset criterion.

Read Stacks Tags 054R and 0551, then 04KZ (finite coefficient descent), 038I (testing over
separable closure), 054P (descent through a common extension), and 020J (separably closed
base). The finite-descent statement uses the actual local finite type hypothesis from
04KZ, with finiteness of components supplied separately by Mathlib. Its edge cases were
checked mathematically: an empty scheme uses the bottom intermediate field; nilpotents
do not affect the component subsets; several split components can be handled by one
compositum; and purely inseparable residue extensions do not require reduced base changes.
For the subset criterion, an empty subset cannot satisfy the nonempty irreducibility
hypothesis; the identity field extension is included; nonclosed subsets are allowed
because the argument uses open maps with geometrically irreducible fibres directly.
All fields, tensor products and common extensions stay in the requested universe.

The unit `sk-prop-normal-form` has empty `realized.statement` and `realized.steps` lists.
The assigned component-splitting step is retained, and no unit-level route is bypassed.

## New nodes

`lem-sbc-components-finite-separable-descent`:
`dag/nodes/sec-smooth-base-change/lem-sbc-components-finite-separable-descent.json`,
with `lean/Sheaf/AlgebraicGeometry/ComponentsFiniteSeparableDescent.lean`.
This is the single remaining descent obligation, sourced to Stacks 04KZ and 054R.
The conclusion is a component correspondence after one specified separable closure,
strictly one part of the original argument. Its finite-component hypothesis is proved
before applying it, rather than folded into a restatement of the assigned theorem.

`lem-sbc-subset-geometric-irreducibility`:
`dag/nodes/sec-smooth-base-change/lem-sbc-subset-geometric-irreducibility.json`,
with `lean/Sheaf/AlgebraicGeometry/SubsetGeometricIrreducibility.lean`.
This proved statement packages the common-extension and open-projection argument of
Stacks 054P, 020J and 038I for arbitrary subsets. Its proof dependencies are the existing
`lem-weil-pbc-field-tensor-irreducible` and `lem-weil-common-extension-fields` nodes.

No change records are needed: all existing signatures and visibility are unchanged.

## Second reading by M2

1. I compared the delivered `GenericComponentsSplit.lean` declaration with the repository
   version. The theorem signature is byte-for-byte unchanged; the added imports are proof
   imports except for the existing public finite and etale APIs.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile without
   errors or warnings. The only remaining `sorry` is the named descent theorem, and there
   are no forbidden declarations or sorries in definitions.
3. The two added statements were checked against their hypotheses and edge cases. The
   component descent statement is strictly the finite separable-closure descent subproblem;
   the subset criterion is exactly the irreducibility transfer needed by the target. Local
   searches found no existing declarations with either interface.
4. The proof follows the unit route: no unit statement or realized step is bypassed. The
   target proof first establishes noetherianity and finite components, then uses the finite
   descent node, and finally applies the subset criterion.
5. DAG node proofs, dependencies, origins, Lean declarations, and the report agree with
   the source. The descent node records its one remaining sorry and its complete source-based
   proof plan; the geometric-irreducibility node records the proved route and dependencies.

I changed only this second-reading report section after the first worker's delivery. No
   Lean source, node, or import was altered during review.
