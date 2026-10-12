## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.Modules.exists_proper_cohomology_finite_free_resolution`
with a complete Lean reduction. Its signature, including both `letI` binders in
`hpc`, is unchanged. The main proof evaluates the complex, proves its upper-bound
cohomology vanishing, applies the existing
`DerivedCategory.exists_finiteFree_model_isStrictlyLE`, and constructs an actual
quasi-isomorphism to its global-sections complex using Mathlib's K-projectivity,
`Qh_map_bijective`, fullness of the homotopy quotient and naturality of
`quotientCompQhIso`. Thus the ring-model step is implemented, not moved to a new hole.

The new module `Sheaf.AlgebraicGeometry.AffineSheafResolutionOfRingModel` states
only the remaining affine sheafification step. Its hypotheses explicitly include
an actual map `f : P ⟶ Γ(C)` and `[QuasiIso f]`. It neither assumes nor constructs
a pseudo-coherent ring model. The main theorem supplies these data from the
existing bounded finite-free model theorem and the completed lifting argument.
All data choices occur inside a theorem proof; no new definitions are introduced.

Updated the main DAG node's proof route and supplied a complete new sheafification
node with its actual Lean signature, sources, proof steps and search records.
Removed the obsolete sandbox ring-model node from the previous attempt: the
existing `lem-pc-pseudo-coherent-bounded-finite-free-model` suffices.

Replaced the public direct-image sections import with the Mathlib modules needed
by the statement. Added ordinary proof imports for the bounded finite-free model,
the new sheafification step, derived K-projectivity and module projectivity.
Both sandbox modules compile cleanly with `lcompile.py --all`, without warnings.
The unchanged direct importer `Sheaf.AlgebraicGeometry.ProperFlatCechModel` also
compiles against the sandbox overlay without warnings; it already explicitly
publicly imports all three removed modules. Its source is not delivered.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.exists_proper_cohomology_finite_free_resolution`
(node `lem-pc-proper-cohomology-finite-free-resolution`); no `sorry` remains in the
item's module. This is a decomposition, not a proof free of `sorryAx`.

Hole added: `AlgebraicGeometry.Scheme.Modules.exists_affine_sheaf_resolution_of_ring_model`
(node `lem-pc-affine-sheaf-resolution-from-ring-model`), in its own new module.
Its proof is exactly `:= by sorry`. This is the only new hole in the delivery.

Existing imported hole used, unchanged:
`DerivedCategory.exists_finiteFree_model_isStrictlyLE`
(node `lem-pc-pseudo-coherent-bounded-finite-free-model`).
The upper-bound transfer and actual chain-map lifting introduce no holes.

One upper hole closed and one strictly smaller hole added gives zero net holes
closed, before any pruning effect. The new statement is independent of
pseudo-coherence and handles only a supplied ring resolution; the nontrivial
construction of that resolution and its actual comparison map is in the main proof.

## No longer needed

Removed imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`.

None is needed for this affine resolution statement or its proof. In particular,
the direct-image sections machinery is not used; evaluation of the termwise zero
objects suffices for the bound. These imports are unnecessary along this edge;
no claim is made that they leave the entire target closure through other paths.

The previous attempt's proposed `lem-pc-affine-ring-finite-free-model` and
`exists_affine_ring_finite_free_model` are not delivered or needed: their work is
covered by the existing finite-free model theorem plus the completed Mathlib lift.
No original planned mathematical dependency is discarded: the finite-free model
and K-projectivity remain direct proof dependencies, and the tilde/Gamma
adjunction remains a dependency of the sheafification step.

## Where the brief, the DAG or earlier work was wrong

The previous report claimed a reduction absent from the reset main module. Its
node records had placeholder statements and proof text, and incorrectly pointed
both new declarations at the main module. Rebuilt the node metadata from the
actual statements and argument, and removed the obsolete second-reading section
from this first-worker report.

The earlier sheafification statement described by that second reading was false
because it omitted any relation between P and C. The retained sandbox version
already had the needed explicit quasi-isomorphism; this delivery checks and uses
that interface. Taking P=0 now entails that Γ(C) is acyclic, which on an affine
quasi-coherent complex makes C acyclic, so the previous counterexample no longer
applies. The zero ring and empty affine scheme have only zero modules/sheaves;
rank zero treats them. No positivity, nonzero-ring or lower-bound assumption is
added. A complex bounded above by d stays bounded above under both evaluation
and sheafification. Arbitrary negative degrees cause no problem.

Tag 08E7 is about pseudo-coherence under affine associated sheaves, not the
underived affine equivalence. Corrected docstring citations to the precise
[affine equivalence, Tag 01IB](https://stacks.math.columbia.edu/tag/01IB) and
[exactness of associated sheaf, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV).
The existing main node's source field is unchanged; the proof_origin records the
precise source of the implemented route.

The unit `sk-thm-picard-coherence` has no realized node bindings. This delivery
preserves its finite-free replacement route; it does not bypass a bound unit step.

## New nodes

`lem-pc-affine-sheaf-resolution-from-ring-model` states the transfer of a supplied
actual finite-free ring quasi-isomorphism to a finite-free sheaf resolution with
the same upper bound. Its module is
`lean/Sheaf/AlgebraicGeometry/AffineSheafResolutionOfRingModel.lean`; its node is
`dag/nodes/sec-picard-framework/lem-pc-affine-sheaf-resolution-from-ring-model.json`.
The proof specifies affine chart transport, naturality of the quasi-coherent
counit, exactness detected on localized stalks and preservation of finite free
objects. It is strictly the final step of the original plan. No existing
statement or definition is changed. Public import pruning is recorded in
`coord/changes/proper-cohomology-finite-free-resolution-imports.md`, with the
complete downstream user table. No forced adaptation is needed.

## Second reading by H1

1. I compared the delivered main module with the repository version. The existing
 theorem signature is byte-for-byte unchanged; the added affine module contains
 the new declaration recorded by its node.
2. Both delivered modules compile with `lcompile.py --all`; the only remaining
 `sorry` is the named split theorem
 `exists_affine_sheaf_resolution_of_ring_model`, and no forbidden declarations or
 hollow definitions occur.
3. The split statement includes the actual map and `QuasiIso` instance relating
 the ring complex to the evaluated sheaf complex. It is strictly smaller than the
 main target and its docstring, node, source, and proof steps agree. The affine
 edge cases described in the report do not weaken its hypotheses.
4. The proof uses the finite-free model and K-projective lifting route, then
 delegates only the final sheafification step. The three removed imports are
 unused by the proof and are recorded in the change record.
5. The node proof and `proof_deps` match the imports and theorem applications;
 the new node has the required metadata. The unit route is retained: the finite-
 free replacement node remains the main route, with the affine transfer as its
 final step.

I changed only this report section; no Lean statements or proofs required repair.
