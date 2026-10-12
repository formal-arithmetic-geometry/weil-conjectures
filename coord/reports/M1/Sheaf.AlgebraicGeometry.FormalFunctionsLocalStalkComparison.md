## What changed

Replaced the sorry in `AlgebraicGeometry.formalFunctions_local_stalk_comparison`
with a complete Lean reduction. Its statement and both existing definitions are unchanged.
The proof obtains the actual beta and its section formula from
`Scheme.Modules.flatBaseChangeMap_sections`. A resolution lift and the new
`Scheme.Modules.flatBaseChangeResolutionBeta_isIso` show this beta is invertible.
The new `localDerived_stalk_transport`, instantiated with `G = R^p f_*F`, transports
it to an equivalence on the original stalk. Applying its pointwise formula to the
source section class and using the existing section formula proves the required
predicate for every resolution and every open-comparison choice.

Added two new modules, one theorem each, and their nodes. Updated the original
statement node's proof, proof_deps and proof_origin. All new imports of the item
are ordinary proof imports. No definitions, existing signatures, targets or
visibility were changed, and no other existing module was adapted.

The local transport is strictly a part of the argument: it works for an arbitrary
module G and an arbitrary isomorphism beta, without properness or coherence, and
only asserts what happens to a section whose adjoint value is a specified target
class. It does not assert the flat-base-change section formula. The other new
lemma asserts invertibility of the actual resolution comparison on qcqs morphisms;
it does not construct or characterize the original stalk equivalence.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.formalFunctions_local_stalk_comparison`
(node `lem-weil-pbc-formal-functions-local-stalk-comparison`).
There are no sorries in the item's module.

Added two holes, each exactly `:= by sorry` in a new public theorem:

- `AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_isIso`
  in `Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionIso`, node
  `lem-weil-pbc-flat-base-change-resolution-iso`.
- `AlgebraicGeometry.localDerived_stalk_transport`
  in `Sheaf.AlgebraicGeometry.LocalDerivedStalkTransport`, node
  `lem-weil-pbc-local-derived-stalk-transport`.

This is a decomposition, not a sorry-free mathematical proof: one upper hole
closed and two lower holes added, a net of minus one before closure-ledger effects.
Both remaining statements have complete proof docstrings and source citations.
The edge checks include degree zero, the zero module, and empty base change.
For transport, no assumption on F beyond being a module is needed: evaluation
on a local spectrum is exact for all sheaves of modules. D.target.augmentation
and D.target.components pin its class map, so the statement does not quantify over
arbitrary unconstrained section-complex isomorphisms. For flat base change the
qcqs and quasi-coherence hypotheses are retained; no field or finite-dimensional
assumption is introduced.

## No longer needed

No original import was removed: all four original public imports support the
existing statements. No unit-level statement or step was bypassed.

The following old proof dependencies are no longer direct dependencies of the
item's proof, and are removed from its proof_deps:

- `lem-weil-pbc-localization-noetherian`: no separate proof that the local base is
  Noetherian is needed for flat base change or exact local evaluation.
- `lem-weil-pbc-module-pullback-finite-type`
  (`Sheaf.AlgebraicGeometry.ModulePullbackFiniteType`): no finite-type proof for F'
  is needed.
- `lem-weil-pbc-module-pullback-quasi-coherent`: no separate pullback-coherence
  argument is needed for this local comparison.
- `lem-weil-pbc-proper-fp-permanence`: the proof uses Mathlib's proper/qcqs and
  locally-finite-type instances, without a separate permanence theorem.
- `pqf-def-locnoeth` and `pqf-lem-locnoeth-lft`: the relevant Mathlib definitions
  and `LocallyOfFiniteType.isLocallyNoetherian` are already available.
- `lem-weil-pbc-module-cohomology-fmap-basic-properties` and
  `lem-weil-pbc-module-cohomology-fmap-functorial`: no separate scalar or
  composition calculation is used in the item.
- `def-weil-pbc-module-cohomology-fmap`, `def-weil-pbc-module-stalk`, and
  `lem-weil-pbc-higher-direct-image-presheaf` are no longer direct proof steps of
  the item; the first two remain statement support and the last remains in the
  proof plan of the local-transport lemma. This is not a claim of global pruning.

No whole-library module is claimed globally unreachable: other imports or targets
may still need these modules. The pruning here is of the item's stated direct route.

## Where the brief, the DAG or earlier work was wrong

The original node already notes that `lem-pc-flat-base-change-cohom` only gives a
field-extension finrank statement. It cannot show that the specific resolution
beta for Spec(O_y) → Y is invertible. The new 02KH node supplies precisely that
missing part. The source-library compact-separated comparisons inspected during
search use Ext-based cohomology and a different canonical comparison, and do not
state this O_X-module-derived sheaf isomorphism.

The two local identifications in 02OD require a canonical comparison on germs,
not only an abstract isomorphism of modules. The new local transport records that
comparison for arbitrary sections, with its target section-class hypothesis
separate from the flat-base-change formula already available in the library.

The separately composed stalk-to-sections and sections-to-cohomology experiment
caused excessive unfolding during equality normalization. The delivered transport
packages those two identifications into one geometric step. Using the explicit
`e.toLinearMap` in its formula avoids the expensive coercion normalization when
matching the unchanged predicate. Only the final two modules, not the discarded
experiments, are delivered. Local compilation of the final item takes about 52–54
seconds, within the prescribed 60-second limit.

## New nodes

`lem-weil-pbc-flat-base-change-resolution-iso` is Stacks 02KH part (1) for the
specific resolution-defined beta and every augmented lift. It retains qcqs and
quasi-coherence, and makes no assertion about local stalk identifications.

`lem-weil-pbc-local-derived-stalk-transport` isolates the local geometry of 02OD:
unit stalk identification, beta on stalks, exact closed-point/global evaluation,
and the canonical resolution class formula. It takes any G and any invertible
beta and supplies the conditional pointwise germ transport. Its mathematical
proof uses the existing higher-direct-image-presheaf and canonical-local-morphism
nodes. There are no change records because no existing interface changed.

## Second reading by M1

1. Compared the delivered module with the repository version. Existing theorem and definition signatures are unchanged; only proof imports and the proof body were added. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. They compile without errors or warnings. The only remaining `sorry`s are the two named split-off theorems; there are no hollow definitions, axioms, unsafe declarations, or forbidden implementation commands. Verdict: pass.
3. Checked the two split-off statements against their docstrings, DAG nodes, edge cases, and searches. Both are strict reductions of the original argument, retain the required hypotheses, and do not duplicate an existing declaration. Verdict: pass.
4. Read the proof from the target downward and checked its imports and pruning list. The proof uses the flat-base-change section formula, augmented lift, resolution-isomorphism node, and local transport node; no unit-level statement or step is bypassed. Verdict: pass.
5. Compared the Lean declarations with the three DAG nodes and checked `proof`, `proof_deps`, `proof_origin`, module paths, and realized unit route. They agree with the delivered proof and the new nodes carry the required metadata. Verdict: pass.

I changed only this second-reading report section; no Lean source or DAG content required repair.
