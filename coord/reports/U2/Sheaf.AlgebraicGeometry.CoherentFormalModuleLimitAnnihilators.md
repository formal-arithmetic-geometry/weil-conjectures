## What changed

`Sheaf.AlgebraicGeometry.CoherentFormalModuleLimitAnnihilators` now proves
`AlgebraicGeometry.coherentFormalModule_limit_annihilators` with its original signature.
The proof follows the original affine route: restrict the given fork/cofork, pass through
an affine completed-module equivalence, include finite modules, and restrict scalars.
It proves finite-module closure under subobjects and quotients using Mathlib, maps the
actual universal properties through each functor, transports preservation along the
natural comparison, and applies the linear kernel/cokernel comparisons and
`LinearEquiv.annihilator_eq`.

Added `Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineLimitModel`, containing only the
natural finite completed-module model of affine section limits. Its source and complete
proof plan are in its docstring and its new node. The concrete section-limit functor is a
composition of existing functors, not a new definition or data chosen from existence.
The equivalence and natural isomorphism are eliminated only inside a proposition proof.

The item's proof imports are now `CoherentFormalModuleAffineLimitModel`,
`CoherentFormalModulesRestrictionLimits`, `Sheaf.RingTheory.AdicCompletionNoetherian`, and
`Mathlib.CategoryTheory.ObjectProperty.Kernels`. Existing public imports, declarations,
visibility and docstrings are unchanged. Updated the original node's proof, proof_deps
and proof_origin to match the compiled argument. No forced adaptations or statement
changes are needed.

Both delivered modules compile together with `lcompile.py --all`, without warnings.
The main proof was also compiled separately after each successful import removal.
The new comparison was checked mathematically for the empty affine open, the zero ideal,
the unit ideal, zero objects, and zero maps. In particular no nontrivial-ring or
proper-ideal hypothesis is added. The unit statement and realized steps are unchanged.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.coherentFormalModule_limit_annihilators`
(node `lem-weil-pbc-formal-kernel-cokernel-limit-annihilators`).
There is no `sorry` left in the item's module.

Added exactly one hole:
`AlgebraicGeometry.coherentFormalModule_affine_limit_model`
(node `lem-weil-pbc-formal-affine-limit-model`), in its new module.
Its proof is exactly `:= by sorry`.

This is a decomposition: one upper hole closed, one lower hole added, net zero holes.
The new statement contains no kernel, cokernel, exactness or annihilator assertion;
it is the natural affine-presentation comparison needed within the argument. The
Noetherian closure argument, all fork/cofork preservation and comparison steps, and
annihilator transport are real Lean proofs in the item's module. Existing imported
holes are not claimed as closed.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`.
Its node `lem-weil-pbc-coherent-formal-modules-affine` remains needed below the new model
node, so this is a relocation of that dependency, not a claim that affine theory is pruned.

Removed `Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness` and the direct
proof dependency `lem-weil-pbc-coherent-formal-modules-local-exactness`.
The annihilator proof does not need the covering-detection or short-complex assertions
of this module; it uses only the narrower already proved
`lem-weil-pbc-coherent-formal-modules-restriction-limits`.

Removed redundant provisional imports after compiling their removal:
`Mathlib.RingTheory.Noetherian.Basic`,
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`,
`Mathlib.RingTheory.Ideal.Maps`, and `Mathlib.Algebra.Category.ModuleCat.Kernels`.
Their declarations remain visible through the retained imports.
The import of `Mathlib.CategoryTheory.ObjectProperty.Kernels` was checked and retained:
its removal makes the object-closure and inclusion-preservation declarations unavailable.

No whole-project pruning count is claimed: other modules may still reach any of these
modules. No further original planned proof nodes were bypassed.

## Where the brief, the DAG or earlier work was wrong

The mathematical route is valid. Its affine-equivalence step suppresses a nontrivial
interface bridge: `coherentFormalModules_affine` is stated on `Spec A`, with
`moduleSpecGammaFunctor` (the Lean name is `moduleSpecΓFunctor`), whereas the item uses
sections on an arbitrary affine open of X. The natural scalar-compatible comparison,
including restriction and transport by the affine-open isomorphism, is not provided by
that signature alone. This is the one step separated into the new model theorem.
An abstract equivalence without its underlying-functor comparison would not suffice.
The new node specifies the controlled termwise-pullback construction, rather than
relying on an unspecified equivalence witness.

The local exactness theorem includes substantially more than the preservation needed
here. Its already proved restriction-limits dependency gives the precise assertion.
LeanSearch returned an Internal Server Error; Loogle, LeanFinder, the supplied grep
service, and local source searches were used. The Stacks source files are not present
in this clone, so Lemmas 087W and 087X were read at their official Stacks pages.

## New nodes

`lem-weil-pbc-formal-affine-limit-model`:
`lean/Sheaf/AlgebraicGeometry/CoherentFormalModuleAffineLimitModel.lean`, declaration
`AlgebraicGeometry.coherentFormalModule_affine_limit_model`.
It states the natural identification of the actual affine section-limit functor with
restriction, a finite completed-module equivalence, inclusion and scalar restriction.
Its proof plan gives ideal transport along the canonical affine isomorphism, controlled
formal pullback, the existing Spec affine theorem with its limiting cones, and assembly
of the natural comparison by uniqueness of limits. Its dependencies remain below the
original annihilator node and keep the blueprint unit's route. No change record is
needed because no existing interface is changed.

## Second reading by U2

1. Interface check: compared both delivered modules with the repository. The only
existing declaration, `AlgebraicGeometry.coherentFormalModule_limit_annihilators`, has
its signature byte-for-byte unchanged (also checked by extracting the text before
`:= by`). Its existing docstring, public imports and visibility are unchanged. The
new module introduces only a theorem, no definitions. No change record is required.
Verdict: pass.

2. Proof check: compiled both modules together after the repair and compiled a scratch
copy with `#print axioms` for both delivered declarations. Both list exactly `propext`,
`Classical.choice`, `Quot.sound` and `sorryAx`; the latter is expected from the open
comparison and upstream holes. The item's body has no hole. The only new hole is
`coherentFormalModule_affine_limit_model`, exactly `:= by sorry`, with its named node
and source/proof docstring. No forbidden declarations or hollow definitions occur.
The proof maps the given universal properties, rather than assuming that arbitrary
termwise kernels are formal kernels. Verdict: pass, conditional on the reported hole.

3. New-statement check: read Stacks 087W and 087X at their official pages, and read
`coherentFormalModules_affine`, `coherentFormalModulesRestriction`, and
`exists_formalSystemsPullback`. The affine theorem provides an equivalence on Spec A
with natural limiting cones; it does not already state the arbitrary-open comparison.
The new theorem supplies precisely that missing comparison. Its Noetherian hypotheses
match the source and the open subscheme hypothesis follows from that on X. At J=0,
the transition isomorphisms give constant systems; at J=A, every term and the completion
are zero; for the empty affine open A is the zero ring. Zero objects and zero arrows
are covered by the natural functor comparison, without an injectivity or surjectivity
hypothesis on the arrow. No counterexample was found. The equivalence witness is
eliminated inside a proposition proof, never used to define arbitrary data.
Fresh LeanFinder search for the affine-open adic-system comparison returned completion
and local-cohomology primitives only; Loogle returned uniqueness-of-limit comparisons;
grep found `restrictAppIso` and its scalar compatibility, not this theorem. Local
searches in both Lean roots found the Spec affine theorem and its components, not a
duplicate arbitrary-open model. Closing this hole requires the nontrivial ideal and
scalar transport construction, not a few-minute application. It is strictly the affine
model step, with none of the kernel/cokernel or annihilator conclusions of the item.
Verdict: valid decomposition, one closed hole and one added hole, net zero.

4. Route and pruning check: read `dag/units/sk-thm-p1.json`'s `realized` statement and
four step lists. Neither removed direct dependency realizes one of those steps; this
below-unit affine route retains restriction, affine equivalence and linear comparison.
The old `proof_deps` contained exactly affine equivalence and local exactness; both
removed direct imports are accounted for under No longer needed. Affine equivalence
remains a dependency of the new model, and the already proved restriction-limits theorem
replaces the broader local-exactness theorem. No whole-project pruning is claimed.
The proof-only imports in the item have the appropriate plain visibility. Verdict: pass
with the planned-dependency import repair described below.

5. Node check: the item's new proof steps and union of `uses` agree with its actual
Noetherian completion, finite-module closure, affine model, restriction preservation,
and linear-equivalence argument. The new node has its source, self-contained statement,
statement dependencies, proof steps, search records, split status, ancestry, chapter,
unit, creation record and Lean record. Its Lean statement agrees with the new theorem;
its planned dependencies are existing declarations, not copies. Verdict: pass after
making the module's planned proof imports agree with its node.

Changed during second reading: added plain imports of
`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine` and
`Sheaf.AlgebraicGeometry.FormalSystemsPullback` to the new open model module. These
are the already recorded dependencies for its Spec-equivalence and controlled-pullback
proof steps, as required by the stage-3 dependency-import contract. They are planned
imports for the named open theorem, not public interface additions. Recompiled both
modules and checked axioms after this repair. No statement, definition, proof body or
DAG route changed. No additional hole was closed or added.
