## What changed

Replaced the proof hole of `AlgebraicGeometry.Scheme.ProEt.component_pushforward_exact_unit`
by a proof of the unchanged statement from existing library declarations and one separate
local unit lemma. The four original definitions and all original public imports are unchanged.

The private helpers prove the component-test geometry (affineness, w-contractibility,
closed-point formula, stalk isomorphisms and the specified component homeomorphism),
construct the coefficient adjunction using generic coefficient comparison, and prove
additivity and preservation of finite limits and colimits of module pushforward. Exactness
uses actual weakly contractible evaluation from the source library, the module forgetful
functor, Stonean presentations and the local-surjectivity criterion. Covering descent turns
the Stonean local unit into a global module isomorphism. Whiskering its inverse constructs
the natural evaluation isomorphism; its inverse law and naturality give both formulas.

Added `Sheaf.AlgebraicGeometry.ComponentModuleUnitStonean`, which isolates the local
module-unit calculation of HRS Proposition 4.3(1), with arbitrary ring coefficients and
explicit chosen adjunction. This is a strictly smaller part of the argument: it does not
assert the geometry, existence of the coefficient comparison, exactness, global descent,
or natural evaluation isomorphisms of the original item. Its docstring gives the split-cover,
Kan-extension, scalar-transport and adjunction-uniqueness proof. Its node records the source
and the declared dependencies of that argument. The item node now follows the actual proof.

The proof imports the universe-compatible module-adjoint theorem and uses existing private
proved helpers for field component equivalence and ring reconstruction via proof-only
`import all`; no source-library file was changed.

## Proved and sorry left

Closed the one original hole, by declaration:
`AlgebraicGeometry.Scheme.ProEt.component_pushforward_exact_unit`.
All private helpers in that module have complete proofs.

Added one hole, by declaration:
`AlgebraicGeometry.Scheme.ProEt.component_module_unit_bijective_on_stonean_tests`
(node `lem-sfb-component-module-unit-stonean`). Its proof is exactly `by sorry`.
There are no other holes in either delivered Lean file and no holes in definitions.
This is a decomposition (one upper hole closed, one strictly smaller local-unit hole added),
not a claim of positive net hole reduction or an axiom-free proof of the original theorem.
Existing imported stated dependencies retain their own proof status.

## No longer needed

Removed direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact`
- `Sheaf.AlgebraicGeometry.ProEtale.WContractibleClopenPartition`
- `Sheaf.Topology.StoneanCover`
- `Sheaf.CategoryTheory.GeometricModuleTransport`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation`
- `Sheaf.AlgebraicGeometry.StalkIsomorphismLifting`

The exactness proof uses the already proved source affine weak-contractibility theorem
instead of `det-pe-wc-sections-exact`. Stonean presentations and Mathlib coherent-cover
lemmas replace `det-pe-stonean-cover`. Right-adjoint limit preservation and the source
forgetful-colimit theorem replace the dedicated module-limit and site-epi wrappers.
The scalar transport and split-cover dependencies are now local-unit proof dependencies,
not direct dependencies of the upper theorem. In particular the new node still needs
`det-pe-wcb-clopen-partition`, `lem-weil-pbc-geometric-module-transport`,
`lem-weil-pbc-proetale-finite-coproduct-evaluation`,
`lem-weil-pbc-ringed-topoi-module-adjunction`, and
`new-lem-zl-stalk-isomorphism-lifting`; these are not claimed globally pruned.

Removed obsolete top-level tool approvals from the item node, retaining the order of
remaining approvals: `det-pe-stonean-cover`, `det-pe-wc-sections-exact`,
`det-pe-wcb-clopen-partition`, `lem-weil-pbc-geometric-module-transport`,
`lem-weil-pbc-proetale-finite-coproduct-evaluation`,
`lem-weil-pbc-ringed-topoi-module-adjunction`, and
`new-lem-zl-stalk-isomorphism-lifting`. No module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed and no target or definition was changed. The plan's ordinary
module transport needs care about universes: the existing small-category
`inverseImage_underlying_unit_of_ring_presentation` theorem fixes object, morphism and
coefficient universes equal, whereas the component sites here have objects in `u+1`,
morphisms in `u`, and module values in `u+1`. It therefore cannot be applied directly.
The local unit lemma records the precise required conclusion without asserting that this
universe mismatch has already been repaired. Likewise the ordinary Mathlib right-adjoint
instance is replaced with the existing universe-compatible theorem.

The proof follows the inherited HRS component-test route. The unit record has no realized
statement or step assigned to this node, and no blueprint unit has been bypassed.
Empty W, empty E and zero coefficient rings were checked in the mathematical argument;
no nonempty, finite or discrete-coefficient hypothesis is introduced.

## New nodes

`lem-sfb-component-module-unit-stonean` is the bijectivity of the ordinary module unit at
an extremally disconnected profinite component test, the local calculation in HRS
Proposition 4.3(1). It generalizes the coefficient input only to avoid tying a genuine local
inverse-image lemma to the paper's condensed coefficient notation. Its Lean attachment is
`Sheaf.AlgebraicGeometry.ComponentModuleUnitStonean` and its proof is recorded in full in
words. Three kinds of Mathlib search (including two semantic formulations) found no direct
match. The node inherits the item's chapter, unit and blueprint ancestry. No change record
is needed: no existing definition, signature or statement is changed.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
