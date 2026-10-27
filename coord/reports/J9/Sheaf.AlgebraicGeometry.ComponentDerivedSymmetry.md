## What changed

`Sheaf.AlgebraicGeometry.ComponentDerivedSymmetry` now proves
`AlgebraicGeometry.ProEtale.CondensedRing.component_derived_symmetry` with its original
signature. The proof constructs the strong monoidal module functor using
`Mod.ResidueOrdinary.mapModComapMonoidal`, proves its ordinary braiding equation by
cancelling the balanced tensor projection, and converts that equation to oplax form.
It lifts the component sheaf adjunction to modules to supply the left-adjoint instance.
The proved source-library `Functor.leftDerivedFunctorBraided` then supplies the native
Koszul derived braiding. Finally the proof transports the strong braided structure
along `leftDerivedFunctorIsoMapDerivedCategory` to the fixed termwise derived functor
used in `componentSymmetric`.

Added private proof imports of `Sheaf.Paper.IntegralResidueOrdinaryMonoidal`,
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure`,
and the new `Sheaf.AlgebraicGeometry.ComponentPullbackFlat`. The original public import
of `CondensedLisseEvaluationModel` is retained. No existing public signature, definition,
source-library file, or consumer was changed. The private braiding helper is fully
proved; it works for a general strong braided abelian functor and a coefficient
isomorphism.

The only missing input is preservation of ordinary flat internal modules by the
component inverse image. It is stated in the new module, with a source, a complete
finite-relation proof in words, and its DAG node. The original node's proof route and
proof dependencies now describe the actual Lean proof.

Both Lean files compiled through `lcompile.py --all`: ComponentPullbackFlat in 45.8 s,
ComponentDerivedSymmetry in 55.6 s, with no warnings or errors. Earlier single-file
compiles of the symmetry proof also passed. The last changes after that compile are
the flatness theorem's expanded proof docstring, DAG records, and this report; delivery
runs the final compile and preflight.

## Proved and sorry left

Original holes: 1. Original hole replaced by a complete Lean proof:
`AlgebraicGeometry.ProEtale.CondensedRing.component_derived_symmetry`
(`lem-zl-component-derived-symmetry`). There is no `sorry` left in the assigned module.

Added holes: 1, exactly the public theorem
`AlgebraicGeometry.ProEtale.CondensedRing.component_pullback_preservesFlat`
(`lem-zl-component-pullback-flat`) in
`Sheaf.AlgebraicGeometry.ComponentPullbackFlat`. Its whole proof is `:= by sorry`.
No other holes were added, and none occur in definitions or private declarations.

This is a decomposition: one upper hole is closed using one new lower hole, so the
net hole change is zero. It is not an unconditional proof of derived symmetry.
The new obligation concerns individual ordinary modules and exactness of tensoring;
it has no complexes, derived category, total-tensor signs, or braided derived functor
in its conclusion. The complete Lean assembly proves the passage from that ordinary
input to the original derived conclusion, rather than restating derived symmetry.
Existing holes already imported through the original model are unchanged.

## No longer needed

No original Lean import was removed. The following four original planned proof
dependencies are not used directly by this proof and were removed from the assigned
node's `proof_deps` and proof-step `uses`:

- `lem-trf-geometric-inverse-image-exact`
  (`Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`): exactness of the fixed
  abelian component inverse image is already a hypothesis, and exactness of its
  module lift is supplied by the existing instances.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
  (`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`): the ordinary internal
  balanced tensor comparison is already proved in IntegralResidueOrdinaryMonoidal.
- `lem-weil-pbc-ringed-pullback-preserves-kflat`
  (`Sheaf.Paper.KFlatRingedToposPullback`): the source library's generic derived-functor
  construction uses ordinary flatness and its existing K-flat-resolution API.
- `lem-weil-pbc-site-derived-tensor-descent`
  (`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`): the
  generic source-library derived monoidal and braided construction performs this
  localization and coherence argument.

These are dependencies pruned from this item's route, not assertions that their
modules are globally unreachable. No module is withdrawn or listed for deletion.
The remaining ordinary-flatness argument still uses the internal/sectionwise
comparison and algebraic inverse-image flatness theory named in its own node.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed and no target or unit route changes. The planned derived
comparison and descent can be replaced by the already-proved general source-library
construction. The available scheme-morphism theorem
`AlgebraicGeometry.ProEtale.inverseImageModule_preservesFlat` cannot be applied to
`componentTests`: its source is a profinite slice site, not the small pro-etale site
of another scheme. This is why ordinary component flatness remains an explicit
obligation rather than an attempted application of that theorem.

The flatness source was checked in Stacks Project `sites-modules.tex`,
`lemma-pullback-flat` (Tag 05VD). Its finite-relation argument includes the zero ring,
empty finite relations, and the empty scheme. A whole-blueprint search and repository
search found no existing component flatness statement. The generic algebraic
inverse-image flatness theorem and internal/sectionwise comparison are reused as
planned dependencies; no duplicate generic flatness theorem was added.

## New nodes

`lem-zl-component-pullback-flat`, in `dag/nodes/sec-zeta-weil/`, is the ordinary-module
flatness part of the original node's passage to flat-term K-flat complexes. Its Lean
attachment is the single new theorem in `Sheaf.AlgebraicGeometry.ComponentPullbackFlat`.
The node records the local equational criterion argument of Tag 05VD, the actual
relative-test inverse image, internal/sectionwise module comparison, coefficient
isomorphism transport, three kinds of Mathlib searches, and the same chapter and
unit as its parent. No existing statement or definition was changed, so no change
record or forced consumer adaptation is needed.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
