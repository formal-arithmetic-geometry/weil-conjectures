# AlgebraicGeometry.ProEtale.CondensedRing.monoidal_leftDerivedUpperStar

## Reason

The adopted module contains seven proof holes inside constructed definitions/instances.
C2's retained complete repair compiles, but normal deliveries correctly encounter the
source-library freeze: the repair also constructs the tensor counits differently, adds
public helpers/imports, and changes other construction bodies. Repeatedly redispatching
that broader repair cannot make it a proof-only delivery. Prior maintenance reports
requested a gate change without changing this incompatible source layout.

This authorized module maintenance repair applies the already-written C2 implementation;
no new mathematical proof is invented by maintenance. The source-library gate, review
service, landing tools and dispatcher remain untouched.

## Old

`upperStarTensorCounit` contains two naturality holes;
`leftDerivedUpperStarTensorLeftCounit` contains two naturality holes;
`monoidal_leftDerivedUpperStar` contains associativity and both unitality holes.
The complete old source is retained as
`Monoidal.lean.maintenance-1792257299.bak` alongside the server file.

## New

The homotopy tensor counit is composed from canonical natural transformations.
The derived counits and bifunctors use the existing generic constructions. The worker's
generic derivability helpers prove the comparison is invertible; its theorem
`leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison` identifies the universal
left-derived comparison with the canonical comonoidal comparison.

The monoidal structure uses the existing proved `Functor.residueDerivedMonoidal`.
`residueDerivedOplax_η_eq_tensorUnitIso` and `leftDerivedMonoidalWithUnit` retain the
explicit original unit map. Local aliases for ambient, pullback and tensor-colimit properties reduce repeated
searches; the complex tensor existence proof directly reuses its graded instance. All seven old holes are closed, and no new hole is introduced.

Every existing public signature and visibility is preserved. The changed private helper
`isIso_tensorCounit_app_app` and the removed private `isIso_upperStarTensorComplexHom`
have no public callers. Three public imports expose the data needed by the constructed
public definitions. Existing declaration docstrings are retained.

## Users

| module | group holding it at inspection | effect |
| --- | --- | --- |
| WeilConjectures | unclaimed | Public signatures preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | B2 | Public signatures preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Public signatures and explicit unit API preserved; consumer checked. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Public signatures preserved; no adaptation. |

These are the direct importers; the downstream tool reports 207 transitive users.
No target statement is changed. The construction change uses the same canonical tensor
and unit comparisons; the named compatibility certificate connects the universal lift
to the monoidal structure. The global build remains responsible for all transitive users.

## Status

open; maintenance module correction, pending the normal global build. Single-file compilation, public-signature checks and
consumer validation are recorded in the maintenance report. No protected pipeline tool
or concurrency/admission setting was changed.
