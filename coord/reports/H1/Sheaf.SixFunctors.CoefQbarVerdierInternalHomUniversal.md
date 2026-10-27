## What changed

Implemented `internal_hom_universal_of_comparison` with its original statement.
The proof represents source and target Hom groups at common finite stages. Finite
adjunctions give bijective evaluation transposes. Compatibility identifies their
images with the specified global evaluation. Surjectivity follows by representing
a target morphism; injectivity follows by refining representatives until their
images agree and then applying finite-stage injectivity.

Six new proved support modules make the normalizations explicit:
`CoefQbarVerdierTensorDescent`, `CoefQbarVerdierTensorInclusion`,
`CoefQbarVerdierFiniteEvaluationStage`, `CoefQbarVerdierFiniteEvaluationScalar`,
`CoefQbarVerdierDualInclusion`, and `CoefQbarVerdierEvaluationRepresentatives`.
Their imports in the item are proof imports. The item's existing public import
and theorem signature are unchanged. No existing definitions, other existing
modules, source-library declarations, or target statements were changed.

The geometric calculations use generic categorical helpers and local reducibility
settings. These avoid repeatedly expanding rational tensor, scalar localization,
and coefficient-category implementations. The support modules separate the
expensive calculations after profiling and local simplification; the per-file
compile limit is unchanged.

All six original modules passed `lcompile.py --all` without errors or warnings.
Delivery rechecks exposed a 62-second elaboration of the finite evaluation scalar
module. Explicit stage-category arguments improved its generic transport step;
profiling then isolated the normalized square and its extension to arbitrary
morphisms. The normalized square now has a separate proved module. No profiling
options remain. The two affected files compile cleanly in 32.5 and 41.6 seconds.
Delivery reruns all required checks on the seven modules.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.CoefQbarVerdier.internal_hom_universal_of_comparison`.
Original holes: 1. Holes closed: 1. Holes added: 0. Sorries left in the delivery: 0.

The six new public theorems are also proved:
`tensor_descent_spec`, `tensorInclusion_coherent`, `finite_evaluation_scalar_of_stages`,
`finite_evaluation_transport_stages`,
`finite_dual_inclusion_coherent`, and `finite_evaluation_representatives`, all in
`WeilConjectures.CoefQbarVerdier`. There are no split-off proof obligations.
Every private helper is proved, and every new definition is an explicit
construction. The only chosen functor used in the normalization is identified by
its existing unique representative prescription.

The argument covers identity extensions, arbitrary endpoint isomorphisms, and
morphisms identified only after further scalar extension. It assumes no
faithfulness of scalar extension.

## No longer needed

No existing imports were removed, and no modules were withdrawn or pruned.
The original public data import remains necessary. The separate existence lemma
`lem-coef-integral-finite-extension` is not invoked by this proof: its required
finite comparison data are already fields of the supplied `Finite` record. Its
underlying definitions remain in the statement's dependency closure.

The chosen internal-Hom comparison is not needed to prove bijectivity of the
specified evaluation. Its binder remains unchanged, and the comparison sibling
is still needed by the parent's construction; this delivery does not withdraw it.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was disputed or weakened. The original one-step plan
needed explicit tensor-inclusion and evaluation normalizations before its
representative argument could be written in Lean. These are the new proved nodes.

The docstring's finite-adjunction lemma is in a parent module importing this
item, so importing that parent would create a cycle. A private generic counit
calculation in the representative support module supplies the same finite
bijection directly from the existing `Finite.hom` adjunction and normalization.

## New nodes

`lem-coef-qbar-finite-evaluation-stage-square`: transports the normalized finite
evaluation square from rational scalar extension to the recorded stage transition.
This proved intermediate square is separated from arbitrary-morphism transport
after profiling to keep each module below the per-file compile limit.

`lem-coef-qbar-tensor-descent-spec`: proves that the prescribed tensor satisfies
`IsDescent` for the actual rational tensor family. The normalized endpoint formula
and the unique representative prescription identify it with explicit descent.
This isolates the expensive normalization proof after the other tensor
calculations were reduced to abstract isomorphism algebra.

`lem-coef-qbar-tensor-inclusion-coherent`: identifies the prescribed inclusion
with the image of `isoToStage` under explicit bilinear descent. The fully faithful
synchronized-product diagonal gives its naturality and coefficient square.

`lem-coef-qbar-finite-evaluation-stage-scalar`: transports the normalized finite
evaluation square along the recorded transition equality, then applies tensor
naturality and evaluation naturality to arbitrary morphisms and endpoint isomorphisms.

`lem-coef-qbar-dual-inclusion-coherent`: transports the recorded dual and
dualizing-object inclusion squares to the stage-system transitions. Naturality
and composition of `isoToStage` give the formula for arbitrary representatives.

`lem-coef-qbar-evaluation-representatives`: packages the finite adjunction
bijection, evaluation on representatives, and compatibility of their tensor
objects. All three clauses are used by the item's proof. These are finite-stage
calculations, not the global bijectivity conclusion under another name.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarVerdierDualInclusion": "1eaf5d2109b6aff5ef28a25e028981d3dd7dfa18", "Sheaf.SixFunctors.CoefQbarVerdierEvaluationRepresentatives": "97ea3b309a94da006b8a4c8fbc0287416bd154a0", "Sheaf.SixFunctors.CoefQbarVerdierFiniteEvaluationScalar": "95ce17a81cd71f9176f9cd91772e74f03b64b559", "Sheaf.SixFunctors.CoefQbarVerdierFiniteEvaluationStage": "ca0fb762ff05bb48a3dc5ef6f56a46c5118bed5d", "Sheaf.SixFunctors.CoefQbarVerdierInternalHomUniversal": "73c2eb7db91047a00ed29e0e2be7fb1a89044b0b", "Sheaf.SixFunctors.CoefQbarVerdierTensorDescent": "3eff1ab05deed12e9f0e0a6742193d21984f515a", "Sheaf.SixFunctors.CoefQbarVerdierTensorInclusion": "e1b021e95f7241ae19e4a9ab57f7650af3d71bca"}, "results": {"Sheaf.SixFunctors.CoefQbarVerdierInternalHom": {"hash": "1d723423e9adea8fd21909e1a5684d1b675e0850", "status": "OK"}}, "seconds": 69, "time": "2026-10-28T04:01:52+0800", "transitive": 0, "version": 1}
```

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
