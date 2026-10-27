## What changed

Partial proof delivery for `Sheaf.Paper.FieldStageOrdinaryRealization`.
Four of its eight existing holes are filled without changing any public signature,
public import, existing definition body, or existing docstring.

* `integralRestriction_exact`: compose restriction with forgetting to abelian
  sheaves. This is definitionally the original forgetful functor. Preservation
  and reflection of finite limits and colimits give exactness of restriction.
* `constantLinear_existsUnique`: construct the ring map from constants to
  compatible sections of the constant ring sheaf using the sheafification unit.
  Restrict the existing section-ring Hom module structure along that ring map.
  Its scalar action is the required sectionwise formula by reduction; that
  formula determines every Hom module structure and therefore the Linear record.
  The three added helpers are private and completely proved.
* `coefficientMap_comp`: apply functoriality of constant sheafification to the
  composite of the lifted coefficient homomorphisms.
* `closureInclusion_comp`: cancel the intermediate Shrink algebra equivalence
  and identify the composite subtype inclusions by extensionality.

Add the private proof import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule` for the existing
section-ring linear structure. Remove the unused private proof imports listed below.
The existing DAG proof route is retained; no new mathematical dependency is introduced.
The four completed proofs apply to arbitrary schemes and include identity inclusions
and the zero coefficient ring where their signatures permit it.

## Proved and sorry left

Closed four existing holes (namespace `WeilConjectures.OrdinaryFieldRealization`):

* `integralRestriction_exact`
* `constantLinear_existsUnique`
* `coefficientMap_comp`
* `closureInclusion_comp`

Four existing holes remain unchanged, all attached to
`lem-sf-field-stage-ordinary-realization`:

* `extendComp_existsUnique`
* `extendUnit_existsUnique`
* `pairLinear_existsUnique`
* `exists_ordinaryFieldRealization`

Added holes: zero. Split-off theorems: zero. This is a partial delivery, with
four actual proofs rather than a decomposition. The tensor coherence and the
bounded common-stage realization remain to be proved by the existing five-step plan.

## No longer needed

Remove these eleven unused private imports:

* `Sheaf.Paper.SfIntegralConstructibleLinear`
* `Sheaf.Paper.CompleteResidueCohomologyBounds`
* `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
* `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`
* `Sheaf.Paper.SfScalarExtensionComposition`
* `Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent`
* `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`
* `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution`
* `Sheaf.Paper.SfIntegralConstructible`
* `Sheaf.Paper.SfRationalizationKaroubi`

The public imports already expose the declarations needed by the statements.
No DAG node or module is claimed to be mathematically unnecessary: the main
realization theorem is still open, and its planned comparison and boundedness
lemmas remain relevant. There is no withdrawal and no change to the unit route.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The exactness and constant-linearity infrastructure
can be proved directly using the existing forgetful and section-ring APIs; it
requires none of the advanced comparison lemmas in the main realization plan.
The generic linear structure is used only as proof data for its uniquely specified
public theorem. No arbitrary witness of mere existence is introduced.

Validation: the final single-file server compile and delivery preflight are recorded
by the delivery tool. No target, shared module, or DAG statement was modified.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
