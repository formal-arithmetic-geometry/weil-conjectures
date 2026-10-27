## What changed

Proved `coefficientScalarTensorRepresentative_internal` with its original statement unchanged.
The proof first derives the ordinary scalar tensor square from the two supplied generator
normalizations. It extends that square to each total-complex summand and then to the signed
unbounded total complex. Independently, the universal counit equation for the derived tensor
comparison gives the internal complex square. The original theorem transports K-flatness and
termwise flatness across the total comparison, applies `hscalar` to both factors and their
tensor, and pastes these squares with `htensor`, localization compatibility and naturality.
The final cancellation uses an explicit composite isomorphism.

The twelve proved supporting statements occupy separate modules to keep kernel checking and
elaboration below the per-file limit. Their imports are private proof imports in the assigned
module. Its public imports, all existing signatures, all shared definitions, and the blueprint
unit route are unchanged. No adopted source module is edited.

Validation: all thirteen Lean modules passed the remote compiler in import order, including
the assigned theorem. The final diagnostic options have been removed. The public theorem
signature and imports match the original, the new node signatures match their Lean, and
no delivery node participates in a dependency cycle.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarTensorRepresentative_internal`.
Added zero holes; zero holes remain in the delivery. This is a proof, not a decomposition into
new unproved statements.

The twelve new public theorems are proved:

- `coefficientScalarTensor_ordinary`;
- `coefficientScalarTensor_summand`;
- `coefficientScalarTensor_total`;
- `coefficientScalarTensor_complexLocalization`;
- `coefficientScalarTensor_internalComplex`;
- `coefficientTensor_localization`;
- `coefficientScalarTensorRepresentative_paste`;
- `coefficientScalarTensorRepresentative_leftPath`;
- `coefficientScalarTensorRepresentative_totalPath`;
- `coefficientScalarTensor_summandNaturality`;
- `coefficientScalarTensor_complexCounit`;
- `coefficientScalarTensor_homotopyComplex`.

All private helpers are proved. Existing library statements used by the proof retain their
current proofs and obligations.

## No longer needed

No original module or declaration is pruned. The original public imports are retained.
The representative-equation definition is no longer a direct proof dependency of the
assigned node: it is carried by the new pasting node and still required by the original
public import. Unused private proof imports of
`SectionCochainTensorComparison` were removed from the new ordinary and totalization
modules, and an unused private diagram lemma was removed from the new localization module.
The hypotheses and representative
equation remain necessary. No existing module or declaration is withdrawn. The new proof
uses only the ordinary normalization, tensor inclusion, derived counit and localization APIs
needed for its actual argument; unrelated planned theory is not imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The originally holed internal-image step
can be closed from the supplied normalizations and existing tensor/localization APIs, rather
than splitting it into another equivalent obligation. The internal complex calculation uses
the existing general theorem `Functor.leftDerivedTensorComparison_app_app_comp_tensorHom`.
Large concrete rewrite searches were replaced with a proved categorical diagram-pasting
lemma and explicitly typed comparison arrows. The total-complex calculation uses the direct
`GradedObject.Monoidal.ι_tensorHom` naturality formula. The categorical calculation
also uses `internalLocalizationTensorMap_app` explicitly and rewrites the curried
`derivedTensor` map with the native tensor morphism formula, avoiding reduction through
derived localization choices. The scalar-counit identification is checked separately in
its own module. The internal square combines that equation, the proved comparison of complex
and homotopy localization tensor maps, and the native derived counit face through a proved
private categorical diagram lemma. Local prolongation transparency and retained `let`
bindings avoid unnecessary conversion through the large complex constructions. Keeping the
totalization, section equivalence, and section monoidal structure abstract during summand
diagram matching reduced its checked runtime from over a minute to 48 seconds. The
total-path proof introduces its statement's existing `let` bindings directly, preserving
the shared functors and comparison maps through kernel checking and serialization.

## New nodes

`lem-sfb-coefficient-scalar-tensor-ordinary`, realized by
`Sheaf.Paper.CoefficientScalarTensorOrdinary`: the ordinary square follows by testing the
scalar-extension coequalizer on pure tensors, tensor/sheafification extensionality, and the
provided generator and monoidal equations. No flatness assumptions are used.

`lem-sfb-coefficient-scalar-tensor-summand`, realized by
`Sheaf.Paper.CoefficientScalarTensorSummand`: the total-complex square after precomposition
with one specified bidegree inclusion. This is a strict part of the total-complex argument,
using the ordinary square and the four summand formulas.

`lem-sfb-coefficient-scalar-tensor-total`, realized by
`Sheaf.Paper.CoefficientScalarTensorTotal`: equality of chain maps follows from the proved
summand square by coproduct extensionality and homological-complex extensionality.

`lem-sfb-internal-complex-localization-tensor-comparison`, realized by
`Sheaf.Paper.InternalComplexLocalizationTensorComparison`: the localization tensor map on
complexes equals the homotopy-to-derived tensor map after taking the homotopy quotient.
This follows by unfolding the composite lax monoidal structure and its identity factors.

`lem-sfb-coefficient-scalar-tensor-internal-complex`, realized by
`Sheaf.Paper.CoefficientScalarTensorInternalComplex`: the internal complex scalar counit
square, without flatness assumptions. It follows from the general derived tensor counit
equation and the preceding localization comparison.

`lem-sfb-coefficient-tensor-localization`, realized by
`Sheaf.Paper.CoefficientTensorLocalization`: the section localization tensor map on
reconstructed complexes simplifies to the localized native tensorator followed by the
localization and total-comparison maps. Its proof cancels the inverse comparison factors
in `qTensor_spec` and uses `sectionTotalComparison_eq`. The module also holds proved private
categorical helpers used by the pasting calculation.

`lem-sfb-coefficient-scalar-tensor-representative-pasting`, realized by
`Sheaf.Paper.CoefficientScalarTensorRepresentativePasting`: the categorical part of the
argument, given the three scalar complex equations. It has no K-flatness or flat-term
hypotheses. Its proof uses the proved localization normalization, total-complex square and
internal complex square, and pastes them with naturality and `htensor`. The assigned theorem
supplies those three scalar equations using its flatness assumptions. This helper is proved,
with no transferred or repackaged hole.

`lem-sfb-coefficient-scalar-tensor-representative-left-path`, realized by
`Sheaf.Paper.CoefficientScalarTensorRepresentativeLeftPath`: the left path identity after
comparison, using the scalar equation only on P tensor Q. Its proof uses scalar-counit
naturality, the total-complex square, the internal counit square, and localization
naturality. It requires neither the two factor scalar equations nor `htensor`. Separating
this proved identity from the final tensor square keeps the concrete diagram checks small.

`lem-sfb-coefficient-scalar-tensor-representative-total-path`, realized by
`Sheaf.Paper.CoefficientScalarTensorRepresentativeTotalPath`: the scalar equation on the
tensor complex, localization normalization and the ordinary total square identify the
initial scalar path through the localized internal total tensor. This is a proved strict
part of the left path argument, before applying the internal derived tensor square.

`lem-sfb-coefficient-scalar-tensor-summand-naturality`, realized by
`Sheaf.Paper.CoefficientScalarTensorSummandFormulas`: the tensor of a prolonged natural
comparison carries bidegree inclusions to the corresponding target inclusions.
The proof is graded tensor naturality; the module also holds proved private summand
formulas and a categorical pasting lemma. Abstract functors keep these proofs independent
of the size of the concrete reconstruction constructions.

`lem-sfb-coefficient-scalar-complex-counit`, realized by
`Sheaf.Paper.CoefficientScalarComplexCounit`: the fixed complex scalar comparison equals
the derived counit, by the existing counit factorization and the identity localization
comparison. This is a proved strict part of the internal complex square. The module
also proves the private factor corner combining two counit equations with the equality
of complex and homotopy localization tensorators.

`lem-sfb-coefficient-scalar-tensor-homotopy-complex`, realized by
`Sheaf.Paper.CoefficientScalarTensorHomotopyComplex`: the general derived tensor counit
face specialized to homotopy quotients of complexes. The proof is the existing general
counit theorem, with quotient and prolongation objects normalized. Keeping this proved
face separate avoids repeating its large conversion inside the internal complex square.

No change record is needed: only the assigned module, its proof record, and new proved
modules and nodes are changed.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
