## What changed

Replaced the sole proof hole in
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.integral_residue_coefficient_transport`
by a complete assembly of two strictly smaller comparisons. The original statement,
universes, hypotheses and public imports are unchanged. The new proof obtains a normalized
ordinary discrete coefficient model, compares the derived residues, transports every homology
object along the exact functor comparison and the residue isomorphism, and transports native
Tor amplitude with the existing exact faithful monoidal functor theorem. It converts native
Tor amplitude to the existing coefficient-model test using `nativeTor_iff`; replacing an
unordered lower endpoint by `min a b` preserves the zero-object case.

Added `Sheaf.AlgebraicGeometry.DiscreteCoefficientModel`: the additive constant-sheaf
comparison, a normalization predicate on constant sections and its proved uniqueness lemma,
the explicit section-action / small-site / scalar-restriction functor, its proved equivalence and additive instances, and its
ordinary-module comparison theorem.
Added `Sheaf.AlgebraicGeometry.IntegralResidueModelComparison`: the proved existing lifted
quotient equivalence, reoriented, proved tensor-colimit, flat-resolution and K-flat scalar-extension helpers, and the
derived common-residue isomorphism theorem.
The functors are constructed explicitly; no definition selects an arbitrary object from an
unproved existence statement. The existential coefficient map in the proof is determined by
its action on all constant sections, hence by sheafification.

This is a decomposition of the remaining comparison work. It makes the homology and Tor
assembly real Lean rather than moving the original equivalence to a new name. Neither new
obligation states constructible finite-Tor residue transport: one concerns the ordinary heart
for arbitrary discrete scalars, and the other is only an isomorphism without finiteness tests.
The unit's comparison-of-first-reductions route is preserved. The proof reuses the existing
small-site equivalence helpers from `IntegralModelsCompletionTransport` and scalar
cancellation isomorphisms from `ConstantScalarRestrictionTensor` through private proof
imports; these helpers are fully proved and are used only in theorem proofs.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.integral_residue_coefficient_transport`
(node `lem-sfb-integral-residue-coefficient-transport`). There are zero holes left in the
assigned module.

Added two named holes, each with a complete proof in words and its own module and node:

- `AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_coefficient_model`
  (`lem-sfb-discrete-coefficient-model`).
- `AlgebraicGeometry.ProEtale.IntegralModelsStacks.integral_residue_model_comparison`
  (`lem-sfb-integral-residue-model-comparison`).

Hole accounting: one closed, two added; a decomposition, not a net hole reduction. The
additive sheaf isomorphism, normalization predicate, explicit functor and quotient ring
equivalence have no holes. The public instances `discreteCoefficientModel_isEquivalence`
and `discreteCoefficientModel_additive` are proved for every scalar isomorphism, without
using either new hole. `discreteCoefficientNormalized_unique` proves that the specified
normalization determines the scalar ring isomorphism, also without using either hole. No existing definition, target statement or
source-library signature was changed.

Also proved in `IntegralResidueModelComparison`:
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.residueTensorColimits`,
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.residueFlatResolution`, and
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.residueExtensionKFlat`.
These instantiate existing internal-module results with the specified scalar structures;
they add no assumptions or holes. The reoriented quotient equivalence
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.integralResidueScalarEquiv` uses the existing,
proved and uniquely normalized quotient equivalence.

Validation: `lcompile.py --all` compiled all three delivery modules with no errors or
warnings (45.8 s, 49.8 s and 51.2 s respectively). The original assigned theorem signature
was compared verbatim and is unchanged. All new node dependencies exist, and every new
public declaration is recorded in its node. The imports retained each supply declarations
used by the corresponding statement, explicit construction or proof.

## No longer needed

No original public import was removed, and no module was withdrawn or globally pruned.
The original direct proof dependencies for integral completion, integral realization,
coefficient quotient arithmetic, section tensor comparison, constant scalar tensor
comparison, fixed-scalar realization and Noetherian global constructibility are now needed
by the two smaller comparisons. They are retained in their respective node proof dependencies,
rather than claimed as pruned. The assigned node now directly depends on those comparisons,
the exact cohomology comparison, coefficient constructibility isomorphism invariance and the
coefficient flat-model theorem.

The internal-residue/Stacks comparison and finite continuous-coefficient presentation routes
were inspected but not imported: they stop at a different residue presentation or use a
different finite coefficient realization and universe. No declaration from either route is
removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or changed target was found. The original proof plan combines a
normalized scalar presentation, a derived common-quotient comparison, and invariant transport.
The existing declarations do not directly state the first two comparisons for exactly the
fixed-scalar small-site presentation. The new nodes isolate these gaps; the homology and Tor
transport part is implemented from existing declarations. In particular the native Tor
predicate allows unordered endpoints, whereas the coefficient-model predicate includes
`a ≤ b`; the proof explicitly widens the interval instead of assuming those definitions are
identical. Checks include empty schemes, zero modules/residues, disconnected sites and scalar
relabeling by a specified ring equivalence.

## New nodes

`lem-sfb-discrete-coefficient-model` records the normalized ordinary-module equivalence and
its preservation/reflection of finite constant models. Normalization fixes the coefficient
map on the sheafification unit, preventing an arbitrary coefficient automorphism. It is
independent of complexes, completion, reduction and Tor amplitude.

`lem-sfb-integral-residue-model-comparison` records the isomorphism of the two first derived
residues. It uses the existing lifted quotient equivalence and normalized common-quotient
comparison, and imposes no constructibility, Tor, completeness or Noetherian hypothesis on
the input complex. There are no change records because no existing definition or statement
changed.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
