## What changed

Reduced ordinaryTripleProductTranspose to three strictly smaller assertions: a binary
ordinary-product transpose, and left/right equations involving only pullback/tensor
comparisons and arbitrary maps. The item itself contains a complete assembly proof:
it transposes the outer and inner products, uses the two comparison equations on the
actual counits, and deduces equality by injectivity of the adjunction Hom equivalence.
Private, fully proved helpers establish equality-transport compatibility and naturality
of the tensor and binary evaluation composites. Tensor naturality is first proved
with an abstract coefficient category and then specialized, avoiding costly unfolding
of the concrete flat-resolution instances during kernel checking.

Moved the existing ordinary data to OrdinaryProductTransposeData, publicly reexported
by the item, retaining their signatures and concrete bodies. Added two explicit composites
ordinaryBinaryEvaluation and ordinaryTripleEvaluation for arbitrary maps, marked irreducible
to prevent rewriting from unfolding the underlying derived constructions. This avoids an
import cycle between the item and its smaller lemmas. Change record:
coord/changes/H3-ordinary-product-transpose-data.md. There are no existing importers of the
item; downstream.py and textual consumer checks found no forced adaptations.

Validation: all five modules compiled through the delivery checks without warnings.
The original theorem signature is byte-for-byte unchanged.

## Proved and sorry left

Original holes: 1. Closed upper hole:
WeilConjectures.PurityFiniteSetting.ordinaryTripleProductTranspose
(lem-pur-ordinary-triple-product-transpose), proved from the three statements below.

Added holes: 3, each the entire proof of a named public theorem in its own module:

- WeilConjectures.PurityFiniteSetting.ordinaryBinaryProductTranspose
  (lem-pur-ordinary-binary-product-transpose).
- WeilConjectures.PurityFiniteSetting.ordinaryTripleLeftComparison
  (lem-pur-ordinary-triple-left-comparison).
- WeilConjectures.PurityFiniteSetting.ordinaryTripleRightComparison
  (lem-pur-ordinary-triple-right-comparison).

This is a decomposition, not a net decrease in holes: one upper hole closed, three
strictly smaller holes added. The item has zero remaining holes, the new data has zero,
and the delivery has three. The binary lemma has only two factors. The comparison
lemmas have arbitrary independent maps and use no direct-image product, exchange,
projection or adjunction in their statements; they isolate just the coherence calculation.

## No longer needed

The item's former private imports are removed:
Sheaf.Paper.FiniteSystemPullbackCoherence,
Sheaf.Paper.DerivedPullbackTensorIso,
Sheaf.SmoothPurity.OrdinaryDerivedCompositeTranspose,
Sheaf.Paper.IntegralFinitePullbackComposition,
WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution,
Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
and Mathlib.AlgebraicGeometry.Morphisms.Separated.
Existing public prerequisites are retained through the extracted data module; no
adopted source declaration or public import is removed.

The three geometric permanence nodes lem-pod-separated-finite-type-base-change,
lem-sfb-finite-type-composition-base-change, and lem-weil-pbc-proper-fp-permanence
are not needed by this argument: all ordinary operations and smaller calculations
are defined for arbitrary scheme maps, so the theorem's original geometric assumptions
need no intermediate propagation. No module is withdrawn.

The original proof dependency and tool-use lists are replaced by those actually used
in the assembly. The new binary obligation retains the genuine successive-transpose
calculation of ordinaryDerivedCompositeTranspose in its plan. The intrinsic
DerivedPullbackTensorIso and FiniteSystemPullbackCoherence theorems are not applied
as if they were equations for the distinct fixed-scalar implementation; the new
comparison obligations isolate exactly that fixed-scalar calculation. No assertion
is made that any of these shared modules is globally unused.

## Where the brief, the DAG or earlier work was wrong

The cited DerivedPullbackTensorIso theorem states coherence for intrinsic ring-sheaf
operations, while the item uses the published fixed-scalar derived operations. Its
finite clause cannot be applied to these maps without a comparison argument.
FiniteSystemPullbackCoherence likewise concerns the intrinsic derived-system model.
The fixed-scalar source library already provides leftDerivedUpperStarComp_assoc_app;
the outstanding tensor/composition compatibility is isolated explicitly, rather than
silently treating the two implementations as definitionally equal.

Checked the existing binaryCounitTranspose node and generic projection/cup-product
lemmas: they do not identify the actual geometric symmetry/projection/exchange word
with this binary transpose, nor do they identify the specified triple pullback
comparisons. Searches of the current blueprint, DAG and Mathlib did not find an exact
replacement. The unit route is unchanged: ordinary transpose, ordered triple counits,
and injectivity of the Hom equivalence.

Small-case checks of the new statements: identities and equal objects give the usual
monoidal-adjunction equations; zero input maps make both comparison words zero by
additivity; the right source associator is retained and cancels only the specified
inverse target associator; arbitrary square equality proofs are harmless by proof
irrelevance. No boundedness, constructibility, properness, exchange invertibility or
projection invertibility was introduced. The binary lemma holds for all schemes and
maps; the finite coefficient setting is the same as the original item.

## New nodes

- def-pur-ordinary-product-transpose-data: extracts the existing concrete ordinary
  operations and product diagram, with binary/triple evaluation composites; no holes.
- lem-pur-ordinary-binary-product-transpose: steps 2--5 of the old proof, strictly binary.
- lem-pur-ordinary-triple-left-comparison: step 6's pullback/tensor calculation for
  arbitrary maps, independently of products and adjunctions.
- lem-pur-ordinary-triple-right-comparison: step 7's pullback/tensor calculation,
  retaining all associators and projection transports.

Each new statement carries the blueprint source and its complete proof in words.
The data extraction is recorded in coord/changes/H3-ordinary-product-transpose-data.md.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
