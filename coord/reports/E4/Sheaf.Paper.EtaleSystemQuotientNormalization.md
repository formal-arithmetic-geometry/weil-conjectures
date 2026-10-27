## What changed

Proved the bodies of both original theorems in
`Sheaf.Paper.EtaleSystemQuotientNormalization`, with all original public statements,
definitions and imports preserved. The restriction isomorphism is constructed by
conjugating composite adjunctions; its Hom-chain and counit equations are proved.
The coefficient mate is identified with the constant-tensor counit transpose by
`restricted_mate_tensor`, and its invertibility follows from the existing constant
tensor theorem and conservative scalar restriction. Normalization of strict systems
uses the actual Brown quotient mates and the evaluation-bound transition equation.
The private Brown cube calculations are reused verbatim from the already-proved
helpers in `EtaleCoefficientSystemAdjoint`; importing that parent would create a cycle.

Added `Sheaf.Paper.EtaleQuotientTensorProjection`, isolating the geometric equality
between the restricted compact-support scalar map and the specified constant-tensor
projection. This is step 2 of the original argument, a separate map-coherence result;
it has no exceptional right adjoints, no isomorphism conclusion for exceptional
mates, and no normalized systems. Updated the parent proof route and added its node.
There are no definition or statement repairs and no forced consumer adaptations.

## Proved and sorry left

Closed both original holes:
- `AlgebraicGeometry.Etale.etaleCoefficientQuotientNormalization`.
- `AlgebraicGeometry.etaleSystemQuotientNormalization`.

Added one hole:
- `AlgebraicGeometry.Etale.etaleQuotientTensorProjection`
  (`lem-pur-etale-quotient-tensor-projection`).

The original module has zero holes; the delivery has one hole. This is a reduction
from two original holes to one geometric coherence lemma, not a claim that the
whole dependency closure is sorry-free. The proper component is already proved by
`scalar_projection_ambient`; the remaining formal work is the open projection mate
and the canonical constant-sheaf/pullback composition comparisons. A generic inverse
mate calculation was proved and compiled in the scratchpad while investigating
that open comparison, but is not added as an unused library declaration.

Both original theorems compile. The new theorem's type also compiles. Edge cases
checked mathematically: identity coefficient map, nonflat Z/ell² to Z/ell, zero
coefficient ring, empty source, identity compactification and equal system indices.
The map identity uses unit/counit naturality and never assumes coefficient flatness.

## No longer needed

No original public import is removed, and no existing module is withdrawn. The
proof uses the single-ring theorem `etaleSingleCoefficientProjection` directly,
instead of constructing the full system projection theory solely to extract its
single-ring clause. Thus `lem-pur-etale-system-coefficient-projection` is no longer
a proof dependency of this node; it remains a statement dependency and its public
import is retained. The original change-of-rings/tensor comparison step is retained
through the new geometric lemma rather than repeated in the parent. No other
original dependency is claimed globally pruned. Unneeded imports from the initial
new-module draft were removed; only constant-tensor definitions, projection data
and the sheaf change-of-rings instances remain there.

## Where the brief, the DAG or earlier work was wrong

Step 2 says the single-ring coefficient-projection clause identifies the specified
map with the constant-tensor projection, but its Lean declaration records only the
scalar-unit transpose. It does not record that tensor-map identity. The new lemma
states precisely this missing geometric step; it does not repackage either original
normalization theorem. The other steps follow the planned route. The unit's route
is unchanged. The original definitions and theorem signatures remain verbatim.

## New nodes

`lem-pur-etale-quotient-tensor-projection` is the sourced proper/open tensor-map
identity used in step 2. It is strictly below the exceptional adjunction argument
and uses the already fixed scalar/tensor and projection constructions. Its module
contains one public theorem, exactly `:= by sorry`, with a complete proof in words.
Three kinds of Mathlib searches and a blueprint duplicate search were performed.
There is no change record because no existing definition or statement changed.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
