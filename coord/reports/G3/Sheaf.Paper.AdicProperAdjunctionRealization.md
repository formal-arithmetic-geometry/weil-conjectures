## What changed

Reduced `WeilConjectures.AdicQbarRealization.Proper.adic_proper_adjunction_realization`
to two genuine geometric steps, in new modules `Sheaf.Paper.AdicNormalizedPullbackRealization`
and `Sheaf.Paper.AdicProperOrdinaryPushPreservation`. The first retains only Steps 1--4
of the original plan: normalized coefficient operations, integral comparisons and the
common-stage tensor/unit-compatible inverse-image comparison. It makes no direct-image
assertion. The second retains Step 5 only: constructibility of the actual ordinary
proper direct image, independently of any chosen inverse-image comparison.

The item constructs the original Comparison without changing any existing declaration
signature, definition or public import. It derives pullback preservation from the
Family image clauses and the inverse-image isomorphism. A proved private categorical
helper shows a mate component is invertible when its target belongs to the fully
faithful source image: the two adjunctions and the inverse-image isomorphism give the
Hom bijections; surjectivity produces an inverse and injectivity proves the other
inverse equation. Proper push preservation supplies exactly that image membership.
The actual mate formula and both unit/counit identities are then proved in the ordinary
ambient derived categories, using Mathlib mate identities and cancellation.

All work is confined to the sandbox. The existing item is preserved despite its
historical quarantine row; there is no withdrawal or replacement by an empty module.
The source-library boundary is untouched. No shared definition/interface repair or
consumer adaptation is needed. Existing transparency-disabling options were removed
from the item and are not introduced in the new modules.

## Proved and sorry left

Original hole eliminated: `WeilConjectures.AdicQbarRealization.Proper.adic_proper_adjunction_realization`.
This is a decomposition, not a completed geometric proof: one upper hole is closed
and two strictly smaller geometric holes are added (net holes closed minus added: -1).
The item itself has zero textual holes. Its private mate helper is fully proved.

Every remaining hole added by this delivery is the complete body of a named public theorem:

- `WeilConjectures.AdicQbarRealization.Proper.adic_normalized_pullback_realization`
  (`lem-sf-adic-normalized-pullback-realization`), in
  `Sheaf.Paper.AdicNormalizedPullbackRealization`.
- `WeilConjectures.AdicQbarRealization.Proper.adic_proper_ordinary_push_preservation`
  (`lem-sf-adic-proper-ordinary-push-preservation`), in
  `Sheaf.Paper.AdicProperOrdinaryPushPreservation`.

No definition or private declaration contains sorry. No axiom is introduced. The new
statements retain the finite-field, geometric and residue-unit assumptions and cover
empty schemes, zero complexes and identity coefficient extensions. Properness is used
only for the direct-image step. No arbitrary witness is chosen to define a new object:
the new data structure consists of the prescribed normalized comparison maps, and all
choices in the assembly occur within the theorem proving Nonempty Comparison.

Validation: all three modules passed remote single-file compilation through lcompile.py.
The corrected upper module compiled in 20.7 seconds using the two compiled sandbox
dependencies. The overlay DAG audit found no dependency cycle through any of the
three delivered nodes. Delivery preflight is run by deliver3.py.

## No longer needed

The following proof-only imports are removed from the item:

- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Sheaf.Paper.LocallyFiniteCoefficientRingRealization`.
- `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization`.
- `Sheaf.Paper.RationalRealizationPullbackComparison`.
- `Sheaf.Paper.RationalRealizationScalarCoherence`.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
- `Sheaf.SixFunctors.ConstructibleTensorCompletion`.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`.
- `Sheaf.Paper.CompletedPrimitiveCounitComparison`.
- `Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`.
- `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`.
- `Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility`.
- `Sheaf.Paper.PbcScalarExtension`.
- `Sheaf.CategoryTheory.MateIsoAlongEquivalences`.

The geometric lemmas for Steps 1--4 remain mathematical dependencies of the new
inverse-image node; the compact-support and finite-Tor lemmas remain dependencies of
the new preservation node. They are not claimed pruned from the target closure merely
because their direct imports were removed here. Existing public imports are preserved.
No existing node or module is withdrawn.

The upper proof no longer needs `fix-prop-adjunctions`,
`lem-pur-ordinary-adjunction-scalar-compatibility` or `prop-weil-pbc-scalar-extension`
as separate proof steps: `geometricCommonStageAdjunction` already supplies precisely
the published common-stage adjunction. It no longer needs the separate
`lem-weil-mate-iso-along-equivalences` theorem: the proved private Hom-bijection
argument works directly on the essential images and produces the ambient mate
isomorphism. Its argument follows the same categorical method.

Obsolete direct tool-use approvals were removed from the parent node (all entries
except `lem-amb-mate-unit-counit` and `lem-pur-mate-unit-compatibility`). This removes
no independent mathematical statement; the geometric tool dependencies are retained
on their corresponding new subargument nodes.

## Where the brief, the DAG or earlier work was wrong

The old DAG plan is mathematically retained, but its Steps 1--4 do not arrive as one
Lean theorem with the required Operations/IntegralAgreement/Family tensor interfaces;
those normalizations still require a bridge across the existing presentations. The
new inverse-image statement isolates that missing construction without asserting any
of the right-adjoint conclusions.

The compact-support theorem chooses its own native presentation. Applying it to
(id,p) alone does not immediately give preservation for the arbitrary fixed Family
and Operations in this item. The new preservation node explicitly requires the
section-module equivalence, normalized coefficient map and uniqueness-of-right-adjoint
transport to the actual ordinary module direct image.

The ordinary realization is an equivalence with its full bounded constructible image,
not with the entire ambient unbounded derived category. The private mate argument
therefore uses proper pushforward preservation to place the mate target in that image;
it never asserts essential surjectivity onto the whole ambient category.

No target, unit statement or unit route changes. The unit record has no realized
steps to bypass. There is no mathematical dispute or upstream declaration change.

## New nodes

`lem-sf-adic-normalized-pullback-realization` states only the balanced normalized
inverse-image construction (old proof Steps 1--4), using the fixed Family and its
finite tensor normalizations. Its own module includes the concrete PullbackComparison
record, with no direct-image or adjunction-identification fields. Mathlib searches
found only generic underived scalar/pullback and tensor statements.

`lem-sf-adic-proper-ordinary-push-preservation` states only the proper preservation
step (old proof Step 5), for any Operations with the required precomposition map.
It does not include a comparison a, a mate b, or any equation of adjunctions. The
source is BS 6.7.2 and 6.8.14--6.8.15 through the existing compact-support realization.
Mathlib searches found properness instances and underived sheaf adjunctions, not this
native bounded constructible preservation result. No change record is necessary
because no existing definition or statement changes.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
