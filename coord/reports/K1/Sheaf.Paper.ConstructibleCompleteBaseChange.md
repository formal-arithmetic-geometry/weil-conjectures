## What changed

Proved `AlgebraicGeometry.Scheme.constructibleComplete_properBaseChange` with its
original signature, definitions, public imports and declaration docstring. Its private
helpers prove that the coefficient prime divides the annihilator, exactness of
completed pullback, naturality of the specified ambient exchange, and its component
formula. The proof restricts that transformation through the full subcategories,
uses complete base change to make its components invertible, and transports the
source shift comparison through the resulting natural isomorphism. Mathlib supplies
exactness of the target functor with this transported comparison.

The independent object-preservation proposition from the source is recorded in
`Sheaf.Paper.CompletedConstructiblePreservation` for the original adic coefficient
datum. The existing specialized preservation wrapper uses a different universe and
lifted coefficient datum. The preservation module now proves intrinsic completeness for
each output using
completion units and unit-compatible comparisons. It also constructs compatible
etale origins by bounded-below full faithfulness, and assembles the uniform local
models using normalized local effectivity. Its only remaining input is the separate
finite-reduction control lemma in `CompletedConstructibleReductionControl`: common
cohomological bounds and constructibility. The item proves the
specified exchange, naturality, invertibility and triangulated-functor restriction.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.constructibleComplete_properBaseChange`
(node `cor-weil-pbc-constructible-complete`). No `sorry` remains in the item.

Also proved the new preservation assembly:
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.constructible_preservation`
(node `lem-weil-pbc-actual-coefficient-constructible-preservation`).

Added one hole:
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.constructible_reduction_control`
(node `lem-weil-pbc-completed-constructible-reduction-control`). No other declaration
in the three delivered modules contains `sorry`. This is a decomposition: one original
hole closed, one lower finite-reduction hole added, net zero. It does not remove
`sorry` from the complete targets' axiom closure. The remaining theorem excludes
completeness, all etale origins, uniform models and compatibility of origins; these are
proved in the preservation assembly.

Checked the new statement on zero objects, empty schemes, zero finite quotients,
identity pullbacks and zero fibre bound. Its conclusions are membership and support
containments; it asserts neither nonemptiness nor equality of cohomological supports.
Its global-vanishing argument retains etale origins and does not treat the strata as
a pro-etale covering.

Verification: all three delivered modules compile through `lcompile.py --all`.
The delivery tool additionally runs its declaration and axiom probes. Its final
result records the actual delivery commit.

## No longer needed

Removed the following direct proof imports from the item:

- `Sheaf.Paper.PreservationConstructible`
- `Sheaf.Paper.CompletedExchangeCoherence`
- `Sheaf.RingTheory.UniformPerfectQuotientBound`
- `Mathlib.Algebra.Category.ModuleCat.Projective`
- `Mathlib.CategoryTheory.Preadditive.Projective.Resolution`
- `Mathlib.RingTheory.Finiteness.Defs`
- `Mathlib.RingTheory.Ideal.Operations`
- `Mathlib.RingTheory.Ideal.Quotient.Operations`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `Sheaf.AlgebraicGeometry.ProEtaleStalkConservative`
- `Sheaf.Paper.BoundedConstructibleTower`
- `Sheaf.Paper.CompletedRlimFunctor`
- `Sheaf.Paper.PbcQbarCompletedPullback`
- `Sheaf.Paper.PbcUniformCompleteTriangulated`

The explicit ambient transformation proves naturality without
`lemma-weil-pbc-completed-exchange-coherence` /
`Sheaf.Paper.CompletedExchangeCoherence`. Exactness of `towerModulePull` and the
published triangulated reduction-tower property avoid a new K-flat tower-resolution
argument in this corollary. Thus `lem-weil-pbc-diagram-kflat-replacements` and
`lem-pur-left-derived-from-kflat-class` are removed from this node's dependencies,
along with its obsolete tool approval for the latter.

`lem-cbc-proetale-stalk-conservative`, the quotient bound, constant-completion
comparison and bounded-tower theory remain inputs of the separate preservation
proposition. Their removal as direct inputs to the corollary does not remove them
from the global target closure. The older specialized preservation wrapper is not
used by this proof: it would need a coefficient-transport theorem. Public uniform
triangulation imports and the unit's realized statements and steps remain.

The preservation module no longer directly imports CompletedPullbackReduction,
CompletedDirectImageLimits, PerfectProjectionFormula, FiniteRingConstructibleDerivedOrigin,
ConstantCompletionEquivalence, UniformPerfectQuotientBound or ProEtaleStalkConservative.
The remaining finite-reduction lemma records the relevant geometric inputs separately;
they remain in the closure. The finite-ring derived-origin module is also no longer a
direct dependency of the new finite-reduction lemma; normalized local effectivity
already supplies the levelwise origins used in the assembly. CompletedDirectImageLimits is replaced in the preservation
assembly by the unit-compatible intrinsic completion interface.

The new node additionally uses the existing exact comparison, canonical reduction
adic tower, actual completed pullback and strict-presentation transport. These prove
the normalization and completeness steps without new holes.

## Where the brief, the DAG or earlier work was wrong

The existing `WeilConjectures.pbc_preservation_constructible` takes `E : Type u`,
a ULift valuation ring, canonical geometric-residue-field fibres and a supplied
common reduction interval. The assigned corollary takes `E : Type (u + 1)`, the
unlifted valuation ring, arbitrary algebraically closed geometric fibres and obtains
the interval from membership. Direct application therefore fails at the coefficient
categories. The new source proposition preserves the original datum rather than
identifying different module categories definitionally. The old wrapper is unchanged.

The source reconstruction wrapper also requires finite type over a field, absent
from this item. No such hypothesis was added. The new proposition's proof in words
uses finite reductions, intrinsic completeness, finite amplification, normalized
origins and local effectivity.

The node's shift-coherence argument can be shortened because the conclusion asks
existentially for shift comparisons. Transport the source comparison through the
constructed natural isomorphism; no compatibility with an independently chosen target
comparison is required. Naturality follows from the ambient construction on all maps.
No target or existing intermediate signature is changed.

After the provider interruptions, all retained operations were checked before retry.
No earlier successful push or pending tool was found. Earlier compile-service requests
had timed out without Lean diagnostics; the service now responds. The resumed
reduction-control experiment was extended into the delivered proof: completeness,
normalization lifting and uniform local-model assembly now compile. The resumed proof
also derives levelwise etale origins from local effectivity, exact
realization and its canonical scalar-restriction comparison, removing that requirement
from the remaining lemma. The finite-level
geometric control is the sole named remaining hole. Earlier exploratory versions are
retained under `scratchpad/`. The dry run's reset reference clock was not edited or
bypassed. The reference clock changed from start 1792426893.0519233 to 1792436119.2122777
while the session continued; dry runs reported 36 minutes and later 5 minutes.
Preflight detected and corrected the two new nodes' creator-role/item fields and
their missing LeanSearch entries. Both searches ran through the required launcher and
found no matching theorem. These provider-resume attempts retain the same group/item sandbox. The reset is
reported here for the launcher owner; no metadata was modified by this worker.

## New nodes

`lem-weil-pbc-actual-coefficient-constructible-preservation` records the source's
preservation proposition for the original adic datum. It is strictly the geometric
object-preservation part of this corollary. The item itself proves the exchange
construction, invertibility, naturality and exact restriction. The blueprint search
found the specialized preservation proposition and records it in `blueprint.same_as`;
its existing Lean wrapper does not fit the assigned coefficient categories. This
new preservation theorem is now proved from the finite-reduction lemma and existing
completion, comparison and local-effectivity interfaces.

`lem-weil-pbc-completed-constructible-reduction-control` is the finite-level portion
of the source preservation proof (steps 1 and 3--5): common bounds and constructible
cohomology. It asserts no completeness, etale origins, uniform output models
or origin compatibility. Its proof docstring explains the uniform perfect-quotient
bound, finite amplification and canonical quotient-linear reduction comparisons. Searches are recorded in
the nodes and `searches.jsonl`.

Change record: `coord/changes/K1-original-datum-constructible-preservation.md`.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
