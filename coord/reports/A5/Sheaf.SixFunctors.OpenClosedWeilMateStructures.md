## What changed

Proved the original theorem from four separate coefficient-stage lemmas and a complete
generic calculation of its two final rational/common-stage mate assertions. The latter
uses the published invertibility of the specified Frobenius exchange maps, expands their
mate formulas, cancels inverse isomorphisms in the mate unit/counit identities and uses
naturality to prove both outer Weil squares.

Extracted the nineteen existing data declarations verbatim to OpenClosedWeilMateData,
publicly reexported by the original module. This permits acyclic imports of four genuine
parts of the proof. Every original public signature and definition body is preserved.
The change record is coord/changes/open-closed-weil-mate-data.md. No source-library file changed.

Validation: all nineteen relocated definition signatures and bodies were compared
against the original module and are unchanged. The finite and original theorem proofs
compiled in the full delivered import order. The ordinary integral argument previously
compiled separately; the final packet is checked again by the delivery tool.


## Proved and sorry left

Closed the original hole in WeilConjectures.sf_openClosed_weil_mate_structures. This is a
decomposition, not a net proof: three named results remain, each in its own module.

- WeilConjectures.sf_openClosed_weil_completion_stage:
  lem-sf-open-closed-weil-mate-completion-stage.
- WeilConjectures.sf_openClosed_weil_coefficient_stage:
  lem-sf-open-closed-weil-mate-coefficient-stage.
- WeilConjectures.sf_openClosed_weil_descent_stage:
  lem-sf-open-closed-weil-mate-descent-stage.

Original item: one hole. Item after change: zero holes. Added: three holes. Net: minus two.
The ordinary integral predicate is proved privately from
IntegralSupportNormalization.integralSupportFunctorNormalization: identify the actual
completed direct image with the completed coefficient presentation by its coefficient
map, use uniqueness of adjoints for the closed pullback, and transport constructibility
along the specified normalization isomorphisms. Frobenius equivalences and mate identities
supply the integral exchanges. The public integral stage combines this complete argument
with the separate strict completion normalization theorem.

WeilConjectures.sf_openClosed_weil_finite_stage is also proved, with no added hole:
finite immersion constructibility and open extension provide the four preservation
clauses; pullback along the Frobenius automorphism is an equivalence; mate invertibility,
unit/counit identities and naturality give the intrinsic assertion. A proved generic
conjugation lemma and mate-pasting cubes give the normalized ringed-site assertion.
The generic two-mate proof and the combination of all stage conclusions contain no holes.
All retained holes are named public theorems with separate nodes and proof descriptions.

## No longer needed

The item no longer directly imports MateIsoAlongEquivalences, InverseMateEquivalence,
SfImmersionCompletedPullbackComparison, OpenRoosUnitAdjunction,
IntegralOpenReductionComparison, CompletedDirectImageLimits,
BasicOperationsCoefficientReduction, PbcRationalTransport or StageSystem.Functor.
The two generic mate invertibility imports are retained in the proved finite-stage module.
The first two invertibility calculations for the final actual functors were already
proved in FieldWeilShriekShiftData and CommonStageWeilShriek. The other dependencies
remain assigned to the corresponding stage nodes. No existing mathematical module is
withdrawn; no module-level pruning is claimed. The original node's nine direct tool-use
entries are removed: lem-weil-mate-iso-along-equivalences,
lem-stage3-inverse-mate-equivalences, lem-sf-immersion-completed-pullback-comparison,
lem-sf-open-roos-unit-adjunction, lem-sf-integral-open-reduction-comparison,
prop-weil-pbc-direct-image-limits, lem-fix-operation-reduction,
prop-weil-pbc-rational-transport and prop-weil-pbc-descent-functors. These tools belong
to the separated stage nodes where needed; this does not claim they are globally unused.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged. The final two assertions have a shorter route
through existing, proved invertibility results for their exact specified maps. The
normalization obligations of the first eight clauses are separate substantial results,
recorded as four stage statements. The additional ordinary-integral proof reduces
the retained completion obligation.
The definition extraction is required to state these
without creating an import cycle, not to avoid a compile timeout.

## New nodes

- def-sf-open-closed-weil-mate-data owns the unchanged data declarations.
- lem-sf-open-closed-weil-mate-finite-stage isolates the intrinsic finite assertion and
  its normalized ringed presentation.
- lem-sf-open-closed-weil-mate-integral-stage combines the proved ordinary integral
  assertion with strict completion normalization.
- lem-sf-open-closed-weil-mate-completion-stage isolates only the strict-tower comparison
  pins and normalized transport; it is strictly smaller than the integral stage.
- lem-sf-open-closed-weil-mate-coefficient-stage isolates all three ordinary scalar passages.
- lem-sf-open-closed-weil-mate-descent-stage isolates rationalization, rational scalar
  extension and common-stage descent.

Each is strictly part of the original conjunction. The last two original conjuncts are
proved directly by real Lean calculations. The unit route and all parent uses remain.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
