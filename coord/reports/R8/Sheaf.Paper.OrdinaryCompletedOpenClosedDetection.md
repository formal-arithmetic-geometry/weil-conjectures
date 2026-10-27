## What changed

The item's original theorem statement, universes, binders and public imports are unchanged.
The proof compares the actual open ordinaryPull with restriction to the localized
site, using the ordinary coefficient isomorphism from qcqsOrdinaryRestrictionExact,
the map/pullback site adjunction, its module adjunction, a direct module transport
equivalence, and uniqueness of left adjoints. Both ring-adjunction unit equations
are retained explicitly. The transport routine records its actual pushforward
functor, so Mathlib's pushforward composition isomorphism gives the comparison
without unfolding a large equality of functors. It is the same generic equivalence
construction used by the private sliceModuleTransport helper, with a stronger
functor equation; importing all of the derived-operations module is unnecessary. Naturality then gives
a map of module short exact sequences; Mathlib's short five lemma proves that its middle component is invertible.

OrdinaryCompletedLocalizationSequence proves the independent-universe module
localization sequence. Its private, proved helpers adapt the existing ringed
localization proof to module universe max u (t+1): bounded affine refinements,
finite distinguished-open/closed-localization covers, the open counit comparison,
vanishing of extension sections on specialization neighbourhoods, and descent of
sectionwise exactness through sheaf separation and local kernel lifts. The local
closed-unit comparison is the sole new remaining obligation. This is a genuine
local step of Tag 09AH, identified separately by Tag 09AC; it does not repackage
joint detection or assume the localization sequence.

Only this item, its node, three new modules and their nodes are changed. No shared
definition, other existing module, target statement, or upstream declaration is
changed. The bounded-cover arguments stay in scheme universe t, while sheaves and
module sections take values in max u (t+1).

## Proved and sorry left

Closed the original hole:

- WeilConjectures.IntegralOnSlice.ordinaryCompletedOpenClosedDetection.

Proved the new intermediate theorems:

- WeilConjectures.IntegralOnSlice.ordinaryCompletedLocalizationSequence.
- AlgebraicGeometry.Scheme.proEtale_module_shortExact_of_local_sections_independent.

Added one named remaining hole:

- WeilConjectures.IntegralOnSlice.ordinaryCompletedSpecializationUnit.

There are zero holes in the item, the localization-sequence module and the
local-exactness criterion; there is one in the specialization-unit module. Thus
this delivery is a decomposition
(one old hole closed, one smaller hole added), not a net proof-hole reduction.
qcqsOrdinaryRestrictionExact is an existing stated dependency and is not changed
or counted as a new hole here.

The new specialization statement includes empty affine objects: the sheaf axiom
makes their section modules trivial. When i has empty source, the specialization
hypothesis forces V empty. When i is an identity, the unit is invertible. The
localization proof also permits an empty open or closed piece, and the short five
argument requires no nonempty-source assumption.

## No longer needed

No original public import was removed and no module is withdrawn. The temporary
proof import `import all Sheaf.Paper.IntegralDerivedOperationsOnSlices` was removed:
the direct equivalence construction and pushforward composition API avoid it.
Only the weakly-etale site-localization module is imported for that site geometry.

The item's former planned direct dependencies
lem-fix-qcqs-ordinary-restriction-models (Sheaf.Paper.QcqsOrdinaryRestrictionModels)
and lem-tw-completed-coefficient-ringed-coherence
(Sheaf.Paper.CompletedCoefficientRingedCoherence) are not used by this proof.
The coefficient-isomorphism clause of qcqsOrdinaryRestrictionExact and the unit
of the actual ring adjunction give the needed open comparison directly.

lem-weil-pbc-proetale-ringed-open-closed
(Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed) is also not used: its fixed
coefficient universe does not fit the item's independent universes. Instead the
new module writes the local covering/exactness argument in the required universe.
The corresponding fixed-universe module-specialization theorem is not imported
as a purported proof of its independent-universe analogue.

These are pruning changes to this item's proof dependencies, not claims that
those declarations are globally unused. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The DAG's suggested ringed open-closed theorem fixes the coefficient/module
universe to the scheme universe plus one. It cannot directly instantiate the
item's independent coefficient-field universe. The localization and section
arguments are instead supplied in max u (t+1), leaving precisely the local
closed-unit comparison at that universe.

The latest blueprint unit sk-rem-sf-pf-done has no realized statement/proof-step
nodes to bypass. Its remark and the ancestor's projection-formula route are
preserved. The new local lemmas serve the ancestor's ordinary open-closed
comparison clause recorded on the item.

The generic localized module adjunction is used as a tool from the smooth-purity
unit, and the bounded ring refinements and specialization geometry as tools from
the proper-base-change unit. They supply site/module constructions, not a route
replacing a unit's statement. The node records name their actual dependencies.

## New nodes

- lem-fix-proetale-module-local-exact-independent:
  Sheaf.AlgebraicGeometry.ProEtaleModuleLocalExactIndependent, the proved local
  section criterion used for descent of exactness. The proof treats kernel
  inclusions and lifts abstractly; its separate module avoids re-elaborating the
  criterion together with the geometric covering construction.
- lem-fix-ordinary-completed-localization-sequence:
  Sheaf.Paper.OrdinaryCompletedLocalizationSequence, proved from the local
  specialization-unit statement and the written covering and descent arguments.
- lem-fix-ordinary-completed-specialization-unit:
  Sheaf.Paper.OrdinaryCompletedSpecializationUnit, the actual closed-unit
  bijectivity on affine weakly contractible specialization neighbourhoods,
  with source, proof in words and independent universes.

Searches for the completed module detection/localization statement used LeanSearch,
LeanFinder, Loogle and Mathlib grep, recorded by msearch.py in searches.jsonl.
They found generic adjunction uniqueness, module pushforward adjunction and short
five APIs, but no statement for the required completed pro-etale coefficients.
The imported blueprint was searched for specialization-unit and localization
sequence duplicates; none states either new independent-universe local lemma.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
